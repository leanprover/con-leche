import Setlec.Kernel.Core
import Std.Data.HashMap

/-!
# The memoized knot

The same core bodies (`Setlec.Kernel.Core`) tied together at a state
monad carrying memoization caches.  Memo keys are **depth-free** (the
expression alone, the pair for `defeq`): the same subterm reached under
different binder contexts reuses one entry.  This is justified by the
depth invariance theorems (`Setlec/Verify/Deep.lean`): every entry
point returns the same result at any depth at which its input is
well-scoped, so an entry backed at *some* well-scoped depth is valid at
every other one.  Every cache operation is guarded on `wscopedB` — an
ill-scoped argument (impossible in disciplined runs, but the bridge
must not assume the discipline) bypasses the cache.

Depth invariance additionally requires a well-formed environment
(`EnvWF`).  There is **no runtime check** for it: the checker only ever
calls the core on environments it built itself, and the consistency
proof carries `EnvWF` as part of the environment model invariant
(`EnvModel.wf`), threading it into the refinement bridge
(`Setlec/Verify/Bridge.lean`, `Setlec/Model/BridgeWF.lean`) — never
add boolean checks for what is proven to hold.

This instance is what the checker executes; the pure knot
(`Setlec.Kernel.TypeChecker`) is the verified specification and the
refinement bridge relates the two (see DESIGN.md).
-/

namespace Setlec

/-- Memoization state for the five core entry points, keyed by the
expression alone (results are depth-invariant for well-scoped inputs;
the environment is fixed for the lifetime of a cache — each top-level
call starts fresh). -/
structure KCache where
  whnfCore : Std.HashMap Expr Expr := {}
  whnf : Std.HashMap Expr Expr := {}
  infer : Std.HashMap Expr Expr := {}
  defeq : Std.HashMap (Expr × Expr) Bool := {}
  annot : Std.HashMap Expr Expr := {}

instance : Inhabited KCache := ⟨{}⟩

/-- The cached checker monad. -/
abbrev CheckSM := StateT KCache CheckM

/-- Memoize a unary entry point under the expression alone; the cache
is consulted only when the key is well-scoped at the ambient depth
(the precondition of the depth-invariance transport). -/
def memoE (get' : KCache → Std.HashMap Expr Expr)
    (set' : KCache → Std.HashMap Expr Expr → KCache)
    (f : Nat → Expr → CheckSM Expr) : Nat → Expr → CheckSM Expr :=
  fun d e => do
    if e.wscopedB d then
      match (get' (← get))[e]? with
      | some r => pure r
      | none =>
        let r ← f d e
        -- Detach the map from the state before inserting: `insert` on a
        -- map still referenced from `st`'s field would copy the whole
        -- backing array on every miss.
        modify fun st =>
          let mp := get' st
          let st := set' st ∅
          set' st (mp.insert e r)
        pure r
    else f d e

/-- Memoize the binary definitional-equality entry point. -/
def memoB (f : Nat → Expr → Expr → CheckSM Bool) :
    Nat → Expr → Expr → CheckSM Bool :=
  fun d a b => do
    if a.wscopedB d && b.wscopedB d then
      match (← get).defeq[(a, b)]? with
      | some r => pure r
      | none =>
        let r ← f d a b
        modify fun st =>
          let mp := st.defeq
          let st := { st with defeq := ∅ }
          { st with defeq := mp.insert (a, b) r }
        pure r
    else f d a b

/-- The executable core: the bodies tied at `CheckSM`, every level's
entry points wrapped with the guarded cache. -/
def cachedFns (env : Env) : Nat → CoreFns CheckSM :=
  coreKnot env fun r =>
    { whnfCore := memoE (·.whnfCore)
        (fun st mp => { st with whnfCore := mp }) r.whnfCore
      whnf := memoE (·.whnf) (fun st mp => { st with whnf := mp }) r.whnf
      infer := memoE (·.infer) (fun st mp => { st with infer := mp }) r.infer
      defeq := memoB r.defeq
      annotate := memoE (·.annot)
        (fun st mp => { st with annot := mp }) r.annotate }

end Setlec
