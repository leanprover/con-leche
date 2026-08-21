import Setlec.Kernel.Core
import Std.Data.HashMap

/-!
# The memoized knot

The same core bodies (`Setlec.Kernel.Core`) tied together at a state
monad carrying memoization caches: every entry point is wrapped with a
cache lookup keyed by binder depth and expression (the environment is
fixed for the lifetime of a cache — each top-level call starts fresh).
This instance is what the checker executes; the pure knot
(`Setlec.Kernel.TypeChecker`) is the verified specification and the
refinement bridge relates the two (see DESIGN.md).
-/

namespace Setlec

/-- Memoization state for the five core entry points. -/
structure KCache where
  whnfCore : Std.HashMap (Nat × Expr) Expr := {}
  whnf : Std.HashMap (Nat × Expr) Expr := {}
  infer : Std.HashMap (Nat × Expr) Expr := {}
  defeq : Std.HashMap (Nat × Expr × Expr) Bool := {}
  annot : Std.HashMap (Nat × Expr) Expr := {}

instance : Inhabited KCache := ⟨{}⟩

/-- The cached checker monad. -/
abbrev CheckSM := StateT KCache CheckM

/-- Memoize a unary (depth, expression) entry point. -/
def memoE (get' : KCache → Std.HashMap (Nat × Expr) Expr)
    (set' : KCache → Std.HashMap (Nat × Expr) Expr → KCache)
    (f : Nat → Expr → CheckSM Expr) : Nat → Expr → CheckSM Expr :=
  fun d e => do
    match (get' (← get))[(d, e)]? with
    | some r => pure r
    | none =>
      let r ← f d e
      -- Detach the map from the state before inserting: `insert` on a
      -- map still referenced from `st`'s field would copy the whole
      -- backing array on every miss.
      modify fun st =>
        let mp := get' st
        let st := set' st ∅
        set' st (mp.insert (d, e) r)
      pure r

/-- Memoize the binary definitional-equality entry point. -/
def memoB (f : Nat → Expr → Expr → CheckSM Bool) :
    Nat → Expr → Expr → CheckSM Bool :=
  fun d a b => do
    match (← get).defeq[(d, a, b)]? with
    | some r => pure r
    | none =>
      let r ← f d a b
      modify fun st =>
        let mp := st.defeq
        let st := { st with defeq := ∅ }
        { st with defeq := mp.insert (d, a, b) r }
      pure r

/-- The memoized core: the bodies tied at `CheckSM`, every level's
entry points wrapped with the cache. -/
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
