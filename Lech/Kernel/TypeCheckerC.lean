import Lech.Kernel.Core
import Std.Data.HashMap

/-!
# The memoized knot

The same core bodies (`Lech.Kernel.Core`) tied together at a state
monad carrying memoization caches.  Memo keys are **depth-free** (the
expression alone, the pair for `defeq`): the same subterm reached under
different binder contexts reuses one entry.  This is justified by the
depth invariance theorems (`Lech/Verify/Deep.lean`): every entry
point returns the same result at any depth at which its input is
well-scoped, so an entry backed at *some* well-scoped depth is valid at
every other one.

There is **no runtime check** on the memo operations (never add
boolean checks for what is proven to hold):

* The scoping half of depth invariance — every key consulted or
  inserted is well-scoped at the ambient depth — is the *call
  discipline*, proven for every core body over the cached knot
  (`Lech/Verify/Disc.lean`): the checker's entry points are only
  ever invoked on well-scoped arguments (raw input is closed, checked
  once per declaration; the `fvar` leaf checks in
  `inferBody`/`annotateBody` enforce scoping inside traversals that
  happen anyway), and each body passes only well-scoped arguments to
  its recursive calls.
* The environment half (`EnvWF`) is a hypothesis of the bridge,
  threaded from the environment invariant (`EnvS.wf`) through
  `Lech/Verify/Bridge.lean` / `Lech/Verify/BridgeWFDecl.lean` —
  the checker only ever calls the core on environments it built
  itself.

This instance is what the checker executes; the pure knot
(`Lech.Kernel.TypeChecker`) is the verified specification and the
refinement bridge relates the two (see DESIGN.md).
-/

namespace Lech

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
  /-- The io-grade inference memo (task #170 / #172 B4): the `inferIO`
  slot's results at the gated mode, split from `infer` per the
  task-#170 memo ruling (a hit here never serves a full-infer query).
  At gate-off modes the io slot shares the `infer` memo and this map
  stays empty. -/
  inferIO : Std.HashMap Expr Expr := {}

instance : Inhabited KCache := ⟨{}⟩

/-- The cached checker monad. -/
abbrev CheckSM := StateT KCache CheckM

/-- Memoize a unary entry point under the expression alone.  No scope
check: the call discipline (`Lech/Verify/Disc.lean`) proves every
key arrives well-scoped at the ambient depth, which is what the
depth-invariance transport of the cache bridge needs. -/
def memoE (get' : KCache → Std.HashMap Expr Expr)
    (set' : KCache → Std.HashMap Expr Expr → KCache)
    (f : Nat → Expr → CheckSM Expr) : Nat → Expr → CheckSM Expr :=
  fun d e => do
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

/-- Memoize the binary definitional-equality entry point (no scope
check, as in `memoE`). -/
def memoB (f : Nat → Expr → Expr → CheckSM Bool) :
    Nat → Expr → Expr → CheckSM Bool :=
  fun d a b => do
    match (← get).defeq[(a, b)]? with
    | some r => pure r
    | none =>
      let r ← f d a b
      modify fun st =>
        let mp := st.defeq
        let st := { st with defeq := ∅ }
        { st with defeq := mp.insert (a, b) r }
      pure r

/-- The executable core: the bodies tied at `CheckSM`, every level's
entry points wrapped with the guarded cache. -/
def cachedFns (mode : CheckMode) (env : Env) : Nat → CoreFns CheckSM :=
  coreKnot mode env fun r =>
    { whnfCore := memoE (·.whnfCore)
        (fun st mp => { st with whnfCore := mp }) r.whnfCore
      whnf := memoE (·.whnf) (fun st mp => { st with whnf := mp }) r.whnf
      infer := memoE (·.infer) (fun st mp => { st with infer := mp }) r.infer
      defeq := memoB r.defeq
      annotate := memoE (·.annot)
        (fun st mp => { st with annot := mp }) r.annotate
      -- the io slot (task #170 / #172 B4): its own memo at the gated
      -- mode (the two-memo ruling); the full memo's wrapper — the same
      -- closure the `infer` field carries — everywhere else, because
      -- the two grades are one function there
      inferIO := if mode.betaGate then
          memoE (·.inferIO)
            (fun st mp => { st with inferIO := mp }) r.inferIO
        else
          memoE (·.infer)
            (fun st mp => { st with infer := mp }) r.infer }

end Lech
