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
every other one.  Two guards keep that justification airtight:

* every cache operation is guarded on `wscopedB` — an ill-scoped
  argument (impossible in disciplined runs, but the bridge must not
  assume the discipline) bypasses the cache;
* memoization is enabled only for syntactically well-formed
  environments (`Env.wfB`, the `Bool` mirror of `Verify`'s `EnvWF`,
  which the invariance theorems require) — an ill-formed environment
  (never produced by the checker) runs the plain knot.

This instance is what the checker executes; the pure knot
(`Setlec.Kernel.TypeChecker`) is the verified specification and the
refinement bridge relates the two (see DESIGN.md and
`Setlec/Verify/Bridge.lean`).
-/

namespace Setlec

/-- The stored names as a hash set — the gate's resolution oracle
(`Env.find?` is list-linear; the gate must stay linear in the
environment's total size). -/
def Env.nameSet (env : Env) : Std.HashSet Name :=
  env.consts.foldl (fun s c => s.insert c.name) {}

/-- `Expr.constsResolve`, resolved against a name set. -/
def Expr.constsResolveS (s : Std.HashSet Name) : Expr → Bool
  | .bvar _ | .sort _ | .lit (.strVal _) => true
  | .lit (.natVal _) =>
    s.contains natName && s.contains natZeroName && s.contains natSuccName
  | .const n _ => s.contains n
  | .fvar _ _ ty => ty.constsResolveS s
  | .app f a => f.constsResolveS s && a.constsResolveS s
  | .lam _ ty body _ | .forallE _ ty body _ =>
    ty.constsResolveS s && body.constsResolveS s
  | .letE _ ty val body =>
    ty.constsResolveS s && val.constsResolveS s && body.constsResolveS s
  | .proj sn _ e => s.contains sn && e.constsResolveS s

/-- One-pass conjunction of the four per-expression facts the gate
needs: `fvar`-free, level parameters within `lps`, constants resolving
in the name set, bound variables below the cutoff. -/
def Expr.declWfB (s : Std.HashSet Name) (lps : List Name) :
    Nat → Expr → Bool
  | k, .bvar i => decide (i < k)
  | _, .fvar _ _ _ => false
  | _, .sort u => u.allParamsDefined lps
  | _, .const n us => s.contains n && us.all (Level.allParamsDefined lps)
  | k, .app f a => f.declWfB s lps k && a.declWfB s lps k
  | k, .lam _ t b m =>
    t.declWfB s lps k && b.declWfB s lps (k + 1) &&
      (match m.cod with
       | some v => v.allParamsDefined lps
       | none => true)
  | k, .forallE _ t b m =>
    t.declWfB s lps k && b.declWfB s lps (k + 1) &&
      (match m.cod with
       | some v => v.allParamsDefined lps
       | none => true)
  | k, .letE _ t v b =>
    t.declWfB s lps k && v.declWfB s lps k && b.declWfB s lps (k + 1)
  | _, .lit (.strVal _) => true
  | _, .lit (.natVal _) =>
    s.contains natName && s.contains natZeroName && s.contains natSuccName
  | k, .proj sn _ e => s.contains sn && e.declWfB s lps k

/-- The `Bool` mirror of `Verify`'s per-constant `ConstWF`, resolving
against the precomputed name set. -/
def ConstantInfo.wfB (s : Std.HashSet Name) (c : ConstantInfo) : Bool :=
  c.toConstantVal.type.declWfB s c.toConstantVal.levelParams 0 &&
  (match c with
   | .defnInfo cv value => value.declWfB s cv.levelParams 0
   | .recInfo cv _ _ _ _ rules =>
     rules.all fun r => r.rhs.declWfB s cv.levelParams 0
   | _ => true)

/-- The `Bool` mirror of `Verify`'s `EnvWF` (checked once per
top-level entry-point call; gates memoization). -/
def Env.wfB (env : Env) : Bool :=
  let s := env.nameSet
  env.consts.all (ConstantInfo.wfB s)

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

/-- The memoized core: the bodies tied at `CheckSM`, every level's
entry points wrapped with the guarded cache. -/
def cachedFnsM (env : Env) : Nat → CoreFns CheckSM :=
  coreKnot env fun r =>
    { whnfCore := memoE (·.whnfCore)
        (fun st mp => { st with whnfCore := mp }) r.whnfCore
      whnf := memoE (·.whnf) (fun st mp => { st with whnf := mp }) r.whnf
      infer := memoE (·.infer) (fun st mp => { st with infer := mp }) r.infer
      defeq := memoB r.defeq
      annotate := memoE (·.annot)
        (fun st mp => { st with annot := mp }) r.annotate }

/-- The plain knot at `CheckSM` (no memoization): the fallback for
syntactically ill-formed environments, where depth invariance — the
cache's soundness argument — is unavailable.  The checker never
produces such an environment; the gate keeps the bridge honest without
trusting that. -/
def plainFnsS (env : Env) : Nat → CoreFns CheckSM :=
  coreKnot env fun r => r

/-- The executable core: memoized for well-formed environments, plain
otherwise. -/
def cachedFns (env : Env) : Nat → CoreFns CheckSM :=
  if env.wfB then cachedFnsM env else plainFnsS env

end Setlec
