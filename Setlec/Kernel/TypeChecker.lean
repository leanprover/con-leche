import Setlec.Kernel.Core

/-!
# The pure knot

The core bodies (`Setlec.Kernel.Core`) tied together at `CheckM`, with
no memoization: this instance is the **specification** — all semantic
verification (`Setlec/Model/*`, `Setlec/Verify/*`) reasons about these
fueled entry points, and the refinement bridge (see DESIGN.md) carries
every claim over to the memoized instance the checker executes
(`Setlec.Kernel.TypeCheckerC`).
-/

namespace Setlec

/-- The pure core: the bodies tied at `CheckM`, fuel in the knot. -/
def pureFns (env : Env) : Nat → CoreFns CheckM :=
  coreKnot env id

/-- Head normalization without delta (fueled). -/
def whnfCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr :=
  (pureFns env fuel).whnfCore depth e

/-- The full reduction loop (fueled). -/
def whnf (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr :=
  (pureFns env fuel).whnf depth e

/-- Infer-only type inference (fueled). -/
def inferTypeCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr :=
  (pureFns env fuel).infer depth e

/-- Definitional equality (fueled). -/
def isDefEqCore (env : Env) (fuel depth : Nat) (a b : Expr) : CheckM Bool :=
  (pureFns env fuel).defeq depth a b

/-- The annotation pass (fueled). -/
def annotateCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Expr :=
  (pureFns env fuel).annotate depth e

/-- `ensureSort` over the pure knot (fueled). -/
def ensureSortCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Level :=
  ensureSort (pureFns env fuel) env depth e

/-- The **codomain sort** of a term: the sort of its inferred type,
`ensureSort ∘ inferType` (fueled).  This is exactly the level the
annotation pass computes for a binder — `annotateCore`'s `∀`-clause
runs it on the opened body, its `λ`-clause on the body's inferred type
— and hence the certificate a raw-storage decoration pass reads
(task #100).  Its interned, memoized twin is `codOfI`. -/
def codOfCore (env : Env) (fuel depth : Nat) (e : Expr) : CheckM Level := do
  ensureSortCore env fuel depth (← inferTypeCore env fuel depth e)

end Setlec
