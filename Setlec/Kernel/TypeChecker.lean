import Setlec.Kernel.Env
import Setlec.Kernel.Level
import Setlec.Kernel.ExprOps

/-!
# Type inference, reduction and definitional equality

The heart of the checker.  All functions work on the supported fragment and
`throw` a `CheckError` otherwise:

* `.notImplemented`: a positively detected not-yet-supported feature; the
  driver turns this into the arena "declined" exit code.
* `.invalid`: the input is wrong; "rejected".
* `.internal`: an internal failure of unclear cause (e.g. fuel exhaustion);
  never a verdict about the input.

Current fragment: sorts and dependent function types.

## Binders

Following nanoda, an opened binder becomes `fvar d n ty` where `d` is the
current binder depth (a de Bruijn *level*) and `ty` the binder's type; the
local context is implicit in the term.  `inferType` and `isDefEq` thread the
depth.  `isDefEq` opens each side's body with that side's *own* annotation
at the same depth (the annotation of an `fvar` is never compared — `fvar`s
are equal iff their depths are), which matches how the model interprets
each side.

## Deviation from real kernels (to be removed)

`isDefEq` on two ∀-types additionally checks that the *codomain sorts* of
the two bodies are semantically equal levels.  Real kernels do not check
this — for well-typed inputs it is implied — but our model interprets
Prop-valued and Type-valued products differently, and proving that two
algorithm-defeq bodies have equal sorts requires metatheory (sort
coherence) we do not have yet.  The extra check only costs completeness
and performance, not soundness.

Verification: `Setlec.Model.TypeChecker`.
-/

namespace Setlec

inductive CheckError where
  | notImplemented (what : String)
  | invalid (msg : String)
  | internal (msg : String)
  deriving Repr

instance : ToString CheckError where
  toString
    | .notImplemented what => s!"not implemented yet: {what}"
    | .invalid msg => s!"invalid: {msg}"
    | .internal msg => s!"internal error: {msg}"

abbrev CheckM := Except CheckError

/-- Lift a fuel-style partial result; `none` is an internal error. -/
def liftFueled (what : String) : Option α → CheckM α
  | some a => pure a
  | none => throw (.internal s!"fuel exhausted: {what}")

/-- Reduce an expression to weak head normal form. -/
def whnf (_env : Env) : Expr → CheckM Expr
  | .sort u => pure (.sort u)
  | .fvar idx n ty => pure (.fvar idx n ty)
  | .forallE n ty body bi => pure (.forallE n ty body bi)
  | _ => throw (.notImplemented "whnf beyond sorts, fvars and foralls")

/-- Ensure `e` (the type of some expression) is a sort, returning its level. -/
def ensureSort (env : Env) (e : Expr) : CheckM Level := do
  match ← whnf env e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-- Infer the type of an expression whose free variables are `fvar`s below
`depth` (no loose `bvar`s). -/
def inferType (env : Env) (depth : Nat) : Expr → CheckM Expr
  | .sort u => pure (.sort (.succ u))
  | .fvar _ _ ty => pure ty
  | .forallE n ty body _ => do
    let u ← ensureSort env (← inferType env depth ty)
    let v ← ensureSort env (← inferType env (depth + 1) (body.instantiate1 (.fvar depth n ty)))
    pure (.sort (.imax u v))
  | _ => throw (.notImplemented "inferType beyond sorts, fvars and foralls")
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- Fueled definitional-equality core.  Fuel exhaustion is an internal
error, not a verdict. -/
def isDefEqCore (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr → CheckM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: isDefEq")
  | fuel + 1, depth, a, b => do
    match ← whnf env a, ← whnf env b with
    | .sort u, .sort v => liftFueled "level comparison" (Level.isEquiv u v)
    | .fvar i _ _, .fvar j _ _ => pure (i == j)
    | .forallE n₁ ty₁ body₁ _, .forallE n₂ ty₂ body₂ _ => do
      unless ← isDefEqCore env fuel depth ty₁ ty₂ do return false
      let b₁ := body₁.instantiate1 (.fvar depth n₁ ty₁)
      let b₂ := body₂.instantiate1 (.fvar depth n₂ ty₂)
      unless ← isDefEqCore env fuel (depth + 1) b₁ b₂ do return false
      -- Deviation (see module docstring): codomain sorts must agree.
      let v₁ ← ensureSort env (← inferType env (depth + 1) b₁)
      let v₂ ← ensureSort env (← inferType env (depth + 1) b₂)
      liftFueled "level comparison" (Level.isEquiv v₁ v₂)
    -- Distinct supported head symbols are never definitionally equal.
    | .sort _, .fvar .. | .sort _, .forallE ..
    | .fvar .., .sort _ | .fvar .., .forallE ..
    | .forallE .., .sort _ | .forallE .., .fvar .. => pure false
    | _, _ => throw (.notImplemented "defEq beyond sorts, fvars and foralls")

/-- A generous fuel bound for `isDefEqCore`. -/
def defEqFuel : Nat := 10000

/-- Definitional equality at binder depth `depth`. -/
def isDefEq (env : Env) (depth : Nat) (a b : Expr) : CheckM Bool :=
  isDefEqCore env defEqFuel depth a b

end Setlec
