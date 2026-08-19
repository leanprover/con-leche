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

Current fragment: sorts, dependent function types, lambdas and
applications (with beta reduction).

## Binders

Following nanoda, an opened binder becomes `fvar d n ty` where `d` is the
current binder depth (a de Bruijn *level*) and `ty` the binder's type; the
local context is implicit in the term.  `inferType` and `isDefEq` thread the
depth.  `isDefEq` opens each side's body with that side's *own* annotation
at the same depth (the annotation of an `fvar` is never compared — `fvar`s
are equal iff their depths are), which matches how the model interprets
each side.

## Sort annotations

Binders carry a codomain-sort annotation (`BinderMeta.cod`), computed
once by `annotate` (the only place binder bodies are type-checked) and
trusted by `inferType` thereafter; the set-model's Prop/Type classifier
reads it (see DESIGN.md).  Deviation from real kernels (to be removed):
`isDefEq` on two ∀-types additionally checks that the codomain
annotations are equivalent levels — for well-typed inputs this is
implied, and with annotations the check is a cheap level comparison.

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

/-- Fuel for `whnf`: bounds delta-unfolding chains; exhaustion is an
internal error, never a verdict. -/
def whnfFuel : Nat := 10000

/-- Reduce an expression to weak head normal form.  Definitions are
delta-unfolded (eagerly for now; the lazy strategy of real kernels comes
with performance work).  Constants that are not definitions — or whose
level-argument count is wrong, which inference rejects anyway — are stuck.
-/
def whnf (env : Env) : (fuel : Nat) → Expr → CheckM Expr
  | 0, _ => throw (.internal "fuel exhausted: whnf")
  | fuel + 1, e =>
    match e with
    | .sort u => pure (.sort u)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .forallE n ty body bi => pure (.forallE n ty body bi)
    | .lam n ty body m => pure (.lam n ty body m)
    | .const n us =>
      match env.find? n with
      | some (.defnInfo cv value) =>
        if us.length = cv.levelParams.length then
          whnf env fuel (value.instantiateLevelParams cv.levelParams us)
        else pure (.const n us)
      | _ => pure (.const n us)
    | .app f a => do
      match ← whnf env fuel f with
      | .lam n ty body m =>
        -- Beta only on redexes whose codomain sort is *certainly* nonzero:
        -- proof-redexes are semantically invisible (Prop collapses to a
        -- point in the model) and must stay stuck (see DESIGN.md; real
        -- kernels compensate with proof irrelevance instead).
        match m.cod with
        | some v =>
          if v.isNonZero then whnf env fuel (body.instantiate1 a)
          else pure (.app (.lam n ty body m) a)
        | none => pure (.app (.lam n ty body m) a)
      | f' => pure (.app f' a)
    | _ => throw (.notImplemented "whnf beyond the supported fragment")

/-- Ensure `e` (the type of some expression) is a sort, returning its level. -/
def ensureSort (env : Env) (e : Expr) : CheckM Level := do
  match ← whnf env whnfFuel e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

/-- Fueled definitional-equality core.  Fuel exhaustion is an internal
error, not a verdict. -/
def isDefEqCore (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr → CheckM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: isDefEq")
  | fuel + 1, depth, a, b => do
    match ← whnf env whnfFuel a, ← whnf env whnfFuel b with
    | .sort u, .sort v => liftFueled "level comparison" (Level.isEquiv u v)
    | .fvar i _ _, .fvar j _ _ => pure (i == j)
    | .const n us, .const n' us' =>
      if n = n' then liftFueled "level comparison" (Level.isEquivList us us')
      else pure false
    | .forallE n₁ ty₁ body₁ m₁, .forallE n₂ ty₂ body₂ m₂ => do
      unless ← isDefEqCore env fuel depth ty₁ ty₂ do return false
      let b₁ := body₁.instantiate1 (.fvar depth n₁ ty₁)
      let b₂ := body₂.instantiate1 (.fvar depth n₂ ty₂)
      unless ← isDefEqCore env fuel (depth + 1) b₁ b₂ do return false
      -- Deviation (see module docstring): codomain sorts must agree —
      -- with annotations this is a cheap level comparison.
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ => liftFueled "level comparison" (Level.isEquiv v₁ v₂)
      | _, _ => throw (.internal "unannotated ∀-binder reached isDefEq")
    | .lam n₁ ty₁ body₁ m₁, .lam n₂ ty₂ body₂ m₂ => do
      unless ← isDefEqCore env fuel depth ty₁ ty₂ do return false
      let b₁ := body₁.instantiate1 (.fvar depth n₁ ty₁)
      let b₂ := body₂.instantiate1 (.fvar depth n₂ ty₂)
      unless ← isDefEqCore env fuel (depth + 1) b₁ b₂ do return false
      -- Deviation, as for ∀ (see module docstring).
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ => liftFueled "level comparison" (Level.isEquiv v₁ v₂)
      | _, _ => throw (.internal "unannotated λ-binder reached isDefEq")
    | .app f₁ a₁, .app f₂ a₂ => do
      -- Stuck applications: congruence.  (Eta is not yet handled; a
      -- `false` answer is always sound.)
      unless ← isDefEqCore env fuel depth f₁ f₂ do return false
      isDefEqCore env fuel depth a₁ a₂
    -- Distinct whnf-stuck head symbols: `false` is always sound, and
    -- `whnf` has already thrown on unsupported heads, so no unimplemented
    -- case can hide here.  (Eta-equalities are missed; completeness work.)
    | _, _ => pure false

/-- A generous fuel bound for `isDefEqCore`. -/
def defEqFuel : Nat := 10000

/-- Definitional equality at binder depth `depth`. -/
def isDefEq (env : Env) (depth : Nat) (a b : Expr) : CheckM Bool :=
  isDefEqCore env defEqFuel depth a b

/-- Infer the type of an expression whose free variables are `fvar`s below
`depth` (no loose `bvar`s).  Fueled: the λ-rule re-checks the stored
codomain-sort annotation against the inferred body type, a recursion that
is not structural.  Fuel exhaustion is an internal error, not a verdict. -/
def inferTypeCore (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → CheckM Expr
  | 0, _, _ => throw (.internal "fuel exhausted: inferType")
  | fuel + 1, depth, e =>
    match e with
    | .sort u => pure (.sort (.succ u))
    | .fvar _ _ ty => pure ty
    | .const n us => do
      match env.find? n with
      | none => throw (.invalid s!"unknown constant {n}")
      | some ci =>
        let cv := ci.toConstantVal
        unless us.length = cv.levelParams.length do
          throw (.invalid s!"incorrect number of universe levels for {n}")
        pure (cv.type.instantiateLevelParams cv.levelParams us)
    | .forallE _ ty _ m => do
      -- The codomain-sort annotation is trusted: the body was checked once,
      -- by real inference, when the annotation was created (`annotate`).
      match m.cod with
      | some v => do
        let u ← ensureSort env (← inferTypeCore env fuel depth ty)
        pure (.sort (.imax u v))
      | none => throw (.internal "unannotated ∀-binder reached inferType")
    | .lam n ty body m => do
      match m.cod with
      | some v => do
        -- The domain must be a type (and the model needs its
        -- interpretation defined), exactly as in the ∀ rule.
        let _ ← ensureSort env (← inferTypeCore env fuel depth ty)
        let bt ← inferTypeCore env fuel (depth + 1)
          (body.instantiate1 (.fvar depth n ty))
        -- Re-check the stored annotation: it must be the sort of the
        -- body's type (the λ-annotation is *trusted* by the ∀ it builds,
        -- so it is *checked* here, where the body's type is at hand).
        let v' ← ensureSort env (← inferTypeCore env fuel (depth + 1) bt)
        unless ← liftFueled "level comparison" (Level.isEquiv v v') do
          throw (.invalid "λ-annotation does not match the body's sort")
        pure (.forallE n ty (bt.abstract1 depth) ⟨m.bi, some v⟩)
      | none => throw (.internal "unannotated λ-binder reached inferType")
    | .app f a => do
      let tf ← inferTypeCore env fuel depth f
      match ← whnf env whnfFuel tf with
      | .forallE _ ty body _ =>
        let ta ← inferTypeCore env fuel depth a
        unless ← isDefEq env depth ta ty do
          throw (.invalid "application argument type mismatch")
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | _ => throw (.notImplemented "inferType beyond the supported fragment")

/-- Fuel for `inferTypeCore`: bounds the λ-rule's annotation re-check
recursion.  Exhaustion is an internal error, never a verdict. -/
def inferFuel : Nat := 10000

/-- `inferTypeCore` with the standard fuel. -/
def inferType (env : Env) (depth : Nat) (e : Expr) : CheckM Expr :=
  inferTypeCore env inferFuel depth e

/-- Compute the codomain-sort annotations of every binder in `e`, bottom-up,
by real inference on the opened (already annotated) body.  This is the one
place binder bodies are type-checked; `inferType` afterwards trusts the
annotations.  For a `forallE` the annotation is the body's sort (so this
also checks that the body *is* a type — the ∀-formation rule); for a `lam`
it is the sort of the body's type. -/
def annotate (env : Env) : (depth : Nat) → Expr → CheckM Expr
  | _, .bvar i => pure (.bvar i)
  | _, .fvar idx n ty => pure (.fvar idx n ty)
  | _, .sort u => pure (.sort u)
  | _, .const n us => pure (.const n us)
  | depth, .app f a => do
    let f' ← annotate env depth f
    let a' ← annotate env depth a
    -- Run the application rule here (the one place typing is checked):
    -- this establishes the semantic well-typedness clause for `app`
    -- nodes that beta-reduction soundness relies on (see DESIGN.md).
    let tf ← inferType env depth f'
    match ← whnf env whnfFuel tf with
    | .forallE _ ty _ _ =>
      let ta ← inferType env depth a'
      unless ← isDefEq env depth ta ty do
        throw (.invalid "application argument type mismatch")
      pure (.app f' a')
    | _ => throw (.invalid "function expected")
  | depth, .forallE n ty body m => do
    let ty' ← annotate env depth ty
    let body' ← annotate env (depth + 1) (body.instantiate1 (.fvar depth n ty'))
    let v ← ensureSort env (← inferType env (depth + 1) body')
    pure (.forallE n ty' (body'.abstract1 depth) ⟨m.bi, some v⟩)
  | depth, .lam n ty body m => do
    let ty' ← annotate env depth ty
    let body' ← annotate env (depth + 1) (body.instantiate1 (.fvar depth n ty'))
    let bt ← inferType env (depth + 1) body'
    let v ← ensureSort env (← inferType env (depth + 1) bt)
    pure (.lam n ty' (body'.abstract1 depth) ⟨m.bi, some v⟩)
  | _, .letE _ _ _ _ => throw (.notImplemented "annotate: let-expressions")
  | _, .lit _ => throw (.notImplemented "annotate: literals")
  | _, .proj _ _ _ => throw (.notImplemented "annotate: projections")
termination_by _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

end Setlec
