import Setlec.Kernel.Env
import Setlec.Kernel.Level
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Basis

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

/-! The mutually recursive checker core: reduction, inference and
definitional equality share one strictly decreasing fuel.  The mutual
knot is `whnf`'s beta rule: a redex whose codomain sort is not
*certainly* nonzero (`Level.isNonZero`) may be a proof-redex, which is
semantically invisible (Prop collapses to a point in the model), so the
argument is first *certified* against the λ's domain — see DESIGN.md.
Fuel exhaustion is an internal error, never a verdict. -/
mutual

/-- Reduce an expression to weak head normal form.  Definitions are
delta-unfolded (eagerly for now; the lazy strategy of real kernels comes
with performance work); beta redexes reduce when certainly non-Prop or
when the argument certifies against the domain. -/
def whnfCore (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → CheckM Expr
  | 0, _, _ => throw (.internal "fuel exhausted: whnf")
  | fuel + 1, depth, e =>
    match e with
    | .sort u => pure (.sort u)
    | .fvar idx n ty => pure (.fvar idx n ty)
    | .forallE n ty body bi => pure (.forallE n ty body bi)
    | .lam n ty body m => pure (.lam n ty body m)
    | .const n us =>
      match env.find? n with
      | some (.defnInfo cv value) =>
        if us.length = cv.levelParams.length then
          whnfCore env fuel depth (value.instantiateLevelParams cv.levelParams us)
        else pure (.const n us)
      | _ => pure (.const n us)
    | .app f a => do
      match ← whnfCore env fuel depth f with
      | .lam n ty body m =>
        match m.cod with
        | some v =>
          if v.isNonZero then whnfCore env fuel depth (body.instantiate1 a)
          else do
            -- Possibly-Prop redex: certify the argument against the
            -- domain before reducing (the soundness proof needs
            -- `⟦a⟧ ∈ ⟦ty⟧` at every level assignment).  An uncertified
            -- redex stays stuck — sound, and unreachable for
            -- well-typed input.
            let ta ← inferTypeCore env fuel depth a
            if ← isDefEqCore env fuel depth ta ty then
              whnfCore env fuel depth (body.instantiate1 a)
            else pure (.app (.lam n ty body m) a)
        | none => pure (.app (.lam n ty body m) a)
      | f' => pure (.app f' a)
    | .proj sn i e => do
      let e' ← whnfCore env fuel depth e
      match e'.getAppFn with
      | .const c us =>
        -- Only the basis pair constructor is projected (`PSigma'.mk α β a b`).
        match env.find? c with
        | some (.ctorInfo _ nP nF) =>
          let args := e'.getAppArgs
          if c = psigmaMkName ∧ i < nF ∧ args.length = nP + nF ∧ us.length = 2 then
            let mx : Level := .max (us.getD 0 .zero) (us.getD 1 .zero)
            let arg := args.getD (nP + i) (.bvar 0)
            if mx.isNonZero then whnfCore env fuel depth arg
            else do
              -- Possibly-Prop pair: certify that at Prop instances both
              -- the projected argument and the pair collapse to the
              -- proof point (see DESIGN.md on beta certification).
              if ← projCert env fuel depth e' i us nP then
                whnfCore env fuel depth arg
              else pure (.proj sn i e')
          else pure (.proj sn i e')
        | _ => pure (.proj sn i e')
      | _ => pure (.proj sn i e')
    | _ => throw (.notImplemented "whnf beyond the supported fragment")
  termination_by structural fuel _ _ => fuel

/-- Infer the type of an expression whose free variables are `fvar`s below
`depth` (no loose `bvar`s). -/
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
        match ← whnfCore env fuel depth (← inferTypeCore env fuel depth ty) with
        | .sort u => pure (.sort (.imax u v))
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated ∀-binder reached inferType")
    | .lam n ty body m => do
      match m.cod with
      | some v => do
        -- The domain must be a type (and the model needs its
        -- interpretation defined), exactly as in the ∀ rule.
        match ← whnfCore env fuel depth (← inferTypeCore env fuel depth ty) with
        | .sort _ => do
          let bt ← inferTypeCore env fuel (depth + 1)
            (body.instantiate1 (.fvar depth n ty))
          -- Re-check the stored annotation: it must be the sort of the
          -- body's type (the λ-annotation is *trusted* by the ∀ it builds,
          -- so it is *checked* here, where the body's type is at hand).
          match ← whnfCore env fuel (depth + 1) (← inferTypeCore env fuel (depth + 1) bt) with
          | .sort v' => do
            unless ← liftFueled "level comparison" (Level.isEquiv v v') do
              throw (.invalid "λ-annotation does not match the body's sort")
            pure (.forallE n ty (bt.abstract1 depth) ⟨m.bi, some v⟩)
          | _ => throw (.invalid "expected a sort")
        | _ => throw (.invalid "expected a sort")
      | none => throw (.internal "unannotated λ-binder reached inferType")
    | .app f a => do
      let tf ← inferTypeCore env fuel depth f
      match ← whnfCore env fuel depth tf with
      | .forallE _ ty body _ =>
        let ta ← inferTypeCore env fuel depth a
        unless ← isDefEqCore env fuel depth ta ty do
          throw (.invalid "application argument type mismatch")
        pure (body.instantiate1 a)
      | _ => throw (.invalid "function expected")
    | .proj sn i e => do
      -- Only the basis pair type is projected natively; every other
      -- structure's type delta-unfolds (via its `_model` alias) to a
      -- `PSigma'` nest, which is what `whnfCore` produces here.
      match ← whnfCore env fuel depth (← inferTypeCore env fuel depth e) with
      | .app (.app (.const c us) A) B =>
        match env.find? c with
        | some (.indInfo _) =>
          if c = psigmaName then
            match i with
            | 0 => pure A
            | 1 => pure (.app B (.proj sn 0 e))
            | _ => throw (.invalid "projection index out of range")
          else throw (.notImplemented "projection on a non-basis structure")
        | _ => throw (.notImplemented "projection on a non-basis structure")
      | _ => throw (.notImplemented "projection on a non-basis structure")
    | _ => throw (.notImplemented "inferType beyond the supported fragment")
  termination_by structural fuel _ _ => fuel

/-- Certification for projecting a possibly-Prop pair `e₂ =
PSigma'.mk α β a b` (levels `us`): the projected argument's *type's
sort* matches the corresponding level, and the pair's type's sort
matches `max` of the levels.  At Prop instances this collapses both the
argument and the pair to the proof point, which is exactly what the
reduction's soundness needs there. -/
def projCert (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Nat → List Level →
    Nat → CheckM Bool
  | 0, _, _, _, _, _ => throw (.internal "fuel exhausted: projCert")
  | fuel + 1, depth, e₂, i, us, nP => do
    let arg := e₂.getAppArgs.getD (nP + i) (.bvar 0)
    let ta ← inferTypeCore env fuel depth arg
    match ← whnfCore env fuel depth (← inferTypeCore env fuel depth ta) with
    | .sort uT =>
      let okT ← liftFueled "level comparison" (Level.isEquiv uT (us.getD i .zero))
      let te ← inferTypeCore env fuel depth e₂
      match ← whnfCore env fuel depth (← inferTypeCore env fuel depth te) with
      | .sort wT =>
        let okW ← liftFueled "level comparison"
          (Level.isEquiv wT (.max (us.getD 0 .zero) (us.getD 1 .zero)))
        pure (okT && okW)
      | _ => pure false
    | _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- Definitional-equality core. -/
def isDefEqCore (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr → CheckM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: isDefEq")
  | fuel + 1, depth, a, b => do
    match ← whnfCore env fuel depth a, ← whnfCore env fuel depth b with
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
  termination_by structural fuel _ _ _ => fuel

end

/-- The shared fuel for the checker core: bounds the combined recursion
depth of reduction, inference and definitional equality.  Exhaustion is
an internal error, never a verdict. -/
def checkFuel : Nat := 100000

/-- `whnfCore` with the standard fuel. -/
def whnf (env : Env) (depth : Nat) (e : Expr) : CheckM Expr :=
  whnfCore env checkFuel depth e

/-- `inferTypeCore` with the standard fuel. -/
def inferType (env : Env) (depth : Nat) (e : Expr) : CheckM Expr :=
  inferTypeCore env checkFuel depth e

/-- `isDefEqCore` with the standard fuel. -/
def isDefEq (env : Env) (depth : Nat) (a b : Expr) : CheckM Bool :=
  isDefEqCore env checkFuel depth a b

/-- Ensure `e` (the type of some expression) is a sort, returning its level. -/
def ensureSort (env : Env) (depth : Nat) (e : Expr) : CheckM Level := do
  match ← whnf env depth e with
  | .sort u => pure u
  | _ => throw (.invalid "expected a sort")

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
    match ← whnf env depth tf with
    | .forallE _ ty _ _ =>
      let ta ← inferType env depth a'
      unless ← isDefEq env depth ta ty do
        throw (.invalid "application argument type mismatch")
      pure (.app f' a')
    | _ => throw (.invalid "function expected")
  | depth, .forallE n ty body m => do
    let ty' ← annotate env depth ty
    let body' ← annotate env (depth + 1) (body.instantiate1 (.fvar depth n ty'))
    let v ← ensureSort env (depth + 1) (← inferType env (depth + 1) body')
    pure (.forallE n ty' (body'.abstract1 depth) ⟨m.bi, some v⟩)
  | depth, .lam n ty body m => do
    let ty' ← annotate env depth ty
    let body' ← annotate env (depth + 1) (body.instantiate1 (.fvar depth n ty'))
    let bt ← inferType env (depth + 1) body'
    let v ← ensureSort env (depth + 1) (← inferType env (depth + 1) bt)
    pure (.lam n ty' (body'.abstract1 depth) ⟨m.bi, some v⟩)
  | _, .letE _ _ _ _ => throw (.notImplemented "annotate: let-expressions")
  | depth, .proj sn i e => do
    let e' ← annotate env depth e
    -- Run the projection rule (the one place it is checked; this
    -- establishes the semantic proj clause of `AnnotOk`).
    match ← whnf env depth (← inferType env depth e') with
    | .app (.app (.const c _) _) _ =>
      match env.find? c with
      | some (.indInfo _) =>
        unless c = psigmaName do
          throw (.notImplemented "projection on a non-basis structure")
        unless i < 2 do
          throw (.invalid "projection index out of range")
        pure (.proj sn i e')
      | _ => throw (.notImplemented "projection on a non-basis structure")
    | _ => throw (.notImplemented "projection on a non-basis structure")
  | _, .lit _ => throw (.notImplemented "annotate: literals")
termination_by _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end Setlec
