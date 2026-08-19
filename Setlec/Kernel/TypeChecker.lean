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
      | f' => do
        match ← iotaRec env fuel depth (.app f' a) with
        | some e'' => whnfCore env fuel depth e''
        | none => pure (.app f' a)
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
      | .app (.app (.const c _us) A) B =>
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

/-- Is this (whnf'd) type expression a unit-like inductive type — a
stored inductive whose recursor (under the `<ind>.rec` naming
convention) has no indices and a single zero-field rule?  All of its
inhabitants are then equal (in the model: the proof point; the
environment invariant supplies the fact for the stored constant). -/
def isUnitLikeTy (env : Env) : Expr → Bool
  | .const c _ =>
    (match env.find? c with
      | some (.indInfo _) => true
      | _ => false) &&
    (match env.find? (c.str "rec") with
      | some (.recInfo _ _ _ _ 0 [r]) => r.nfields == 0
      | _ => false) &&
    -- native unit semantics: only for structures without a model alias
    (env.find? ((c.str "rec").str "_model")).isNone &&
    (env.find? (c.str "_model")).isNone
  | _ => false

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
    | .fvar i n₁ ty₁, .fvar j n₂ ty₂ =>
      if i == j then pure true
      else stuckIrrel env fuel depth (.fvar i n₁ ty₁) (.fvar j n₂ ty₂)
    | .const n us, .const n' us' =>
      if n = n' then
        if ← liftFueled "level comparison" (Level.isEquivList us us') then
          pure true
        else stuckIrrel env fuel depth (.const n us) (.const n' us')
      else stuckIrrel env fuel depth (.const n us) (.const n' us')
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
      -- Stuck applications: congruence, else proof irrelevance.
      -- (Eta is not yet handled; a `false` answer is always sound.)
      if ← isDefEqCore env fuel depth f₁ f₂ then
        if ← isDefEqCore env fuel depth a₁ a₂ then
          pure true
        else stuckIrrel env fuel depth (.app f₁ a₁) (.app f₂ a₂)
      else stuckIrrel env fuel depth (.app f₁ a₁) (.app f₂ a₂)
    | .proj s₁ i₁ e₁, .proj s₂ i₂ e₂ => do
      -- Stuck projections: congruence, else proof irrelevance.
      if i₁ == i₂ then
        if ← isDefEqCore env fuel depth e₁ e₂ then pure true
        else stuckIrrel env fuel depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
      else stuckIrrel env fuel depth (.proj s₁ i₁ e₁) (.proj s₂ i₂ e₂)
    -- One-sided λ: eta, else proof irrelevance.
    | .lam n₁ ty₁ body₁ m₁, b₂ => do
      if ← etaCert env fuel depth n₁ ty₁ body₁ m₁ b₂ then pure true
      else stuckIrrel env fuel depth (.lam n₁ ty₁ body₁ m₁) b₂
    | a₁, .lam n₂ ty₂ body₂ m₂ => do
      if ← etaCert env fuel depth n₂ ty₂ body₂ m₂ a₁ then pure true
      else stuckIrrel env fuel depth a₁ (.lam n₂ ty₂ body₂ m₂)
    -- Distinct whnf-stuck head symbols: only proof irrelevance can
    -- equate them; `false` is always sound, and `whnf` has already
    -- thrown on unsupported heads, so no unimplemented case can hide
    -- here.
    | e₁, e₂ => stuckIrrel env fuel depth e₁ e₂
  termination_by structural fuel _ _ _ => fuel

/-- One iota step: the expression is a stored recursor applied to
exactly its telescope (params, motives, minors, indices, major), the
major premise whnfs to a fully applied constructor with a matching
rule, and the spine is certified against the recursor's own (pinned,
annotated) type.  The result is the rule's rhs applied to the
non-index prefix and the constructor's fields; over-application is
handled by the outer `whnf` app recursion. -/
def iotaRec (env : Env) : (fuel : Nat) → (depth : Nat) → Expr →
    CheckM (Option Expr)
  | 0, _, _ => throw (.internal "fuel exhausted: iotaRec")
  | fuel + 1, depth, e => do
    match e.getAppFn with
    | .const c us =>
      match env.find? c with
      | some (.recInfo cv nP nM nm ni rules) =>
        let args := e.getAppArgs
        if args.length = nP + nM + nm + ni + 1 then
          let major ← whnfCore env fuel depth
            (args.getD (nP + nM + nm + ni) (.bvar 0))
          match major.getAppFn with
          | .const cj usj =>
            match env.find? cj with
            | some (.ctorInfo cvj cnP cnF) =>
              match rules.find? (fun r => r.ctor == cj) with
              | some r =>
                let margs := major.getAppArgs
                if margs.length = cnP + cnF ∧ r.nfields = cnF then
                  -- the constructor's levels must agree with the
                  -- recursor's instantiation (the rule links their
                  -- level parameters by name)
                  if ← liftFueled "level comparison" (Level.isEquivList usj
                      (cvj.levelParams.map fun p =>
                        Level.subst cv.levelParams us (.param p))) then
                   if ← defEqList env fuel depth (margs.take cnP)
                      (args.take cnP) then
                    if ← iotaCerts env fuel depth
                       (cv.type.instantiateLevelParams cv.levelParams us)
                       (args.take (nP + nM + nm + ni)) then
                     pure (some (Expr.mkAppN
                       (r.rhs.instantiateLevelParams cv.levelParams us)
                       (args.take (nP + nM + nm) ++ margs.drop cnP)))
                    else pure none
                   else pure none
                  else pure none
                else pure none
              | none => pure none
            | _ => pure none
          | _ => pure none
        else pure none
      | _ => pure none
    | _ => pure none
  termination_by structural fuel _ _ => fuel

/-- Certify a spine against a recursor telescope: each argument's
inferred type is defeq to the corresponding (instantiated) domain.
This is what hands the soundness proof the memberships the iota
equations need, at every level assignment. -/
def iotaCerts (env : Env) : (fuel : Nat) → (depth : Nat) → Expr →
    List Expr → CheckM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: iotaCerts")
  | _ + 1, _, _, [] => pure true
  | fuel + 1, depth, .forallE _ ty body _, arg :: rest => do
    let ta ← inferTypeCore env fuel depth arg
    if ← isDefEqCore env fuel depth ta ty then
      iotaCerts env fuel depth (body.instantiate1 arg) rest
    else pure false
  | _ + 1, _, _, _ :: _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- Pairwise definitional equality of two spines (used to check a
major's constructor parameters against the recursor's). -/
def defEqList (env : Env) : (fuel : Nat) → (depth : Nat) → List Expr →
    List Expr → CheckM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: defEqList")
  | _ + 1, _, [], [] => pure true
  | fuel + 1, depth, a :: as, b :: bs => do
    if ← isDefEqCore env fuel depth a b then
      defEqList env fuel depth as bs
    else pure false
  | _ + 1, _, _, _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- The fallback for structurally distinct stuck terms: pair eta in
either direction, else proof irrelevance. -/
def stuckIrrel (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr →
    CheckM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: stuckIrrel")
  | fuel + 1, depth, a, b => do
    if ← pairEtaCert env fuel depth a b then pure true
    else if ← pairEtaCert env fuel depth b a then pure true
    else proofIrrel env fuel depth a b
  termination_by structural fuel _ _ _ => fuel

/-- Pair eta certification: `a` is a fully applied structure
constructor (a stored constructor that is the single rule of an
index-free recursor, under the `<ind>.rec` naming convention), `b`
inhabits the matching structure type at the same levels, and `a`'s
two fields are defeq to `b`'s projections.  In the model both sides
are then the pair of `b`'s components (or the proof point at the Prop
collapse); the environment invariant supplies the facts for the stored
constants. -/
def pairEtaCert (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr →
    CheckM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: pairEtaCert")
  | fuel + 1, depth, .app (.app (.app (.app (.const c us) _pα) _pβ) s₁) s₂,
      b => do
    match env.find? c with
    | some (.ctorInfo _ nP nF) =>
      if nP = 2 ∧ nF = 2 then
        let tb ← inferTypeCore env fuel depth b
        match ← whnfCore env fuel depth tb with
        | .app (.app (.const c' us') _A) _B =>
          match env.find? c' with
          | some (.indInfo _) =>
            match env.find? (c'.str "rec") with
            | some (.recInfo _ _ _ _ ni rules) =>
              match rules with
              | [r] =>
                if ni = 0 ∧ r.ctor = c ∧ r.nfields = 2 ∧
                    (env.find? (c.str "_model")).isNone = true ∧
                    (env.find? ((c'.str "rec").str "_model")).isNone
                      = true then
                  if ← liftFueled "level comparison"
                      (Level.isEquivList us us') then
                    if ← isDefEqCore env fuel depth s₁ (.proj c' 0 b) then
                      isDefEqCore env fuel depth s₂ (.proj c' 1 b)
                    else pure false
                  else pure false
                else pure false
              | _ => pure false
            | _ => pure false
          | _ => pure false
        | _ => pure false
      else pure false
    | _ => pure false
  | _ + 1, _, _, _ => pure false
  termination_by structural fuel _ _ _ => fuel

/-- Eta certification for a one-sided λ against a stuck term `b`: `b`'s
type whnfs to a `∀` whose domain is defeq to the λ's and whose codomain
annotation agrees, and the λ's body is pointwise the application of `b`.
The λ is then `b`'s eta-expansion (soundness: `SetTheory.lam_eta`). -/
def etaCert (env : Env) : (fuel : Nat) → (depth : Nat) →
    Name → Expr → Expr → BinderMeta → Expr → CheckM Bool
  | 0, _, _, _, _, _, _ => throw (.internal "fuel exhausted: etaCert")
  | fuel + 1, depth, n₁, ty₁, body₁, m₁, b => do
    let tb ← inferTypeCore env fuel depth b
    match ← whnfCore env fuel depth tb with
    | .forallE _ ty₂ _ m₂ =>
      match m₁.cod, m₂.cod with
      | some v₁, some v₂ =>
        if ← liftFueled "level comparison" (Level.isEquiv v₁ v₂) then
          if ← isDefEqCore env fuel depth ty₂ ty₁ then
            isDefEqCore env fuel (depth + 1)
              (body₁.instantiate1 (.fvar depth n₁ ty₁))
              (.app b (.fvar depth n₁ ty₁))
          else pure false
        else pure false
      | _, _ => pure false
    | _ => pure false
  termination_by structural fuel _ => fuel

/-- Proof irrelevance certification: both sides' types whnf to the
basis unit type (all of whose inhabitants are the proof point in the
model), or both sides' types' *sorts* are `Prop`.  In the model
everything inhabiting a proposition is the proof point, so any two such
terms are equal — no common-type check is needed for soundness. -/
def proofIrrel (env : Env) : (fuel : Nat) → (depth : Nat) → Expr → Expr →
    CheckM Bool
  | 0, _, _, _ => throw (.internal "fuel exhausted: proofIrrel")
  | fuel + 1, depth, a, b => do
    let ta ← inferTypeCore env fuel depth a
    if isUnitLikeTy env (← whnfCore env fuel depth ta) then
      let tb ← inferTypeCore env fuel depth b
      if isUnitLikeTy env (← whnfCore env fuel depth tb) then
        pure true
      else
        pure false
    else
      match ← whnfCore env fuel depth (← inferTypeCore env fuel depth ta) with
      | .sort uT =>
        let okA ← liftFueled "level comparison" (Level.isEquiv uT .zero)
        let tb ← inferTypeCore env fuel depth b
        match ← whnfCore env fuel depth (← inferTypeCore env fuel depth tb) with
        | .sort vT =>
          let okB ← liftFueled "level comparison" (Level.isEquiv vT .zero)
          pure (okA && okB)
        | _ => pure false
      | _ => pure false
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
