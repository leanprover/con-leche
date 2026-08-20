import Setlec.Kernel.TypeChecker
import Setlec.SetTheory.Basic
import Setlec.Verify.Level
import Setlec.Verify.Shift
import Setlec.Verify.EnvWF
import Setlec.Verify.Leaves
import Setlec.Model.BasisVal
import Setlec.Model.IndModel

/-!
# Interpretation of expressions in the set model

`interpExpr cval env φ d ρ e` maps a kernel expression to an element of
the set-theoretic universe `V`, where

* `cval` values the constants (level-polymorphically: each constant is a
  function of the level-parameter assignment),
* `φ` assigns the universe level parameters,
* `d` is the current binder depth,
* `ρ : Nat → V` values the free variables (`fvar idx …` ↦ `ρ idx`; the
  annotation at an `fvar` leaf is *not* read).

It is partial (`Option`): unsupported expression forms are uninterpreted,
and it grows in lockstep with the checker.

A constant `const n us` is valued at the assignment sending the
constant's own parameters to the evaluation of `us` under `φ` (and other
names to `φ` itself — `Level.substFn`); an `EnvModel`'s `val_params`
field records that the valuation only reads its own parameters, so the
tail is irrelevant.

A `∀`-type is interpreted by opening the binder at index `d` — exactly as
the checker does — and forming the dependent product `SetTheory.pi` over
the domain; the Prop/Type classifier `pi` needs is the evaluation of the
binder's stored codomain-sort annotation (`BinderMeta.cod`) — unannotated
binders are uninterpreted.  `AnnotOk` states that annotations are
*truthful* (each fibre lands in the annotated universe, hereditarily);
it is established once by the annotation pass (`annotate_sound`) and is
a hypothesis of the soundness theorems.

`FvarsOk` states the typing assumptions about the (implicit) local
context.  `EnvModel` packages a model of a whole environment.
-/

set_option linter.unusedVariables false
set_option linter.defProp false

namespace Setlec

variable (V : Type u) [SetTheory V]

open SetTheory

/-- Update a valuation at one index. -/
def updV (ρ : Nat → V) (d : Nat) (x : V) : Nat → V :=
  fun i => if i = d then x else ρ i

/-- Interpret an expression under constant valuation `cval`, level
assignment `φ`, binder depth `d` and free-variable valuation `ρ`. -/
def interpExpr (cval : ConstVal V) (env : Env) (φ : Name → Nat) :
    (d : Nat) → (ρ : Nat → V) → Expr → Option V
  | _, _, .sort u => some (univ (u.eval φ))
  | _, ρ, .fvar idx _ _ => some (ρ idx)
  | _, _, .const n us =>
    match env.find? n with
    | some ci =>
      if us.length = ci.toConstantVal.levelParams.length then
        some (cval n (Level.substFn φ ci.toConstantVal.levelParams us))
      else none
    | none => none
  | d, ρ, .forallE n ty body m =>
    match m.cod with
    | none => none
    | some v =>
      match interpExpr cval env φ d ρ ty with
      | none => none
      | some A => some (pi (v.eval φ) A fun x =>
          (interpExpr cval env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
  | d, ρ, .lam n ty body m =>
    match m.cod with
    | none => none
    | some v =>
      match interpExpr cval env φ d ρ ty with
      | none => none
      | some A => some (SetTheory.lam (v.eval φ) A fun x =>
          (interpExpr cval env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty))).getD SetTheory.empty)
  | d, ρ, .app f a =>
    match interpExpr cval env φ d ρ f, interpExpr cval env φ d ρ a with
    | some vf, some va => some (SetTheory.app vf va)
    | _, _ => none
  | d, ρ, .proj _ i e =>
    match interpExpr cval env φ d ρ e with
    | some ve =>
      if i = 0 then some (sfst ve) else if i = 1 then some (ssnd ve) else none
    | none => none
  | _, _, _ => none
termination_by _ _ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Truthfulness of the codomain-sort annotations: every `∀`-subterm is
annotated, and over every member of the domain's interpretation the
(defined) fibre lands in the annotated universe, hereditarily; `lam`
bodies are covered so that the invariant survives beta reduction. -/
def AnnotOk (cval : ConstVal V) (env : Env) (φ : Name → Nat) :
    (d : Nat) → (ρ : Nat → V) → Expr → Prop
  | d, ρ, .forallE n ty body m =>
    AnnotOk cval env φ d ρ ty ∧
    (∃ v, m.cod = some v) ∧
    ∀ x A, interpExpr V cval env φ d ρ ty = some A → x ∈ˢ A →
      AnnotOk cval env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty)) ∧
      ∀ v, m.cod = some v →
        ∃ w, interpExpr V cval env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty)) = some w ∧
          w ∈ˢ univ (v.eval φ)
  | d, ρ, .lam n ty body m =>
    AnnotOk cval env φ d ρ ty ∧
    (∃ v, m.cod = some v) ∧
    ∀ x A, interpExpr V cval env φ d ρ ty = some A → x ∈ˢ A →
      AnnotOk cval env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty)) ∧
      ∀ v, m.cod = some v →
        ∃ w B, interpExpr V cval env φ (d + 1) (updV V ρ d x)
            (body.instantiate1 (.fvar d n ty)) = some w ∧
          w ∈ˢ B ∧ B ∈ˢ univ (v.eval φ)
  | d, ρ, .app f a =>
    AnnotOk cval env φ d ρ f ∧ AnnotOk cval env φ d ρ a ∧
    ∃ vf va vE A B, interpExpr V cval env φ d ρ f = some vf ∧
      interpExpr V cval env φ d ρ a = some va ∧
      vf ∈ˢ pi vE A B ∧ va ∈ˢ A ∧ ∀ x, x ∈ˢ A → B x ∈ˢ univ vE
  | d, ρ, .proj _ i e =>
    AnnotOk cval env φ d ρ e ∧ i < 2 ∧
    ∃ ve u v A Bf, interpExpr V cval env φ d ρ e = some ve ∧
      ve ∈ˢ sigmaSet (Nat.max u v) A Bf ∧
      A ∈ˢ univ u ∧ ∀ x, x ∈ˢ A → Bf x ∈ˢ univ v
  | _, _, _ => True
termination_by d ρ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- The typing assumptions about the implicit local context, as
conditions on the free-variable leaf closure: every leaf (including
those inside annotations, hereditarily) is bounded by the depth, its
annotation's annotations are truthful, and its valuation is a member of
its annotated type's interpretation. -/
def FvarsOk (cval : ConstVal V) (env : Env) (φ : Name → Nat) (d : Nat) (ρ : Nat → V)
    (e : Expr) : Prop :=
  ∀ l ∈ e.fvarLeaves, l.1 < d ∧ AnnotOk V cval env φ d ρ l.2.2 ∧
    ∃ T, interpExpr V cval env φ d ρ l.2.2 = some T ∧ ρ l.1 ∈ˢ T

/-- The canonical valuation for closed terms. -/
def rho0 : Nat → V := fun _ => SetTheory.empty

/-- Interpretation of a closed expression (as they appear in declarations). -/
def interpClosed (cval : ConstVal V) (env : Env) (φ : Name → Nat) (e : Expr) : Option V :=
  interpExpr V cval env φ 0 (rho0 V) e

/-- Values fitting an opened `∀`-telescope: each value is a member of
the interpretation of the corresponding (progressively instantiated)
domain; `d'`, `ρ'`, `rest` describe the fully opened residual body. -/
inductive TeleFit (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (φ : Name → Nat) :
    Nat → (Nat → V) → Expr → List V → Nat → (Nat → V) → Expr → Prop
  | nil {d ρ e} : TeleFit V cval env φ d ρ e [] d ρ e
  | cons {d ρ n ty body m x xs d' ρ' rest A} :
      interpExpr V cval env φ d ρ ty = some A →
      x ∈ˢ A →
      TeleFit V cval env φ (d + 1) (updV V ρ d x)
        (body.instantiate1 (.fvar d n ty)) xs d' ρ' rest →
      TeleFit V cval env φ d ρ (.forallE n ty body m) (x :: xs) d' ρ' rest


/-- Values fitting a `∀`-telescope along an *expression* spine: each
argument expression interprets to a member of the corresponding domain,
and the telescope is instantiated one argument at a time (mirroring the
iota certificates' walk).  The last index is the fully instantiated
residual body. -/
inductive TeleFitI (V : Type u) [SetTheory V] (cval : ConstVal V)
    (env : Env) (φ : Name → Nat)
    (d : Nat) (ρ : Nat → V) : Expr → List Expr → List V → Expr → Prop
  | nil {e} : TeleFitI V cval env φ d ρ e [] [] e
  | cons {n ty body m arg args x xs A rest} :
      interpExpr V cval env φ d ρ ty = some A →
      interpExpr V cval env φ d ρ arg = some x →
      x ∈ˢ A →
      Expr.fvarsBelow d body →
      Expr.WScoped d arg →
      arg.looseBVarsBounded 0 = true →
      AnnotOk V cval env φ d ρ arg →
      TeleFitI V cval env φ d ρ (body.instantiate1 arg) args xs rest →
      TeleFitI V cval env φ d ρ (.forallE n ty body m) (arg :: args) (x :: xs)
        rest


/-- Fold facts for every stored recursor rule: the recursor's value
applied through its argument spine (`args`, then the major `tv`), with
the major a constructor-value spine, equals the interpreted rule rhs
applied to the non-index prefix and the constructor's fields — together
with the typing slots the reduct's annotation chain needs, and the
rhs's own annotation truthfulness.  Basis blocks discharge this from
the hand-written values; modeled blocks will discharge it from their
checked `_model` theorems. -/
def RecRulesOk (env : Env) (val : ConstVal V) : Prop :=
  ∀ n cv nP nM nm ni rules,
    env.find? n = some (.recInfo cv nP nM nm ni rules) →
    ∀ r ∈ rules,
      (∀ ψ : Name → Nat, AnnotOk V val env ψ 0 (rho0 V) (RecRule.rhs r)) ∧
      ∀ cvj cnP cnF,
        env.find? (RecRule.ctor r) = some (.ctorInfo cvj cnP cnF) →
        ∀ (ψ ψj : Name → Nat) (args margs : List V) (tv : V),
          args.length = nP + nM + nm + ni →
          margs.length = cnP + cnF →
          ChainSlots V (val n ψ) (args ++ [tv]) →
          ChainSlots V (val (RecRule.ctor r) ψj) margs →
          tv = SpineFold V (val (RecRule.ctor r) ψj) margs →
          margs.take cnP = (args ++ [tv]).take cnP →
          (∀ p ∈ cvj.levelParams, ψj p = ψ p) →
          (∃ (φ' : Name → Nat) (us usj : List Level) (d : Nat) (ρ : Nat → V)
              (d₁ : Nat) (ρ₁ : Nat → V) (rest₁ : Expr)
              (d₂ : Nat) (ρ₂ : Nat → V) (rest₂ : Expr),
            ψ = Level.substFn φ' cv.levelParams us ∧
            ψj = Level.substFn φ' cvj.levelParams usj ∧
            TeleFit V val env φ' d ρ
              (cv.type.instantiateLevelParams cv.levelParams us)
              (args ++ [tv]) d₁ ρ₁ rest₁ ∧
            TeleFit V val env φ' d₁ ρ₁
              (cvj.type.instantiateLevelParams cvj.levelParams usj)
              margs d₂ ρ₂ rest₂) →
          ∃ R, interpClosed V val env ψ (RecRule.rhs r) = some R ∧
            SpineFold V (val n ψ) (args ++ [tv]) =
              SpineFold V R (args.take (nP + nM + nm) ++ margs.drop cnP) ∧
            ChainSlots V R (args.take (nP + nM + nm) ++ margs.drop cnP)

theorem RecRulesOk.empty (val : ConstVal V) :
    RecRulesOk V Env.empty val := by
  intro n cv nP nM nm ni rules h
  simp [Env.find?, Env.empty] at h

/-- Modeled-install bookkeeping: every *non-reserved* stored inductive
type former or constructor carries its `_model` companion's value (and
that companion is stored), and every installed projection function its
`_model.proj_j`'s.  Only the inductive-declaration install path
creates such constants, so these value bridges hold globally; the
capability rules' soundness consumes them. -/
def ModeledOk (env : Env) (val : ConstVal V) : Prop :=
  (∀ n cv caps, env.find? n = some (.indInfo cv caps) →
    reservedBasisNames.contains n = false →
    (env.find? (n.str "_model")).isSome = true ∧
    ∀ ψ : Name → Nat, val n ψ = val (n.str "_model") ψ) ∧
  (∀ n cv cnP cnF, env.find? n = some (.ctorInfo cv cnP cnF) →
    reservedBasisNames.contains n = false →
    (env.find? (n.str "_model")).isSome = true ∧
    ∀ ψ : Name → Nat, val n ψ = val (n.str "_model") ψ) ∧
  (∀ (T : Name) (j : Nat) (ci : ConstantInfo),
    env.find? (projFnName T j) = some ci →
    (env.find? (projModelName T j)).isSome = true ∧
    ∀ ψ : Name → Nat,
      val (projFnName T j) ψ = val (projModelName T j) ψ)

omit [SetTheory V] in
theorem ModeledOk.empty (val : ConstVal V) : ModeledOk V Env.empty val := by
  refine ⟨?_, ?_, ?_⟩
  · intro n cv caps h
    simp [Env.find?, Env.empty] at h
  · intro n cv cnP cnF h
    simp [Env.find?, Env.empty] at h
  · intro T j ci h
    simp [Env.find?, Env.empty] at h

/-- A model of an environment: a set-theoretic value for every constant
(a function of the level-parameter assignment), such that

* the environment is syntactically well-formed,
* each constant's value only reads its own level parameters,
* each constant is a member of the interpretation of its type, and
* each definition's value equals the interpretation of its body.

Not a degenerate condition: `interpExpr` is undefined outside the
supported fragment, so an environment using unsupported constructs
provably has no `EnvModel`. -/
structure EnvModel (env : Env) where
  /-- The interpretation of each constant. -/
  val : ConstVal V
  /-- Stored declarations are syntactically well-formed. -/
  wf : EnvWF env
  /-- A constant's value only depends on its own level parameters. -/
  val_params : ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      val n φ₁ = val n φ₂
  /-- Every constant is a member of (the interpretation of) its type. -/
  mem_type : ∀ c ∈ env.consts, ∀ φ : Name → Nat,
    ∃ t, interpClosed V val env φ c.toConstantVal.type = some t ∧ val c.name φ ∈ˢ t
  /-- Every definition is interpreted by its body. -/
  defn_eq : ∀ cv value, ConstantInfo.defnInfo cv value ∈ env.consts → ∀ φ : Name → Nat,
    interpClosed V val env φ value = some (val cv.name φ)
  /-- Stored types (and definition bodies) carry truthful annotations. -/
  annot_ok : ∀ c ∈ env.consts, ∀ φ : Name → Nat,
    AnnotOk V val env φ 0 (rho0 V) c.toConstantVal.type ∧
    ∀ cv value, c = ConstantInfo.defnInfo cv value →
      AnnotOk V val env φ 0 (rho0 V) value
  /-- Every stored inductive-kind constant has a model: the semantic
  facts the checker rules consume (`IndOk`), independent of the
  concrete construction that realizes them. -/
  ind_ok : IndOk V env val
  /-- Every stored recursor rule has a verified fold equation. -/
  rec_rules : RecRulesOk V env val
  /-- Non-reserved inductive-kind constants carry their model values. -/
  modeled_ok : ModeledOk V env val

/-- The empty environment has a (trivial) model. -/
def EnvModel.empty : EnvModel V Env.empty where
  val := fun _ _ => SetTheory.empty
  wf := by intro c hc; cases hc
  val_params := by
    intro n ci h
    simp [Env.find?, Env.empty] at h
  mem_type := by intro c hc; cases hc
  defn_eq := by intro cv value h; cases h
  annot_ok := by intro c hc; cases hc
  ind_ok := IndOk.empty V _ (fun _ x hx => SetTheory.not_mem_empty x hx)
  rec_rules := RecRulesOk.empty V _
  modeled_ok := ModeledOk.empty V _

end Setlec
