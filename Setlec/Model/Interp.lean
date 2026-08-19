import Setlec.Kernel.TypeChecker
import Setlec.SetTheory.Basic
import Setlec.Verify.Level
import Setlec.Verify.Shift
import Setlec.Verify.EnvWF
import Setlec.Verify.Leaves

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

/-- The type of constant valuations. -/
abbrev ConstVal (V : Type u) := Name → (Name → Nat) → V

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
  | _, _, _ => none
termination_by _ _ e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

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
  | d, ρ, .lam n ty body _ =>
    AnnotOk cval env φ d ρ ty ∧
    ∀ x A, interpExpr V cval env φ d ρ ty = some A → x ∈ˢ A →
      AnnotOk cval env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty))
  | d, ρ, .app f a => AnnotOk cval env φ d ρ f ∧ AnnotOk cval env φ d ρ a
  | _, _, _ => True
termination_by d ρ e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

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

end Setlec
