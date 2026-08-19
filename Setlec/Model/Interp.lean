import Setlec.Kernel.TypeChecker
import Setlec.SetTheory.Basic
import Setlec.Verify.Level
import Setlec.Verify.Shift
import Setlec.Verify.EnvWF

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
the domain; the codomain's (evaluated) sort level, which `pi` needs to
decide the Prop/Type split, is computed by `sortLevelOf` using the
checker's own `inferType`.

`FvarsOk` states the typing assumptions about the (implicit) local
context.  `EnvModel` packages a model of a whole environment.
-/

namespace Setlec

variable (V : Type u) [SetTheory V]

open SetTheory

/-- The evaluated sort level of the *type* of `e` — the Prop/Type
classifier for `SetTheory.pi`.  Computed with the checker's own inference;
`none` when inference fails (then nothing is interpreted anyway). -/
def sortLevelOf (env : Env) (φ : Name → Nat) (depth : Nat) (e : Expr) : Option Nat :=
  match inferType env depth e >>= ensureSort env with
  | .ok u => some (u.eval φ)
  | .error _ => none

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
  | d, ρ, .forallE n ty body _ =>
    match interpExpr cval env φ d ρ ty with
    | none => none
    | some A =>
      let body' := body.instantiate1 (.fvar d n ty)
      match sortLevelOf env φ (d + 1) body' with
      | none => none
      | some vE => some (pi vE A fun x =>
          (interpExpr cval env φ (d + 1) (updV V ρ d x) body').getD SetTheory.empty)
  | _, _, _ => none
termination_by _ _ e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- The typing assumptions about the implicit local context: every
reachable free variable is valued inside (the interpretation of) its
annotated type, and the annotations themselves satisfy the same
assumptions. -/
def FvarsOk (cval : ConstVal V) (env : Env) (φ : Name → Nat) (d : Nat) (ρ : Nat → V) :
    Expr → Prop
  | .fvar idx _ ty => idx < d ∧ FvarsOk cval env φ d ρ ty ∧
      ∃ T, interpExpr V cval env φ d ρ ty = some T ∧ ρ idx ∈ˢ T
  | .app f a => FvarsOk cval env φ d ρ f ∧ FvarsOk cval env φ d ρ a
  | .lam _ ty body _ | .forallE _ ty body _ =>
      FvarsOk cval env φ d ρ ty ∧ FvarsOk cval env φ d ρ body
  | .letE _ ty val body =>
      FvarsOk cval env φ d ρ ty ∧ FvarsOk cval env φ d ρ val ∧ FvarsOk cval env φ d ρ body
  | .proj _ _ e => FvarsOk cval env φ d ρ e
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

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

/-- The empty environment has a (trivial) model. -/
def EnvModel.empty : EnvModel V Env.empty where
  val := fun _ _ => SetTheory.empty
  wf := by intro c hc; cases hc
  val_params := by
    intro n ci h
    simp [Env.find?, Env.empty] at h
  mem_type := by intro c hc; cases hc
  defn_eq := by intro cv value h; cases h

end Setlec
