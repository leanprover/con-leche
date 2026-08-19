import Setlec.Kernel.TypeChecker
import Setlec.SetTheory.Basic
import Setlec.Verify.Level
import Setlec.Verify.Shift

/-!
# Interpretation of expressions in the set model

`interpExpr env φ d ρ e` maps a kernel expression to an element of the
set-theoretic universe `V`, where

* `φ` assigns the universe level parameters,
* `d` is the current binder depth,
* `ρ : Nat → V` values the free variables (`fvar idx …` ↦ `ρ idx`; the
  annotation at an `fvar` leaf is *not* read — an `fvar`'s meaning is its
  valuation).

It is partial (`Option`): unsupported expression forms are uninterpreted,
and it grows in lockstep with the checker.

A `∀`-type is interpreted by opening the binder at index `d` — exactly as
the checker does — and forming the dependent product `SetTheory.pi` over
the domain.  The codomain's (evaluated) sort level, which `pi` needs to
decide the Prop/Type split, is computed by `sortLevelOf` using the
checker's own `inferType`; the verification only ever cares about
interpretations of expressions the checker has successfully inferred, for
which this computation succeeds and agrees with the checker's.

`FvarsOk` states the typing assumptions about the (implicit) local
context: each free variable's valuation is a member of its annotated
type's interpretation.  These are the hypotheses of the soundness
theorems, maintained when the checker opens a binder.

`EnvModel` packages a model of a whole (closed) environment.
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

/-- Interpret an expression under level assignment `φ`, binder depth `d`
and free-variable valuation `ρ`. -/
def interpExpr (env : Env) (φ : Name → Nat) : (d : Nat) → (ρ : Nat → V) → Expr → Option V
  | _, _, .sort u => some (univ (u.eval φ))
  | _, ρ, .fvar idx _ _ => some (ρ idx)
  | d, ρ, .forallE n ty body _ =>
    match interpExpr env φ d ρ ty with
    | none => none
    | some A =>
      let body' := body.instantiate1 (.fvar d n ty)
      match sortLevelOf env φ (d + 1) body' with
      | none => none
      | some vE => some (pi vE A fun x =>
          (interpExpr env φ (d + 1) (updV V ρ d x) body').getD SetTheory.empty)
  | _, _, _ => none
termination_by _ _ e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- The typing assumptions about the implicit local context: every
reachable free variable is valued inside (the interpretation of) its
annotated type, and the annotations themselves satisfy the same
assumptions. -/
def FvarsOk (env : Env) (φ : Name → Nat) (d : Nat) (ρ : Nat → V) : Expr → Prop
  | .fvar idx _ ty => idx < d ∧ FvarsOk env φ d ρ ty ∧
      ∃ T, interpExpr V env φ d ρ ty = some T ∧ ρ idx ∈ˢ T
  | .app f a => FvarsOk env φ d ρ f ∧ FvarsOk env φ d ρ a
  | .lam _ ty body _ | .forallE _ ty body _ =>
      FvarsOk env φ d ρ ty ∧ FvarsOk env φ d ρ body
  | .letE _ ty val body =>
      FvarsOk env φ d ρ ty ∧ FvarsOk env φ d ρ val ∧ FvarsOk env φ d ρ body
  | .proj _ _ e => FvarsOk env φ d ρ e
  | _ => True
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- The canonical valuation for closed terms. -/
def rho0 : Nat → V := fun _ => SetTheory.empty

/-- Interpretation of a closed expression (as they appear in declarations). -/
def interpClosed (env : Env) (φ : Name → Nat) (e : Expr) : Option V :=
  interpExpr V env φ 0 (rho0 V) e

/-- A model of an environment: a set-theoretic value for every constant
(a function of the level-parameter assignment), such that

* each constant is a member of the interpretation of its type, and
* each definition's value equals the interpretation of its body.

Not a degenerate condition: `interpExpr` is undefined outside the
supported fragment, so an environment using unsupported constructs
provably has no `EnvModel`. -/
structure EnvModel (env : Env) where
  /-- The interpretation of each constant. -/
  val : Name → (Name → Nat) → V
  /-- Every constant is a member of (the interpretation of) its type. -/
  mem_type : ∀ c ∈ env.consts, ∀ φ,
    ∃ t, interpClosed V env φ c.type = some t ∧ val c.name φ ∈ˢ t
  /-- Every definition is interpreted by its body. -/
  defn_eq : ∀ cv value, ConstantInfo.defnInfo cv value ∈ env.consts → ∀ φ,
    interpClosed V env φ value = some (val cv.name φ)

/-- The empty environment has a (trivial) model. -/
def EnvModel.empty : EnvModel V Env.empty where
  val := fun _ _ => SetTheory.empty
  mem_type := by intro c hc; cases hc
  defn_eq := by intro cv value h; cases h

end Setlec
