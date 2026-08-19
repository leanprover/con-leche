import Setlec.Kernel.Env
import Setlec.SetTheory.Basic
import Setlec.Verify.Level

/-!
# Interpretation of expressions in the set model

`interpExpr` maps (closed, well-typed) kernel expressions to elements of the
set-theoretic universe `V`, relative to an assignment `φ` of the universe
level parameters.  It is partial (`Option`): expression forms the checker
does not support yet are uninterpreted.  It grows in lockstep with the
checker — the invariant maintained across iterations is that everything the
checker *accepts* is interpreted.

`EnvModel` packages a model of a whole environment: a (level-polymorphic)
value for every constant, member of its type's interpretation, and for
definitions equal to the interpretation of the body (which will justify
delta unfolding).
-/

namespace Setlec

variable (V : Type u) [SetTheory V]

open SetTheory

/-- Interpret an expression as an element of `V` under the level-parameter
assignment `φ`, if the expression is in the supported fragment. -/
def interpExpr (φ : Name → Nat) : Expr → Option V
  | .sort u => some (univ (u.eval φ))
  | _ => none

/-- A model of an environment: a set-theoretic value for every constant
(a function of the level-parameter assignment), such that

* each constant is a member of the interpretation of its type, and
* each definition's value equals the interpretation of its body.

Note this is not a degenerate condition: `interpExpr` is undefined outside
the supported fragment, so an environment mentioning unsupported constructs
provably has no `EnvModel`. -/
structure EnvModel (env : Env) where
  /-- The interpretation of each constant. -/
  val : Name → (Name → Nat) → V
  /-- Every constant is a member of (the interpretation of) its type. -/
  mem_type : ∀ c ∈ env.consts, ∀ φ,
    ∃ t, interpExpr V φ c.type = some t ∧ val c.name φ ∈ˢ t
  /-- Every definition is interpreted by its body. -/
  defn_eq : ∀ cv value, ConstantInfo.defnInfo cv value ∈ env.consts → ∀ φ,
    interpExpr V φ value = some (val cv.name φ)

/-- The empty environment has a (trivial) model. -/
def EnvModel.empty : EnvModel V Env.empty where
  val := fun _ _ => SetTheory.empty
  mem_type := by intro c hc; cases hc
  defn_eq := by intro cv value h; cases h

end Setlec
