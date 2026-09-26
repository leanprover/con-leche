module

public import ConLeche.Model.IndTowerRead
public section

/-!
# The reduct stage, at the reading (task #161, IND TIER part 5)

The checked statement's right-hand side, read at the fired chain,
**is** the rule's own right-hand side applied to the fired spine.  The
recorded rhs run fires at the full frame, the applied form's head runs
back to the closed rule reading (renaming, then
`denoteMeta_depth_of_closed`), and the opener spine reads off the chain.

`DefEqClaim` converts the rhs run only against *both* comparands'
gradings.  The a-side is the statement's own right-hand side, graded
through `InferClaim`; the b-side is the *applied form*, whose grading
enters as the premise `hokApp`, in the `∀ ba` form the reading's
existence is derived in.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → AnnotTerm}

/-- The forward direction of `denoteMeta_mkAppN_inv`. -/
theorem denoteMeta_mkAppN_of {d : Nat} :
    ∀ (as : List Expr) {e : Expr} {ea : AnnotTerm} {vs : List AnnotTerm},
      denoteMeta acval env φ d e = some ea →
      DenoteMetaSpine acval env φ d as vs →
      denoteMeta acval env φ d (Expr.mkAppN e as)
        = some (AnnotTerm.mkAppN ea vs) := by
  intro as
  induction as with
  | nil =>
    intro e ea vs he hsp
    cases hsp
    exact he
  | cons a as ih =>
    intro e ea vs he hsp
    cases hsp with
    | @cons _ v _ vs' ha hsp' =>
      have hstep : denoteMeta acval env φ d (.app e a) = some (.app ea v) := by
        rw [denoteMeta_app, he, ha]
        rfl
      exact ih (ea := .app ea v) hstep hsp'

end ConLeche.Model
