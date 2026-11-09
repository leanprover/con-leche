module

public import ConLeche.Model.IndTowerRead
public section

/-!
# The reduct stage, at the reading (task #161, IND TIER part 5)

The checked statement's right-hand side, read at the fired chain,
**is** the rule's own right-hand side applied to the fired spine.  The
recorded rhs run fires at the full frame, the applied form's head runs
back to the closed rule reading (renaming, then
`denote_depth_of_closed`), and the opener spine reads off the chain.

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

open ConLeche (CheckMode Env Expr Name Level isDefEqCore)

universe w

variable {V : Type w} [SetTheory V]
variable {env : Env} {φ : Name → Nat}
variable {acval : Name → (Name → Nat) → Term}

/-- The forward direction of `denote_mkAppN_inv`. -/
theorem denote_mkAppN_of {d : Nat} :
    ∀ (as : List Expr) {e : Expr} {ea : Term} {vs : List Term},
      denote acval env φ d e = some ea →
      DenoteSpine acval env φ d as vs →
      denote acval env φ d (Expr.mkAppN e as)
        = some (Term.mkAppN ea vs) := by
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
      have hstep : denote acval env φ d (.app e a) = some (.app ea v) := by
        rw [denote_app, he, ha]
        rfl
      exact ih (ea := .app ea v) hstep hsp'

end ConLeche.Model
