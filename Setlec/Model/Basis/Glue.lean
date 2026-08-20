import Setlec.Model.BasisInstall

/-!
# Claims-side glue helpers

Per rule, the claims lemmas (in the per-type `Claims` modules) package
exactly what the `whnfCore` iota-branch soundness needs; these are their
shared membership helpers.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-! ## Claims-side glue

Per rule, one lemma packaging exactly what the `whnfCore` iota-branch
soundness needs: the rule-rhs interpretation, the fold equation, and the
membership facts that let the reduct's `AnnotOk` app-chain be
reassembled.  The membership hypotheses are the ∃-witnesses of the
*original* application chain's `AnnotOk`; canonical domains are
recovered with `lam_dom` away from the Prop collapse, and under the
collapse everything is the proof point. -/

/-- Away from `pi 0`, an abstraction's membership transfers elements of
the pi's domain into its own. -/
theorem lam_dom_of_ne {w vE : Nat} {D A : V} {F : V → V} {B : V → V}
    (h : SetTheory.lam w D F ∈ˢ pi vE A B) (hw : w ≠ 0) :
    ∀ x, x ∈ˢ A → x ∈ˢ D := by
  by_cases hvE : vE = 0
  · subst hvE
    exact absurd (mem_pi_zero h) (lam_ne_pt hw)
  · exact lam_dom h hvE hw

/-- The proof point inhabits every trivial Prop-pi. -/
theorem pt_mem_pi_unit {A : V} : (pt : V) ∈ˢ pi 0 A fun _ => unitSet := by
  have := lam_mem (V := V) (v := 0) (A := A) (F := fun _ => pt)
    (B := fun _ => unitSet) (fun _ _ => pt_mem_unitSet)
  rw [lam_zero] at this
  exact this

end Setlec
