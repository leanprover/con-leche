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

/-- A non-collapsed abstraction's membership transfers elements of the
pi's domain into its own (task #100: the nonzero-tag premise becomes a
non-`pt` premise — under the collapse, tags no longer bound values away
from `pt`; consumers certify non-collapse per value, usually by
`lamC_ne_pt_of_witness`). -/
theorem lam_dom_of_ne {w vE : Nat} {D A : V} {F : V → V} {B : V → V}
    (h : SetTheory.lam w D F ∈ˢ pi vE A B)
    (hne : SetTheory.lam w D F ≠ pt) :
    ∀ x, x ∈ˢ A → x ∈ˢ D :=
  lamC_dom_of_ne hne h

/-- The proof point inhabits every trivial Prop-pi. -/
theorem pt_mem_pi_unit {A : V} : (pt : V) ∈ˢ pi 0 A fun _ => unitSet :=
  pt_mem_piC_iff.mpr fun _ _ => pt_mem_unitSet

end Setlec
