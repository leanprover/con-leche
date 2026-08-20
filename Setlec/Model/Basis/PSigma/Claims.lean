import Setlec.Model.Basis.PSigma.AnnotOk
import Setlec.Model.Basis.Glue

/-!
# Claims glue for the `PSigma'.rec` rule
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {ψ : Name → Nat}
open SetTheory Expr

/-- Claims glue for the `PSigma'.rec` rule (Prop-valued motive: both
sides of the fold are the proof point, for any major value). -/
theorem psigmaIota_claims {cval : ConstVal V}
    (hfindS : env.find? psigmaName = some psigmaA)
    (hvalS : ∀ ψ' : Name → Nat, cval psigmaName ψ' = psigmaVal V ψ')
    (hfindM : env.find? psigmaMkName = some psigmaMkA)
    (hvalM : ∀ ψ' : Name → Nat, cval psigmaMkName ψ' = psigmaMkVal V ψ')
    {Av Bv Mv mkv tv av bv : V} {S1 S2 S3 S4 S5 S6 : V}
    (hAv : Av ∈ˢ S1) (hBv : Bv ∈ˢ S2) (hMv : Mv ∈ˢ S3)
    (hmkv : mkv ∈ˢ S4) (hav : av ∈ˢ S5) (hbv : bv ∈ˢ S6) :
    ∃ R, interpClosed V cval env ψ psigmaRecRhsA = some R ∧
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (psigmaRecVal V ψ) Av) Bv) Mv) mkv) tv =
      SetTheory.app (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app R Av) Bv) Mv) mkv) av) bv ∧
      AppSlot (V := V) R Av ∧
      AppSlot (V := V) (SetTheory.app R Av) Bv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app R Av) Bv) Mv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app R Av)
        Bv) Mv) mkv ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app R Av) Bv) Mv) mkv) av ∧
      AppSlot (V := V) (SetTheory.app (SetTheory.app (SetTheory.app
        (SetTheory.app (SetTheory.app R Av) Bv) Mv) mkv) av) bv := by
  refine ⟨_, interp_psigmaRec_rhs hfindS hvalS hfindM hvalM, ?_⟩
  have hRpt : (SetTheory.lam 0 (univ (ψ uN)) fun A =>
      SetTheory.lam 0 (pi (ψ vN + 1) A fun _ => univ (ψ vN)) fun B =>
        SetTheory.lam 0
          (pi 1 (SetTheory.app (SetTheory.app (psigmaVal V ψ) A) B)
            fun _ => univ 0) fun M =>
          SetTheory.lam 0
            (pi 0 A fun a => pi 0 (SetTheory.app B a) fun b =>
              SetTheory.app M
                (SetTheory.app (SetTheory.app (SetTheory.app
                  (SetTheory.app (psigmaMkVal V ψ) A) B) a) b)) fun mk =>
            SetTheory.lam 0 A fun a =>
              SetTheory.lam 0 (SetTheory.app B a) fun b =>
                SetTheory.app (SetTheory.app mk a) b) = (pt : V) := lam_zero
  have hrec_pt : (psigmaRecVal V ψ : V) = pt := by
    simp only [psigmaRecVal]; exact lam_zero
  rw [hRpt, hrec_pt]
  simp only [app_pt]
  exact ⟨trivial,
    ⟨0, S1, fun _ => unitSet, pt_mem_pi_unit (V := V), hAv,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S2, fun _ => unitSet, pt_mem_pi_unit (V := V), hBv,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S3, fun _ => unitSet, pt_mem_pi_unit (V := V), hMv,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S4, fun _ => unitSet, pt_mem_pi_unit (V := V), hmkv,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S5, fun _ => unitSet, pt_mem_pi_unit (V := V), hav,
      fun _ _ => unitSet_mem_univ 0⟩,
    ⟨0, S6, fun _ => unitSet, pt_mem_pi_unit (V := V), hbv,
      fun _ _ => unitSet_mem_univ 0⟩⟩

end Setlec
