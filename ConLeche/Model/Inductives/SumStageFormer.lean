module

public import ConLeche.Model.Inductives.SumData
import ConLeche.Verify.Inductives.SumWF
public section

/-!
# The sum former's cons (task #175 sum-types, indexed)

`stageSumFormer`: the P step at the sum's type former, for a given
list of field chains `Fss` (one per constructor, scoped at the
parameter-and-index frame — the restricted chains `rChains` at an
indexed family) — `stageFormer` with the sum leaf `sumTyAV`
and the per-constructor grading `SumFieldsOkB`.  The former is stored
with the empty capability record, so the block's own capability laws
are vacuous.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps InductiveShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The sum former leaf's two hereditary premises**, from the former's
data and the chains' grading at the parameter frame. -/
theorem formerWalksS {m : EnvModel V env} {cvT : ConstantVal} {nP : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AnnotTerm)}
    (hFD : FormerData m cvT nP resSort pps)
    {Fss : (Name → Nat) → List (List AnnotTerm)}
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat V ((pps ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ParamsOkS (resSort.eval ψ) ρ (Fss ψ) (pps ψ) ∧
      UnderTowerValid ρ (sumBodyAV (resSort.eval ψ) (Fss ψ)) (pps ψ) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleAV_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleAV_graded (V := V) htele (Δ₀ := [])
    (fun ρ _ => hFD.okTy ψ ρ)
  simp only [List.append_nil] at okΓ
  have hlenΓ : (((pps ψ).map (·.2.2)).reverse).length = nP := by
    simp [hFD.len ψ]
  have hent : ∀ i, i < nP → ∃ p, (pps ψ)[i]? = some p ∧
      p.2.2 = (((pps ψ).map (·.2.2)).reverse).getD (nP - 1 - i) default := by
    intro i hi
    have hil : i < (pps ψ).length := by rw [hFD.len ψ]; exact hi
    refine ⟨(pps ψ)[i], List.getElem?_eq_getElem hil, ?_⟩
    rw [getD_reverse_of_peel (hFD.len ψ) hi (List.getElem?_eq_getElem hil)]
  have hΓnil : (((pps ψ).map (·.2.2)).reverse).drop (nP - 0) = [] := by
    rw [Nat.sub_zero, List.drop_eq_nil_of_le (by rw [hlenΓ]; exact Nat.le_refl _)]
  constructor
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => ParamsOkS (resSort.eval ψ) ρ (Fss ψ) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => (hFssOk ψ ρ hρ).1)
      (fun ρ d ds hd hok hrec => ⟨hFD.bits ψ d hd, hok.1, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ (sumBodyAV (resSort.eval ψ) (Fss ψ)) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => sumBodyAV_validV (hFssOk ψ ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat_nil V ρ)
    simpa using hw

end ConLeche.Model
