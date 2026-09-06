import Setlec.SetP.DirectSum.SumDataP
import Setlec.Verify.Direct.SumWF

/-!
# The sum former's cons (task #175 sum-types)

`stageSumFormer`: the P step at the sum's type former, for a given
list of field chains `Fss` (one per constructor, scoped at the
parameter frame) — `stageFormer` with the sum leaf `directSumTyAV`
and the per-constructor grading `SumFieldsOkB`.  The former is stored
with the empty capability record, so the block's own capability laws
are vacuous.
-/

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectSumParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env}

/-- **The sum former leaf's two hereditary premises**, from the former's
data and the chains' grading at the parameter frame. -/
theorem formerWalksS {m : EnvS2Core V env} {cvT : ConstantVal} {nP : Nat}
    {resSort : Level} {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData m cvT nP resSort pps)
    {Fss : (Name → Nat) → List (List AVExpr)}
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ))
    (ψ : Name → Nat) (ρ : Nat → V) :
    ParamsOkS (resSort.eval ψ) ρ (Fss ψ) (pps ψ) ∧
      UnderTowerValid ρ (sumBodyAV (resSort.eval ψ) (Fss ψ)) (pps ψ) := by
  have hst := stripPisAV_mkPisAV (pps ψ) (.sort (resSort.eval ψ))
  rw [hFD.len ψ] at hst
  have htele := piTeleP_of_stripPisAV hst
  obtain ⟨okΓ, -⟩ := piTeleP_graded (V := V) htele (Δ₀ := [])
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
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat2_nil V ρ)
    simpa using hw
  · have hw := hereditaryWalk (V := V)
      (Q := fun ρ ds => UnderTowerValid ρ (sumBodyAV (resSort.eval ψ) (Fss ψ)) ds)
      hlenΓ (hFD.len ψ) hent okΓ
      (fun ρ hρ => sumBodyAV_validV (hFssOk ψ ρ hρ).2)
      (fun ρ d ds hd hok hrec => ⟨hok.2, hrec⟩)
      0 (Nat.zero_le _) ρ (by rw [hΓnil]; exact Sat2_nil V ρ)
    simpa using hw

/-- **The P step at the sum former's cons**, for a given list of field
chains. -/
theorem stageSumFormer (mp : EnvS2PM V μ env)
    (hE₀ : Setlec.EtaFamiliesClosed env)
    {F : Nat} {p : DirectSumParts} {envI : Env} {cvTa : ConstantVal}
    (hind : Setlec.checkDirectSumInd (Setlec.fueledOps μ F) env p = .ok (envI, cvTa))
    {pps : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (Fss : (Name → Nat) → List (List AVExpr))
    (hFssParams : ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ cvTa.levelParams, ψ₁ q = ψ₂ q) → Fss ψ₁ = Fss ψ₂)
    (hFssBelow : ∀ ψ : Name → Nat, ∀ Fs ∈ Fss ψ, FieldsBelow p.nP Fs)
    (hFssOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ →
      SumFieldsOkB (p.resSort.eval ψ) ρ (Fss ψ) ∧ SumFieldsValid ρ (Fss ψ)) :
    ∃ mp' : EnvS2PM V μ envI,
      mp'.base2.acval = acvalWith mp.base2.acval cvTa.name
        (fun ψ => directSumTyAV (p.resSort.eval ψ) (pps ψ) (Fss ψ)) := by
  obtain ⟨hccv, rfl, -⟩ := Setlec.checkDirectSumInd_shape hind
  obtain ⟨hfind, hnres, hpshape, -, -, -, type', -, -, -, -, htr', -, -, hty⟩ :=
    Setlec.checkConstantVal_inv hccv
  have hname : cvTa.name = p.cvT.name := by rw [hty]
  have hfresh : env.find? cvTa.name = none := by
    rw [hname]; exact hfind
  have htr : cvTa.type.constsResolve env = true := by rw [hty]; exact htr'
  have hcb : ConstsBound env cvTa.type := constsBound_of_constsResolve _ htr
  obtain ⟨hwfI, -⟩ := Setlec.direct_sum_ind_wf mp.base2.wf hind
  let A : (Name → Nat) → AVExpr :=
    fun ψ => directSumTyAV (p.resSort.eval ψ) (pps ψ) (Fss ψ)
  have hAbelow : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase := fun ψ =>
    directSumTyAV_below (hFD.below ψ)
      (by rw [hFD.len ψ, Nat.zero_add]; exact hFssBelow ψ)
  have hwalks := formerWalksS hFD hFssOk
  have hreadI : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval cvTa.name A)
        ⟨.indInfo cvTa {} :: env.consts⟩ ψ 0 cvTa.type
        = some (mkPisAV (pps ψ) (.sort (p.resSort.eval ψ))) := fun ψ =>
    denoteP_cons_mono (c₀ := .indInfo cvTa {}) hfresh
      (ConsCrossAt.ofNtc fun _ h => nomatch h) ψ 0 hcb (hFD.read ψ)
  have hnresI : Setlec.reservedBasisNames.contains
      (ConstantInfo.indInfo cvTa {}).name = false := by
    show Setlec.reservedBasisNames.contains cvTa.name = false
    rw [hname]; exact hnres
  have hpshapeI : (ConstantInfo.indInfo cvTa {}).name.isProjFnShape = false := by
    show cvTa.name.isProjFnShape = false
    rw [hname]; exact hpshape
  refine declStepPM_of_ind_member_cons mp (c₀ := .indInfo cvTa {})
    (A := A) hfresh hnresI (Or.inl ⟨_, _, rfl⟩)
    (ConsHeadP.ofFresh hwfI (fun ψ => hAbelow ψ) hnresI
      (fun _ h => nomatch h)
      (fun _ _ _ _ h => nomatch h))
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · intro ψ₁ ψ₂ hφ
    obtain ⟨hp, hw⟩ := hFD.params ψ₁ ψ₂ hφ
    show directSumTyAV _ _ _ = directSumTyAV _ _ _
    rw [hp, hw, hFssParams ψ₁ ψ₂ hφ]
  · exact fun ψ ρ => directSumTyAV_ok2 (hwalks ψ ρ).1
  · exact fun ψ ρ => (directSumTyAV_okP (hwalks ψ ρ).1 (hwalks ψ ρ).2).2
  · exact fun ψ => ⟨_, hreadI ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact hFD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadI ψ).symm.trans hta)
    exact directSumTyAV_mem (hwalks ψ ρ).1
  · -- `caps_ok`: the prefix families cross; the block's own family
    -- claims nothing (the empty capability record)
    intro m₂ hac
    refine capsOkP_cons_direct mp (c₀ := .indInfo cvTa {})
      (A := A) (T := cvTa.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeI
      (Or.inl ⟨cvTa, {}, rfl, rfl⟩)
      (fun T' cvT' caps' hf _ hres hcape => hE₀ T' cvT' caps' hf hcape hres)
      m₂ hac ?_
    intro cvT caps hf _
    have hself := Setlec.Env.find?_cons_self (ConstantInfo.indInfo cvTa {}) env
    obtain ⟨rfl, rfl⟩ :=
      ConstantInfo.indInfo.inj (Option.some.inj (hself.symm.trans hf))
    exact ⟨fun he => absurd he Bool.false_ne_true, fun hu => absurd hu Bool.false_ne_true⟩

end Setlec.SetP
