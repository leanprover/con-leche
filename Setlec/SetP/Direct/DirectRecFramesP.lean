import Setlec.SetP.Direct.DirectRecMinorP

/-!
# The recursor's frames (task #175 W4c, P3 module 6, part 13)

`recFrames`: from the three constants' data at the environment holding
the former and the constructor, and the recursor stage's runs, the
recursor's parameter frame is the constructor's, and at every
parameter valuation the post-parameter phase facts hold — `RecBase`:
the field chain graded, the motive binder the Π over the carrier into
the elimination sort (`recMotive`), the minor binder the minor space
(`recMinor`), the major binder the carrier (`recMajor`).
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The recursor's reversed context above its three special binders is
its reversed parameter context. -/
theorem drop_three_rec {rds : List (Nat × Nat × AVExpr)} {nP : Nat}
    (hlen : rds.length = nP + 3) :
    ((rds.map (·.2.2)).reverse).drop 3 = (((rds.take nP).map (·.2.2)).reverse) := by
  rw [reverse_map_take_drop rds nP, List.drop_left' (by simp [hlen])]

/-- An entry of the recursor's context by its binder position. -/
theorem rec_entry {rds : List (Nat × Nat × AVExpr)} {nP : Nat}
    (hlen : rds.length = nP + 3) {i : Nat} (hi : i < nP + 3) :
    ((rds.map (·.2.2)).reverse).getD (nP + 3 - 1 - i) default
      = (rds.getD i default).2.2 := by
  have hq : rds[i]? = some (rds.getD i default) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  exact getD_reverse_of_peel hlen hi hq

set_option maxHeartbeats 3200000 in
/-- **The recursor's frames.** -/
theorem recFrames (hμ : μ.verified = true) (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {caps : IndCaps}
    (hccv : Setlec.checkConstantVal (Setlec.fueledOps μ F) env p.cvR = .ok cvRa)
    (hRec : Setlec.checkDirectRecTy (Setlec.fueledOps μ F) env p cvTa cvCa cvRa
      = .ok ())
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa caps))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    {pps ds rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hCD : CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds)
    (hRD : RecData mp.base2 cvRa p.nP (elimLevel p) rds)
    (hleafT : ∀ ψ, mp.base2.acval p.cvT.name ψ
      = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hleafC : ∀ ψ, mp.base2.acval p.cvC.name ψ
      = directMkAV (p.resSort.eval ψ) (ds ψ) (((ds ψ).drop p.nP).map (·.2.2)))
    (hiff : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((pps ψ).map (·.2.2)).reverse ρ ↔
        Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ)
    (hfields : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V (((ds ψ).take p.nP).map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ).drop p.nP).map (·.2.2)) ∧
        (p.isProp = false → FieldsBound (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))) ∧
        (p.isProp = true → p.large = true →
          FieldsBound 0 ρ (((ds ψ).drop p.nP).map (·.2.2)))) :
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((((rds ψ).take p.nP).map (·.2.2)).reverse) ρ ↔
        Sat2 V ((((ds ψ).take p.nP).map (·.2.2)).reverse) ρ) ∧
    (∀ (ψ : Name → Nat) (ρ : Nat → V),
      Sat2 V ((((rds ψ).take p.nP).map (·.2.2)).reverse) ρ →
        RecBase ((elimLevel p).eval ψ) (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))
          ((rds ψ).getD p.nP default) ((rds ψ).getD (p.nP + 1) default)
          ((rds ψ).getD (p.nP + 2) default)) := by
  -- the stage's shape
  obtain ⟨-, fvsP, rest, cdomsP, crest, mfv, mbs, mdom, minfv, xFvs, minBody, cdomsF,
    crest2, jbs, jbody, jdom, hopR, hci, hdomsP, hmfv, hmstrip, hmd, hmdeq, hminfv, hopX,
    hcf, hdomsF, hcrest2, hminBody, hjs, hjd, hjdeq, hjbody⟩ :=
    Setlec.checkDirectRecTy_shape hRec
  obtain ⟨-, -, -, -, hlbt, hitf, type', stype, u, hann', -, -, hst, hens, rfl⟩ :=
    Setlec.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hst hens hopR
  have hw0 : Expr.WScoped 0 type' := Expr.WScoped.of_not_hasFvar htf'
  -- the special variables
  obtain ⟨nmM, tyM, rfl⟩ := openPisAtFvars_index _ _ _ hopR p.nP mfv hmfv
  obtain ⟨nmm', tym, rfl⟩ := openPisAtFvars_index _ _ _ hopR (p.nP + 1) minfv hminfv
  rw [Nat.zero_add] at hmfv hminfv hminBody hopX
  obtain ⟨nmJ, jdom', mbJ, rfl, hjbs⟩ := stripPis_one_inv hjs
  obtain rfl : jdom = jdom' := by
    rw [hjbs] at hjd
    exact (Option.some.inj hjd).symm
  subst hjbody
  rw [Nat.zero_add] at hopR
  obtain ⟨nmm, mdom', mbm, hty, hmbs⟩ := stripPis_one_inv hmstrip
  simp only [Expr.fvarTypeD] at hty
  subst hty
  obtain rfl : mdom = mdom' := by
    rw [hmbs] at hmd
    exact (Option.some.inj hmd).symm
  have hlenP : fvsP.length = p.nP + 2 := openPisAtFvars_length _ hopR
  -- the full opening
  have hopAll : openPisAtFvars (p.nP + 3) type' 0
      = some (fvsP ++ [.fvar (p.nP + 2) nmJ jdom],
          .app (.fvar p.nP nmM (.forallE nmm mdom (.sort (elimLevel p)) mbm))
            (.fvar (p.nP + 2) nmJ jdom)) := by
    have := openPisAtFvars_add (p.nP + 2) hopR
      (openPisAtFvars_one nmJ jdom
        (.app (.fvar p.nP nmM (.forallE nmm mdom (.sort (elimLevel p)) mbm)) (.bvar 0)) mbJ
        (0 + (p.nP + 2)))
    rw [Nat.zero_add] at this
    simpa using this
  have hlenF : (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom]).length = p.nP + 3 := by
    simp [hlenP]
  have hidxR : ∀ (i : Nat) (x : Expr), (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom])[i]? = some x →
      ∃ nm ty, x = Expr.fvar i nm ty := by
    intro i x hx
    obtain ⟨nm, ty, h⟩ := openPisAtFvars_index _ _ _ hopAll i x hx
    exact ⟨nm, ty, by rw [h, Nat.zero_add]⟩
  have htakeR : (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom]).take p.nP = fvsP.take p.nP :=
    List.take_append_of_le_length (by omega)
  have hmfvR : (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom])[p.nP]?
      = some (.fvar p.nP nmM (.forallE nmm mdom (.sort (elimLevel p)) mbm)) := by
    rw [List.getElem?_append_left (by omega)]; exact hmfv
  have hminR : (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom])[p.nP + 1]?
      = some (.fvar (p.nP + 1) nmm' tym) := by
    rw [List.getElem?_append_left (by omega)]; exact hminfv
  have hjR : (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom])[p.nP + 2]?
      = some (.fvar (p.nP + 2) nmJ jdom) := by
    rw [List.getElem?_append_right (by omega), hlenP, Nat.sub_self]; rfl
  -- the pins, as `checkDirectDomsAt` records them
  have hpinsP := Setlec.checkDirectDomsAt_inv hdomsP
  have hpinsF := Setlec.checkDirectDomsAt_inv hdomsF
  -- the constructor's stored type
  obtain ⟨hCf, -, -, hCb, -⟩ := mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfC)
  simp only [ConstantInfo.toConstantVal] at hCf hCb
  -- the bits of the motive and of the minor
  obtain ⟨FM, tjM, uM, hjM, huM⟩ :=
    piDomsSorts_of_infer (p.nP + 3) hopAll hst p.nP _ hmfvR
  simp only [Expr.fvarTypeD, Nat.zero_add] at hjM huM
  obtain ⟨FM', tbM, vbM, hibM, hensbM, -, hbitsM⟩ :=
    piBits_of_infer hμ 1 (openPisAtFvars_one nmm mdom (.sort (elimLevel p)) mbm p.nP) hjM huM
  rw [Expr.instantiate1_sort] at hibM
  obtain rfl := inferTypeCore_sort_inv hibM
  obtain rfl := ensureSortCore_sort_eq hensbM
  obtain ⟨Fm, tjm, um, hjm, hum⟩ :=
    piDomsSorts_of_infer (p.nP + 3) hopAll hst (p.nP + 1) _ hminR
  simp only [Expr.fvarTypeD, Nat.zero_add] at hjm hum
  -- the frames, per assignment
  have hframes : ∀ ψ : Name → Nat,
      (∀ ρ : Nat → V, Sat2 V ((((rds ψ).take p.nP).map (·.2.2)).reverse) ρ ↔
        Sat2 V ((((ds ψ).take p.nP).map (·.2.2)).reverse) ρ) ∧
      ∀ ρ : Nat → V, Sat2 V ((((rds ψ).take p.nP).map (·.2.2)).reverse) ρ →
        RecBase ((elimLevel p).eval ψ) (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2))
          ((rds ψ).getD p.nP default) ((rds ψ).getD (p.nP + 1) default)
          ((rds ψ).getD (p.nP + 2) default) := by
    intro ψ
    have hc := claimsAtP_of hμ mp ψ F
    have hR : OpenedP mp.base2 ψ (p.nP + 3) type' (fvsP ++ [Expr.fvar (p.nP + 2) nmJ jdom]) _
        (((rds ψ).map (·.2.2)).reverse) (.app (.bvar 2) (.bvar 0)) :=
      openedP_of_peel hopAll htf' hbt' (hRD.read ψ) (hRD.len ψ) (hRD.okTy ψ)
    have hlenR : (((rds ψ).map (·.2.2)).reverse).length = p.nP + 3 := hR.len
    have hdrop3 := drop_three_rec (rds := rds ψ) (hRD.len ψ)
    -- the parameter frames
    obtain ⟨hident, hres, hwres, hbres, hleafres⟩ := recParamIdent hc hR hidxR hlenF
      (hCD.len ψ) (hCD.read ψ) (hCD.okTy ψ) hCf hCb (by rw [htakeR]; exact hci)
      (fun i hi => by
        obtain ⟨a, b, ha, hb, hdeq⟩ := hpinsP i hi
        exact ⟨a, b, by rw [htakeR]; exact ha, hb, hdeq⟩)
    have hiffP : ∀ ρ : Nat → V, Sat2 V ((((rds ψ).map (·.2.2)).reverse).drop 3) ρ ↔
        Sat2 V ((((ds ψ).take p.nP).map (·.2.2)).reverse) ρ := by
      intro ρ
      have := hident p.nP (Nat.le_refl _) ρ
      rwa [show p.nP + 3 - p.nP = 3 from by omega, Nat.sub_self, List.drop_zero] at this
    have hiffR : ∀ ρ : Nat → V, Sat2 V ((((rds ψ).take p.nP).map (·.2.2)).reverse) ρ ↔
        Sat2 V ((((ds ψ).take p.nP).map (·.2.2)).reverse) ρ := by
      intro ρ; rw [← hdrop3]; exact hiffP ρ
    refine ⟨hiffR, fun ρp hρp => ?_⟩
    have hρp3 : Sat2 V ((((rds ψ).map (·.2.2)).reverse).drop 3) ρp := by
      rw [hdrop3]; exact hρp
    have hsatC := (hiffR ρp).mp hρp
    have hsatP : ∀ ρ : Nat → V, Sat2 V ((((rds ψ).map (·.2.2)).reverse).drop 3) ρ →
        Sat2 V ((pps ψ).map (·.2.2)).reverse ρ :=
      fun ρ h => (hiff ψ ρ).mpr ((hiffP ρ).mp h)
    -- the former's walks
    have hFsOk : ∀ (ψ' : Name → Nat) (ρ : Nat → V), Sat2 V ((pps ψ').map (·.2.2)).reverse ρ →
        FieldsOkB (p.resSort.eval ψ') ρ (((ds ψ').drop p.nP).map (·.2.2)) ∧
        FieldsValid ρ (((ds ψ').drop p.nP).map (·.2.2)) :=
      fun ψ' ρ h => ⟨(hfields ψ' ρ ((hiff ψ' ρ).mp h)).1, (hfields ψ' ρ ((hiff ψ' ρ).mp h)).2.1⟩
    have hok : ∀ ρ : Nat → V,
        ParamsOkT (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) (pps ψ) :=
      fun ρ => (formerWalks hFD hFsOk ψ ρ).1
    have hval : ∀ ρ : Nat → V,
        UnderTowerValid ρ (towerBodyAV (p.resSort.eval ψ) (((ds ψ).drop p.nP).map (·.2.2))) (pps ψ) :=
      fun ρ => (formerWalks hFD hFsOk ψ ρ).2
    have hbitsT : ∀ d ∈ pps ψ, d.2.1 ≠ 0 := hFD.bits ψ
    have hfT' : env.find? p.cvT.name = some (.indInfo cvTa caps) := hfT
    have hlpsT' : (ConstantInfo.indInfo cvTa caps).toConstantVal.levelParams
        = p.cvT.levelParams := hlpsT
    -- the entries
    have heM : ((((rds ψ).map (·.2.2)).reverse)).getD 2 default
        = ((rds ψ).getD p.nP default).2.2 := by
      have := rec_entry (rds := rds ψ) (hRD.len ψ) (i := p.nP) (by omega)
      rwa [show p.nP + 3 - 1 - p.nP = 2 from by omega] at this
    have hem : ((((rds ψ).map (·.2.2)).reverse)).getD 1 default
        = ((rds ψ).getD (p.nP + 1) default).2.2 := by
      have := rec_entry (rds := rds ψ) (hRD.len ψ) (i := p.nP + 1) (by omega)
      rwa [show p.nP + 3 - 1 - (p.nP + 1) = 1 from by omega] at this
    have het : ((((rds ψ).map (·.2.2)).reverse)).getD 0 default
        = ((rds ψ).getD (p.nP + 2) default).2.2 := by
      have := rec_entry (rds := rds ψ) (hRD.len ψ) (i := p.nP + 2) (by omega)
      rwa [show p.nP + 3 - 1 - (p.nP + 2) = 0 from by omega] at this
    -- the motive's bit
    have hbitM : pwBit ψ mbm.pw ≠ 0 := by
      have h := (hbitsM ψ).1
      intro h0
      have := h.mp h0
      simp [Level.eval] at this
    -- the frame extensions
    have hdrop2 : (((rds ψ).map (·.2.2)).reverse).drop 2
        = (((rds ψ).map (·.2.2)).reverse).getD 2 default ::
          (((rds ψ).map (·.2.2)).reverse).drop 3 := by
      have h := drop_succ_eq_getD_cons hlenR (i := p.nP) (by omega)
      rwa [show p.nP + 3 - (p.nP + 1) = 2 from by omega, show p.nP + 3 - 1 - p.nP = 2 from by omega,
        show p.nP + 3 - p.nP = 3 from by omega] at h
    have hdrop1 : (((rds ψ).map (·.2.2)).reverse).drop 1
        = (((rds ψ).map (·.2.2)).reverse).getD 1 default ::
          (((rds ψ).map (·.2.2)).reverse).drop 2 := by
      have h := drop_succ_eq_getD_cons hlenR (i := p.nP + 1) (by omega)
      rwa [show p.nP + 3 - (p.nP + 1 + 1) = 1 from by omega,
        show p.nP + 3 - 1 - (p.nP + 1) = 1 from by omega,
        show p.nP + 3 - (p.nP + 1) = 2 from by omega] at h
    -- the motive
    have hmotive := recMotive hc hR hidxR hlenF hmfvR hbitM hfT' hlpsT'
      (by rw [htakeR]; exact hmdeq) (hleafT ψ) hbitsT (hFD.below ψ) (hFD.len ψ) hok hval hsatP
    -- the major
    have hmajor := recMajor hc hR hidxR hlenF hjR hfT' hlpsT'
      (by rw [htakeR]; exact hjdeq) (hleafT ψ) hbitsT (hFD.below ψ) (hFD.len ψ) hok hval hsatP
    -- the minor: the composite frame and the bits at the opened depth
    obtain ⟨Γm, Rm, comp⟩ := compOpenedP_of hR hidxR hminR hopX
    have hwm : Expr.WScoped (p.nP + 1) tym := by
      have := (hR.var (p.nP + 1) _ hminR).2.1
      simpa [Expr.fvarTypeD] using this
    have hjm2 : Setlec.inferTypeCore μ env Fm (p.nP + 2) tym = .ok tjm := by
      rw [Setlec.inferTypeCore_depth_inv mp.base2.wf Fm
        (Expr.WScoped.to_wscopedB (Expr.WScoped.mono (d' := p.nP + 2) (by omega) hwm))
        (Expr.WScoped.to_wscopedB hwm)]
      exact hjm
    have hum2 : Setlec.ensureSortCore μ env Fm (p.nP + 2) tjm = .ok um := by
      have hwt : Expr.WScoped (p.nP + 1) tjm :=
        Setlec.inferTypeCore_WScoped mp.base2.wf Fm hjm hwm
      rw [Setlec.ensureSortCore_depth_inv mp.base2.wf Fm
        (Expr.WScoped.to_wscopedB (Expr.WScoped.mono (d' := p.nP + 2) (by omega) hwt))
        (Expr.WScoped.to_wscopedB hwt)]
      exact hum
    obtain ⟨Fm', tbm, vbm, hibm, hensbm, -, hbitsm⟩ := piBits_of_infer hμ p.nF hopX hjm2 hum2
    have hvbm : vbm = elimLevel p := by
      rw [hminBody] at hibm
      obtain ⟨tf, n', ty', body', m', hif, hwh, rfl, -⟩ := Setlec.inferTypeCore_app_inv' hibm
      obtain ⟨-, rfl⟩ := inferTypeCore_fvar_inv hif
      obtain ⟨-, -, rfl, -⟩ := Expr.forallE.inj (Setlec.whnf_forallE_eq hwh)
      rw [Expr.instantiate1_sort] at hensbm
      exact ensureSortCore_sort_eq hensbm
    subst hvbm
    have hminor := recMinor hc hR hidxR hlenF hminR comp (hbitsm ψ) (hCD.len ψ) (hCD.okTy ψ)
      hfC hlpsC (hleafC ψ) hres hwres hbres hleafres hcf
      (fun i hi => by
        obtain ⟨a, b, ha, hb, hdeq⟩ := hpinsF i hi
        exact ⟨a, b, ha, hb, hdeq⟩)
      (by rw [hminBody, htakeR]) hiffP (fun ρ h => (hfields ψ ρ h).1)
    -- `RecBase`
    refine ⟨(hfields ψ ρp hsatC).1, ?_, ?_, ?_, ?_⟩
    · -- the squash bound at a large eliminator
      intro hw hl
      have hlarge : p.large = true := by
        cases hpl : p.large
        · exfalso
          apply hl
          simp [elimLevel, hpl, Level.eval]
        · rfl
      by_cases hnp : p.isProp = true
      · exact (hfields ψ ρp hsatC).2.2.2 hnp hlarge
      · have := (hfields ψ ρp hsatC).2.2.1 (by simpa using hnp)
        rwa [hw] at this
    · have h := (hR.okΓ p.nP (by omega) ρp
        (by rw [show p.nP + 3 - p.nP = 3 from by omega]; exact hρp3)).1
      rw [show p.nP + 3 - 1 - p.nP = 2 from by omega] at h
      rw [← heM]
      exact h
    · rw [← heM]
      exact hmotive ρp hρp3
    · intro M hM
      rw [← heM] at hM
      have hρM : Sat2 V ((((rds ψ).map (·.2.2)).reverse).drop 2) (cons M ρp) := by
        rw [hdrop2]; exact Sat2_cons V hρp3 hM
      refine ⟨?_, ?_, ?_⟩
      · have h := (hR.okΓ (p.nP + 1) (by omega) _
          (by rw [show p.nP + 3 - (p.nP + 1) = 2 from by omega]; exact hρM)).1
        rw [show p.nP + 3 - 1 - (p.nP + 1) = 1 from by omega] at h
        rw [← hem]
        exact h
      · rw [← hem]
        exact hminor ρp hρp3 M hM
      · intro m hm
        rw [← hem] at hm
        have hρm : Sat2 V ((((rds ψ).map (·.2.2)).reverse).drop 1) (cons m (cons M ρp)) := by
          rw [hdrop1]; exact Sat2_cons V hρM hm
        refine ⟨?_, ?_⟩
        · have h := (hR.okΓ (p.nP + 2) (by omega) _
            (by rw [show p.nP + 3 - (p.nP + 2) = 1 from by omega]; exact hρm)).1
          rw [show p.nP + 3 - 1 - (p.nP + 2) = 0 from by omega] at h
          rw [← het]
          exact h
        · rw [← het]
          exact hmajor _ hρm
  exact ⟨fun ψ => (hframes ψ).1, fun ψ => (hframes ψ).2⟩

end Setlec.Semantics
