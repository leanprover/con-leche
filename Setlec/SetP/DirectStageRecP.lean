import Setlec.SetP.DirectRecLawP

/-!
# The recursor's cons (task #175 W4c, P3 module 6, part 20)

`stageRec`: the P step at the recursor's cons.  The leaf is
`directRecAV ℓ (rds ψ) nF` over the recursor type's peel; its
hereditary premises are the frames' walks (`recLeafFacts`), the
capability laws are the fieldless family's (the projection slots are
still empty), and the rule's law is `recRuleLaw` when the rule is
plain (an inert rule owes nothing).
-/

namespace Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory Setlec.SetTheory.Tower
open Setlec.Semantics (AVExpr)
open Setlec (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The recursor type's opening, at every assignment, from the stage's
runs. -/
theorem recOpenedAll (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal}
    (hccv : Setlec.checkConstantVal (Setlec.fueledOps μ F) env p.cvR = .ok cvRa)
    (hRec : Setlec.checkDirectRecTy (Setlec.fueledOps μ F) env p cvTa cvCa cvRa
      = .ok ())
    {rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hRD : RecData mp.base2 cvRa p.nP (elimLevel p) rds) :
    ∃ (fvsR : List Expr) (oR : Expr), ∀ ψ : Name → Nat,
      OpenedP mp.base2 ψ (p.nP + 3) cvRa.type fvsR oR (((rds ψ).map (·.2.2)).reverse)
        (.app (.bvar 2) (.bvar 0)) := by
  obtain ⟨-, fvsP, rest, -, -, mfv, -, -, -, -, -, -, -, jbs, jbody, -,
    hopR, -, -, hmfv, -, -, -, -, -, -, -, -, -, hjs, -, -, hjbody⟩ :=
    Setlec.checkDirectRecTy_shape hRec
  obtain ⟨-, -, -, -, hlbt, hitf, type', -, -, hann', -, -, -, -, rfl⟩ :=
    Setlec.checkConstantVal_inv hccv
  obtain ⟨htf', hbt'⟩ := annotate_syntax hann' hitf hlbt
  simp only at htf' hbt' hopR hRD ⊢
  obtain ⟨nmM, tyM, rfl⟩ := openPisAtFvars_index _ _ _ hopR p.nP mfv hmfv
  obtain ⟨nmJ, jdom, mbJ, rfl, -⟩ := stripPis_one_inv hjs
  subst hjbody
  rw [Nat.zero_add] at hopR
  have hopAll : openPisAtFvars (p.nP + 3) type' 0
      = some (fvsP ++ [.fvar (p.nP + 2) nmJ jdom],
          .app (.fvar p.nP nmM tyM) (.fvar (p.nP + 2) nmJ jdom)) := by
    have := openPisAtFvars_add (p.nP + 2) hopR
      (openPisAtFvars_one nmJ jdom (.app (.fvar p.nP nmM tyM) (.bvar 0)) mbJ (0 + (p.nP + 2)))
    rw [Nat.zero_add] at this
    simpa using this
  exact ⟨_, _, fun ψ =>
    openedP_of_peel hopAll htf' hbt' (hRD.read ψ) (hRD.len ψ) (hRD.okTy ψ)⟩

/-- **The P step at the recursor's cons.** -/
theorem stageRec (hμ : μ.verified = true) (hE : Setlec.EtaFamiliesClosed env)
    (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr}
    (hccv : Setlec.checkConstantVal (Setlec.fueledOps μ F) env p.cvR = .ok cvRa)
    (hRec : Setlec.checkDirectRecTy (Setlec.fueledOps μ F) env p cvTa cvCa cvRa
      = .ok ())
    (hRule : Setlec.checkDirectRule (Setlec.fueledOps μ F) env p cvCa cvRa = .ok rhsA)
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa (Setlec.directCaps p)))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    (helim : p.large = true → p.elim ∈ p.cvR.levelParams)
    -- the projection slots are still empty at the extension
    (hslot0 : 0 < p.nF →
      (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
          rhsA⟩] :: env.consts⟩ : Env).find? (Setlec.projFnName p.cvT.name 0) = none)
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
    ∃ mp' : EnvS2PM V μ ⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
          rhsA⟩] :: env.consts⟩,
      mp'.base2.acval = acvalWith mp.base2.acval cvRa.name
        (fun ψ => directRecAV ((elimLevel p).eval ψ) (rds ψ) p.nF) := by
  -- the frames and the openings
  obtain ⟨hiffR, hbase⟩ := recFrames hμ mp hccv hRec hfT hlpsT hfC hlpsC hFD hCD hRD hleafT
    hleafC hiff hfields
  obtain ⟨fvsR, oR, hR⟩ := recOpenedAll mp hccv hRec hRD
  -- the constant's facts
  obtain ⟨hfind, hnres, hpshape, -, -, -, type', -, -, -, -, htr', -, -, hty⟩ :=
    Setlec.checkConstantVal_inv hccv
  have hRname : cvRa.name = p.cvR.name := by rw [hty]
  have hRlps : cvRa.levelParams = p.cvR.levelParams := by rw [hty]
  have hfresh : env.find? cvRa.name = none := by rw [hRname]; exact hfind
  have htrR : cvRa.type.constsResolve env = true := by rw [hty]; exact htr'
  have hcbR : ConstsBound env cvRa.type := constsBound_of_constsResolve _ htrR
  have hwf := Setlec.direct_rec_wf mp.base2.wf hccv hRule
  have hTR : p.cvT.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfT; exact nomatch hfT
  have hCR : p.cvC.name ≠ cvRa.name := by
    intro h; rw [h, hfresh] at hfC; exact nomatch hfC
  -- the leaf
  let A : (Name → Nat) → AVExpr :=
    fun ψ => directRecAV ((elimLevel p).eval ψ) (rds ψ) p.nF
  have hAbelow : ∀ ψ, VExpr.bvarsBelow 0 (A ψ).erase := fun ψ =>
    directRecAV_below (hRD.below ψ) (by rw [hRD.len ψ]; omega)
  have hleaf : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (A ψ) ∧
      interp2 V ρ (A ψ) ∈ˢ interp2 V ρ (mkPisAV (rds ψ) (.app (.bvar 2) (.bvar 0))) :=
    fun ψ ρ => by
      have h := recLeafFacts (hRD.len ψ) (hRD.bits ψ) (hR ψ).okΓ (hbase ψ) ρ
      have hlenFs : ((((ds ψ).drop p.nP).map (·.2.2))).length = p.nF := by simp [hCD.len ψ]
      rw [hlenFs] at h
      exact h
  -- the cons head
  let c₀ : ConstantInfo := .recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP,
      if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert, rhsA⟩]
  have hcross : ∀ e : Expr, ConsCrossAt c₀ e := fun _ => ConsCrossAt.ofNtc (fun _ h => nomatch h)
  have hreadR : ∀ ψ : Name → Nat,
      denoteP (acvalWith mp.base2.acval cvRa.name A) ⟨c₀ :: env.consts⟩ ψ 0 cvRa.type
        = some (mkPisAV (rds ψ) (.app (.bvar 2) (.bvar 0))) := fun ψ =>
    denoteP_cons_mono (c₀ := c₀) hfresh (hcross _) ψ 0 hcbR (hRD.read ψ)
  have hnresC : Setlec.reservedBasisNames.contains c₀.name = false := by
    show Setlec.reservedBasisNames.contains cvRa.name = false
    rw [hRname]; exact hnres
  have hpshapeC : c₀.name.isProjFnShape = false := by
    show cvRa.name.isProjFnShape = false
    rw [hRname]; exact hpshape
  refine declStepPM_of_ind_rec_cons mp (c₀ := c₀) (A := A) hfresh hnresC ⟨_, _, _, _, rfl⟩
    (ConsHeadP.ofFresh hwf (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h) (fun _ h => nomatch h)
      (fun cvR' mI rP rules heq r hr => by
        injection heq with _ _ _ hrules
        subst hrules
        rcases List.mem_singleton.mp hr with rfl
        exact ⟨cvCa, p.nP, p.nF, hfC⟩))
    (fun ψ k => AVExpr.liftN_eq_self _
      (VExpr.bvarsBelow.mono (Nat.zero_le k) (hAbelow ψ)) 1)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · -- level dependence
    intro ψ₁ ψ₂ hφ
    have hφR : ∀ q ∈ cvRa.levelParams, ψ₁ q = ψ₂ q := hφ
    rw [hRlps] at hφR
    show directRecAV _ (rds ψ₁) p.nF = directRecAV _ (rds ψ₂) p.nF
    rw [hRD.params ψ₁ ψ₂ (by rw [hRlps]; exact hφR)]
    congr 1
    cases hpl : p.large
    · simp [elimLevel, hpl, Level.eval]
    · simp only [elimLevel, hpl, if_true, Level.eval]
      exact hφR p.elim (helim hpl)
  · exact fun ψ ρ => (hleaf ψ ρ).1.1
  · exact fun ψ ρ => (hleaf ψ ρ).1.2
  · exact fun ψ => ⟨_, hreadR ψ⟩
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadR ψ).symm.trans hta)
    exact hRD.okTy ψ ρ
  · intro ψ ta hta ρ
    obtain rfl := Option.some.inj ((hreadR ψ).symm.trans hta)
    exact (hleaf ψ ρ).2
  · -- `caps_ok`
    intro m₂ hac
    refine capsOkP_cons_direct mp (c₀ := c₀) (A := A) (T := p.cvT.name) hfresh
      (ConsCrossEnv.ofNtc fun _ h => nomatch h) hpshapeC
      (Or.inr fun _ _ h => nomatch h) ?_ m₂ hac ?_
    · intro T' cvT' caps' hf hne hres hcape
      exact hE T' cvT' caps' hf hcape hres
    · intro cvT caps hf hres
      have hfT' : (⟨c₀ :: env.consts⟩ : Env).find? p.cvT.name
          = some (.indInfo cvTa (Setlec.directCaps p)) := by
        rw [Setlec.Env.find?_cons, if_neg (fun h => hTR h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      have hFD₂ : FormerData m₂ cvTa p.nP p.resSort pps :=
        hFD.cross (c₀ := c₀) (A := A) hfresh (hcross _)
          (constsBound_of_constsResolve _
            (mp.base2.wf _ (Setlec.Semantics.Env.find?_mem hfT)).2.2.1) m₂ hac
      have hleafT₂ : ∀ ψ, m₂.acval p.cvT.name ψ
          = directTyAV (p.resSort.eval ψ) (pps ψ) (((ds ψ).drop p.nP).map (·.2.2)) := by
        intro ψ
        rw [hac]
        show acvalWith mp.base2.acval cvRa.name A p.cvT.name ψ = _
        rw [acvalWith_ne hTR]
        exact hleafT ψ
      have hFsOk : ∀ (ψ' : Name → Nat) (ρ : Nat → V),
          Sat2 V ((pps ψ').map (·.2.2)).reverse ρ →
          FieldsOkB (p.resSort.eval ψ') ρ (((ds ψ').drop p.nP).map (·.2.2)) ∧
          FieldsValid ρ (((ds ψ').drop p.nP).map (·.2.2)) :=
        fun ψ' ρ h => ⟨(hfields ψ' ρ ((hiff ψ' ρ).mp h)).1, (hfields ψ' ρ ((hiff ψ' ρ).mp h)).2.1⟩
      have hpok : ∀ ψ ρ, ParamsOkT (p.resSort.eval ψ) ρ (((ds ψ).drop p.nP).map (·.2.2)) (pps ψ) :=
        fun ψ ρ => (formerWalks hFD hFsOk ψ ρ).1
      refine ⟨fun _ hfam φ' => ?_, fun hunit φ' => ?_⟩
      · -- η: fieldless (the slots are empty otherwise)
        rcases Nat.eq_zero_or_pos p.nF with hnF | hnF
        · have hFs0 : ∀ ψ, ((ds ψ).drop p.nP).map (·.2.2) = [] := by
            intro ψ
            rw [List.drop_eq_nil_of_le (by rw [hCD.len ψ, hnF]; exact Nat.le_refl _)]
            rfl
          refine directEtaLawP0 (m := m₂) (T := p.cvT.name) (caps := Setlec.directCaps p)
            (ds := ds) hnF ?_ ?_ hFD₂.read hFD₂.okTy ?_ ?_ ?_
          · intro ψ; rw [hleafT₂ ψ, hFs0 ψ]
          · intro ψ
            show m₂.acval p.cvC.name ψ = _
            rw [hac]
            show acvalWith mp.base2.acval cvRa.name A p.cvC.name ψ = _
            rw [acvalWith_ne hCR, hleafC ψ, hFs0 ψ]
          · intro ψ ρ; have := hpok ψ ρ; rwa [hFs0 ψ] at this
          · intro ψ ρ as hsp
            have hl := hsp.length_eq
            have hds : ds ψ = (ds ψ).take p.nP := by
              rw [List.take_of_length_le (by rw [hCD.len ψ, hnF]; exact Nat.le_refl _)]
            rw [hds]
            exact (spineFit_iff_of_sat2_iff (by simp [hFD.len ψ, hCD.len ψ, hnF])
              (hiff ψ) ρ as (by simpa using hl)).mp hsp
          · intro ψ; show p.nP = (pps ψ).length; rw [hFD.len ψ]
        · exfalso
          obtain ⟨-, -, hfP⟩ := hfam
          obtain ⟨cv, mI, rP, rules, hf0⟩ := hfP 0 hnF
          rw [hslot0 hnF] at hf0
          exact nomatch hf0
      · have hnF : p.nF = 0 := by
          have : (p.nF == 0) = true := hunit
          simpa using this
        have hFs0 : ∀ ψ, ((ds ψ).drop p.nP).map (·.2.2) = [] := by
          intro ψ
          rw [List.drop_eq_nil_of_le (by rw [hCD.len ψ, hnF]; exact Nat.le_refl _)]
          rfl
        refine directUnitLawP (m := m₂) (T := p.cvT.name) (caps := Setlec.directCaps p)
          ?_ hFD₂.read hFD₂.okTy ?_ ?_
        · intro ψ; rw [hleafT₂ ψ, hFs0 ψ]
        · intro ψ ρ; have := hpok ψ ρ; rwa [hFs0 ψ] at this
        · intro ψ; show p.nP = (pps ψ).length; rw [hFD.len ψ]
  · -- `rec_rules`
    intro m₂ hac φ'
    refine recRulesP_cons_rec mp (c₀ := c₀) (A := A) hfresh rfl m₂ hac φ' ?_
    intro rl hrl hfire
    rcases List.mem_singleton.mp hrl with rfl
    by_cases hplain : Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP = true
    · have hrule : (⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
          rhsA⟩ : RecRule) = ⟨p.cvC.name, p.nF, p.nP, .plain, rhsA⟩ := by
        simp [hplain]
      exact recRuleLaw hμ mp hccv hRec hRule hfT hlpsT hfC hlpsC hFD hCD hRD hleafT hleafC
        hiff hfields hfresh hrule m₂ hac (fun ψ ρ => (hleaf ψ ρ).1) φ'
    · exfalso
      apply hfire
      simp [hplain]

end Setlec.Semantics
