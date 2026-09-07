import Lech.SetP.Direct.DirectRecLawP

/-!
# The recursor's cons (task #175 W4c, P3 module 6, part 20; S2)

`stageRec`: the P step at the recursor's cons.  The stored recursor is
the *generated* one (task #175 S2): its data is read off syntactically
(`recData_of`), its leaf is `directRecAV ℓ (rds ψ) nF` over that
data, the frames' walks (`recLeafFacts` over `recFrames`, a
computation) give the leaf's grading and membership, the capability
laws are the fieldless family's (the projection slots are still
empty), and the rule's law is `recRuleLaw` over the generated rule
when the rule is plain (an inert rule owes nothing).
-/

namespace Lech.SetP
open Lech.Semantics
open Lech.SetModel

open Lech.VExpr Lech.Verify SetTheory Lech.SetTheory.Tower
open Lech.Semantics (AVExpr)
open Lech (Env Expr Name Level ConstantInfo ConstantVal IndCaps DirectParts
  BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- The generated recursor type's opening, at every assignment: the
type strips its `nP + 3` binders by construction. -/
theorem recOpenedAll (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr}
    (hRec : Lech.checkDirectRec (Lech.fueledOps μ F) env p cvTa cvCa = .ok (cvRa, rhsA))
    {bsT : List (Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis p.nP = some (bsT, .sort p.resSort))
    {rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hRD : RecData mp.base2 cvRa p.nP (elimLevel p) rds) :
    ∃ (fvsR : List Expr) (oR : Expr), ∀ ψ : Name → Nat,
      OpenedP mp.base2 ψ (p.nP + 3) cvRa.type fvsR oR (((rds ψ).map (·.2.2)).reverse)
        (.app (.bvar 2) (.bvar 0)) := by
  obtain ⟨cvRi, recTy, sty, rhsTy, u, -, hgen, -, -, -, hbt, hRf, -, -, -, -, -, -, -, -, rfl⟩ :=
    Lech.checkDirectRec_shape hRec
  obtain ⟨cbs, crest0, minorTy, -, -, hrec⟩ := Lech.directRecTy_single hgen
  have hs1 := Lech.replacePisPw_stripPis p.nP hrec hstripT
  have hs := Lech.stripPis_append p.nP (m := 3) hs1 rfl
  obtain ⟨fvsR, oR, hop⟩ := openPisAtFvars_of_stripPis_isSome (p.nP + 3) 0 (by rw [hs]; rfl)
  exact ⟨fvsR, oR, fun ψ =>
    openedP_of_peel hop hRf hbt (hRD.read ψ) (hRD.len ψ) (hRD.okTy ψ)⟩

/-- **The P step at the recursor's cons.** -/
theorem stageRec (hE : Lech.EtaFamiliesClosed env)
    (mp : EnvS2PM V μ env)
    {F : Nat} {p : DirectParts} {cvTa cvCa cvRa : ConstantVal} {rhsA : Expr}
    (hRec : Lech.checkDirectRec (Lech.fueledOps μ F) env p cvTa cvCa = .ok (cvRa, rhsA))
    {bsT : List (Expr × BinderMeta)}
    (hstripT : cvTa.type.stripPis p.nP = some (bsT, .sort p.resSort))
    (hfT : env.find? p.cvT.name = some (.indInfo cvTa (Lech.directCaps p)))
    (hlpsT : cvTa.levelParams = p.cvT.levelParams)
    (hfC : env.find? p.cvC.name = some (.ctorInfo cvCa p.nP p.nF))
    (hlpsC : cvCa.levelParams = p.cvT.levelParams)
    (helim : p.large = true → p.elim ∈ p.cvR.levelParams)
    -- the projection slots are still empty at the extension
    (hslot0 : 0 < p.nF →
      (⟨.recInfo cvRa (p.nP + 2) (p.nP + 2)
        [⟨p.cvC.name, p.nF, p.nP,
          if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then .plain else .inert,
          rhsA⟩] :: env.consts⟩ : Env).find? (Lech.projFnName p.cvT.name 0) = none)
    {pps ds rds : (Name → Nat) → List (Nat × Nat × AVExpr)}
    (hFD : FormerData mp.base2 cvTa p.nP p.resSort pps)
    (hCD : CtorData mp.base2 p.cvT.name cvCa p.nP p.nF p.resSort ds)
    (hRD : RecData mp.base2 cvRa p.nP (elimLevel p) rds)
    (hrds : ∀ ψ, rds ψ
      = recDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p) (pps ψ) (ds ψ))
    (hRuleRead : ∀ ψ : Name → Nat, denoteP mp.base2.acval env ψ 0 rhsA
      = some (mkLamsAV (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
          (pps ψ) (ds ψ)) (AVExpr.mkAppN (.bvar p.nF) (fieldBvars p.nF))))
    (hRuleOk : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      AnnotOkP V ρ (mkLamsAV (ruleDataAV mp.base2 p.cvT.name p.cvC.name ψ p.nP p.nF (elimLevel p)
          (pps ψ) (ds ψ)) (AVExpr.mkAppN (.bvar p.nF) (fieldBvars p.nF))))
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
  -- the openings and the frames
  obtain ⟨fvsR, oR, hR⟩ := recOpenedAll mp hRec hstripT hRD
  have hbase := fun ψ => (recFrames (m := mp.base2) hFD hCD hleafT hleafC hiff hfields ψ
    (hrds ψ) (hR ψ)).2
  -- the constant's facts
  obtain ⟨cvRi, recTy, sty, rhsTy, u, hccv, -, -, htp, htrR, -, -, -, hrhsRes, -, -, -, -, -, -,
    hcvRa⟩ := Lech.checkDirectRec_shape hRec
  obtain ⟨hfind, hnres, hpshape, -, -, -, -, -, -, -, -, -, -, -, -⟩ :=
    Lech.checkConstantVal_inv hccv
  have hRname : cvRa.name = p.cvR.name := by rw [hcvRa]
  have hRlps : cvRa.levelParams = p.cvR.levelParams := by rw [hcvRa]
  have hRtype : cvRa.type = recTy := by rw [hcvRa]
  have hfresh : env.find? cvRa.name = none := by rw [hRname]; exact hfind
  have htrR' : cvRa.type.constsResolve env = true := by rw [hRtype]; exact htrR
  have hcbR : ConstsBound env cvRa.type := constsBound_of_constsResolve _ htrR'
  have hwf := Lech.direct_rec_wf mp.base2.wf hRec
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
  have hnresC : Lech.reservedBasisNames.contains c₀.name = false := by
    show Lech.reservedBasisNames.contains cvRa.name = false
    rw [hRname]; exact hnres
  have hpshapeC : c₀.name.isProjFnShape = false := by
    show cvRa.name.isProjFnShape = false
    rw [hRname]; exact hpshape
  refine declStepPM_of_ind_rec_cons mp (c₀ := c₀) (A := A) hfresh hnresC ⟨_, _, _, _, rfl⟩
    (ConsHeadP.ofFresh hwf (fun ψ => hAbelow ψ) hnresC
      (fun _ h => nomatch h)
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
    show directRecAV _ (rds ψ₁) p.nF = directRecAV _ (rds ψ₂) p.nF
    rw [hRD.params ψ₁ ψ₂ hφR]
    congr 1
    rw [hRlps] at hφR
    cases hpl : p.large
    · simp [elimLevel, Lech.directElimLevel, hpl, Level.eval]
    · simp only [elimLevel, Lech.directElimLevel, hpl, if_true, Level.eval]
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
          = some (.indInfo cvTa (Lech.directCaps p)) := by
        rw [Lech.Env.find?_cons, if_neg (fun h => hTR h.symm)]
        exact hfT
      obtain ⟨rfl, rfl⟩ := ConstantInfo.indInfo.inj (Option.some.inj (hfT'.symm.trans hf))
      have hFD₂ : FormerData m₂ cvTa p.nP p.resSort pps :=
        hFD.cross (c₀ := c₀) (A := A) hfresh (hcross _)
          (constsBound_of_constsResolve _
            (mp.base2.wf _ (Lech.Semantics.Env.find?_mem hfT)).2.2.1) m₂ hac
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
          refine directEtaLawP0 (m := m₂) (T := p.cvT.name) (caps := Lech.directCaps p)
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
        refine directUnitLawP (m := m₂) (T := p.cvT.name) (caps := Lech.directCaps p)
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
      exact recRuleLaw mp hfT hlpsT hfC hlpsC hFD hCD hRD hrds hR hleafT hleafC hiff hfields
        hRuleRead hRuleOk hrhsRes htrR' hfresh hrule m₂ hac (fun ψ ρ => (hleaf ψ ρ).1) φ'
    · exfalso
      apply hfire
      simp [hplain]

end Lech.SetP
