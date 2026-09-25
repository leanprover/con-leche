module

public import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetOutRows
import ConLeche.Model.Inductives.TargetOutCerts
import ConLeche.Model.Inductives.TargetOutGrade
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetRowCertsW
import ConLeche.Model.Inductives.TargetResidue
public import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRuleGrading
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Inductives.RecStage

public section

/-!
# A target rule's FRAME at every class (lane NESTIND, session 9)

The `(c, j)`-th rule of a target check at ANY major — a member of the
block or an outside container (`TgtOutCls`) — opens one frame: the
recursor's prefix, then the constructor's fields at the major's
instantiation.  The facts every call row reads off that frame are the
same at both kinds; only their SOURCES differ (a member constructor's
record `hcore`, the member rows' readings; a container constructor's
environment entry, the instantiated constructor's reading `tgtOutOpen`
and grading `tgtOutCrestWd`).  `tgtFrame_cls` states them once, at the
target spellings (`tgtFdomsAV` for the fields), so the call rows over
the classes read no member-only lemma.

* `tgtFrame_cls` — the package (one case split on the member bit);
* `tgtFrame_walk` — the frame's walk context at any spine fitting the
  prefix and field domains (no case split).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts BlockShape
  TargetMajor RecShape)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Frame

variable {envC : Env} {mpC : EnvModelM V μ envC} {F : Nat} {pp : BlockParts}
  {cvTas : List ConstantVal} {ctorsAs : List (List (ConstantVal × Nat))}
  {out : List (ConstantVal × TargetMajor × List Expr)} {outside nested : Bool}
  {block : List ConstantInfo} {d : BlockData V}
  {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}

set_option maxHeartbeats 4000000 in
/-- **The `(c, j)`-th rule's frame at ANY class**: the target run, the
prefix and field openers, the frame, the abstraction, the stored
family's scoping, the major's parameters scoped at the prefix
(`TgtDsOk`), the constructor at the major's instantiation scoped, the
field openers' readings (the target field domains `tgtFdomsAV`) and the
prefix-and-field grading.  A member class reads its constructor's
record; an outside class its container's environment entry. -/
theorem tgtFrame_cls (hμ : μ.verifiedChecks = true) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) (ConLeche.tgtMemAt out))
    (R : ConLeche.TargetRecRun μ F (mkFEnv envC) pp.toBlockShape outside nested block cvTas
      ctorsAs out)
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm} {envI : Env}
    (hdR : ∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas) (ψ : Name → Nat)
    {c : Nat} (hc : c < (tgtRs out).length)
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[c]? = some r) {j : Nat} {cA : ConstantVal × Nat}
    (hcA : r.2.2.2[j]? = some cA) {rhs : Expr} (hrhs : r.2.1[j]? = some rhs) :
    ∃ (rc : RecShape) (rhs0 : Expr)
      (Q : ConLeche.TargetRuleRun μ F
        (ConLeche.consBlockRecsBareF pp.toBlockShape 0
          ((tgtRs out).map fun r => (r.1, r.2.2.1)) (mkFEnv envC)) (mkFEnv envC) pp.toBlockShape
        (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r.1 rc.rP r.1.type
        (tgtMajor out c) cA rhs0 rhs),
      rc.rP = pp.toBlockShape.rulePrefixAt c ∧
      Q.fvsPref = tgtPrefFvs pp.toBlockShape out c ∧
      Q.fvsF = tgtFieldFvs pp.toBlockShape out c j ∧
      tgtB pp.toBlockShape out c j = rc.rP + cA.2 ∧
      tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
        = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
            Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
              pp.toBlockShape.large)) ∧
      (Q.bodyO, Q.ihs) = tgtAbs μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j ∧
      Q.body.hasFvar = false ∧
      r.1.type.hasFvar = false ∧ r.1.type.looseBVarsBounded 0 = true ∧
      ConstsBound envC r.1.type ∧
      (∀ c', (tgtFam pp.toBlockShape (tgtRs out)).rPs.getD c' 0
        ≤ (tgtFam pp.toBlockShape (tgtRs out)).mIs.getD c' 0) ∧
      (∀ c',
        ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).hasFvar = false ∧
        ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero)).looseBVarsBounded 0
          = true ∧
        ConstsBound envC ((tgtFam pp.toBlockShape (tgtRs out)).recTys.getD c' (.sort .zero))) ∧
      TgtDsOk envC rc.rP Q.fvsPref (tgtMajor out c).ds ∧
      (ConLeche.targetCtorAt (tgtMajor out c) cA.1).hasFvar = false ∧
      (ConLeche.targetCtorAt (tgtMajor out c) cA.1).looseBVarsBounded 0 = true ∧
      ConstsBound envC (ConLeche.targetCtorAt (tgtMajor out c) cA.1) ∧
      (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length = cA.2 ∧
      (∀ (l : Nat) (x : Expr), Q.fvsF[l]? = some x →
        denoteMeta mpC.base2.acval envC ψ (rc.rP + l) x.fvarTypeD
          = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD l default)) ∧
      (∀ l, l < rc.rP + cA.2 → ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).take l) ys →
        WellDenotedV V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD l default)) := by
  -- the target run and the family's facts, at either kind
  obtain ⟨rc, rhs0, M, u, Q, hrc, hMaj, ⟨E⟩, hPref, hQcr, hFld, -, hFn, hAbs⟩ :=
    targetRuleAtG R hr hcA hrhs
  subst hMaj
  have hRP : tgtRP pp.toBlockShape c = rc.rP := by
    rw [tgtRP, List.getD_eq_getElem?_getD, hrc, Option.getD_some]
  have hrP : rc.rP = pp.toBlockShape.rulePrefixAt c := hRP.symm
  obtain ⟨hTf, -, hTres, hTb, hallRhs⟩ :=
    ConLeche.recStage_facts h r (List.mem_of_getElem? hr)
  have hTc : ConstsBound envC r.1.type := constsBound_of_constsResolve _ hTres
  have hbf : Q.body.hasFvar = false :=
    (stripLams_not_hasFvar _ Q.hstrip (hallRhs rhs (List.mem_of_getElem? hrhs)).1).2
  obtain ⟨hle, hRT3⟩ := tgtFam_facts h
  have hB : tgtB pp.toBlockShape out c j = rc.rP + cA.2 := by rw [tgtB_at hr hcA, hrP]
  have hFrEq : tgtFrame μ F (mkFEnv envC) pp.toBlockShape (cvTas.map (·.type)) out c j
      = ConLeche.targetFrameOf (tgtFam pp.toBlockShape (tgtRs out)) rc.rP Q.fvsPref Q.fvsF
          Q.fnorm (Level.zeronessOf (ConLeche.structElimLevel pp.toBlockShape.elim
            pp.toBlockShape.large)) := by
    rw [tgtFrame, ← hPref, ← hFld, ← hFn, hRP]
  have hfl : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length = cA.2 := by
    rw [tgtFdomsAV, readOpenedDoms_length_eq, ← hFld]
    exact openPisAtFvars_length _ Q.hfld
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr ψ, hrP]
  -- the prefix's grading (off the recursor type, at either kind)
  obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -, hwdTy⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
  have hPgrad : ∀ l, l < (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out)
      ψ c).length → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).take l)
        ys →
      WellDenotedV V (consList ys σ)
        ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).getD l
          default) := by
    intro l hl σ ys hys
    have hle' : pp.toBlockShape.rulePrefixAt c
        ≤ (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length := by
      rw [hlenRds]
      have := blockRecHrPle (p := pp) h hc
      omega
    exact prefixDoms_graded_of_tower (cc := blockRecConclAV mpC.base2.acval envC pp.toBlockShape
      (tgtRs out) ψ c) hle' (fun ρ' => by rw [← hTyE]; exact hwdTy ρ')
      (by rwa [blockRulePdomsAV_length hμ mpC h hr ψ] at hl) hys
  cases hmb : (tgtMajor out c).member with
  | some t =>
    -- a MEMBER major: its constructor's record
    have hm : (tgtMajor out c).member.isSome = true := by rw [hmb]; rfl
    have hmR := tgtMemAt_of_member hc hm
    obtain ⟨rc', rhs0', M', Q', hrP', hct, hds, -, -, -, -, -, -, hPrefEq, hFldEq, -, -, -, -,
      -⟩ := tgtRuleAt_facts_majorM h R hr hcA hrhs hm
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
    obtain ⟨ms0, hms0, hctA, -⟩ := recStage_ctorsAt (hm := hmR) h hr
    have hmemk0 : pp.toBlockShape.recTgtAt c
        < (blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).k :=
      (List.getElem?_eq_some_iff.mp hms0).1
    have hcj : ((blockDataOf V pp.toBlockShape ctorsAs pk uOfD ppsOf).ctorsM
        (pp.toBlockShape.recTgtAt c))[j]? = some cA := by
      show (ctorsAs.getD _ [])[j]? = _
      rw [List.getD_eq_getElem?_getD, hctA]; exact hcA
    obtain ⟨hfindC, -, -⟩ := hcore.2.2.2 _ hmemk0 j cA hcj
    have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfindC)
    have hCf : cA.1.type.hasFvar = false := hwfC.1
    have hct' : ConLeche.targetCtorAt (tgtMajor out c) cA.1 = cA.1.type := by
      simp [ConLeche.targetCtorAt, hmb]
    have hds' : (tgtMajor out c).ds = Q.fvsPref.take pp.toBlockShape.nP := by
      obtain ⟨-, -, -, -, -, hdsB⟩ := tgtMember_eq_block R hr hcA hrhs hm
      rw [hdsB, hPref, tgtPrefFvs_eq_block]
    have hcd := blockCtorData_of_core hcore hcj
    obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyAt h hmR hr
    have hFeq := tgtFdomsAV_eq_block R hr hcA hrhs hm mpC.base2.acval envC ψ
    have hfvB : tgtFieldFvs pp.toBlockShape out c j
        = blockRuleFieldFvs pp.toBlockShape (tgtRs out) c j :=
      (tgtMember_eq_block R hr hcA hrhs hm).2.2.1
    have hdF := (blockRuleFdomsAV_eq (hm := hmR) h hr hcA hrhs hcd hCf TE.nP_le ψ).2
    have hokPF := blockRuleHokPF_run hμ h ⟨pk, uOfD, ppsOf, rfl⟩ hS hcore hmr c r hmR hr j cA
      hcA ψ
    refine ⟨rc, rhs0, Q, hrP, hPref, hFld, hB, hFrEq, hAbs, hbf, hTf, hTb, hTc, hle, hRT3,
      tgtDsOk_of_take Q.hpref hTf hTc hds', by rw [hct']; exact hCf,
      by rw [hct']; exact hwfC.2.2.2.1,
      by rw [hct']; exact constsBound_of_constsResolve _ hwfC.2.2.1, hfl, ?_, ?_⟩
    · intro l x hx
      rw [hFeq, hrP]
      exact hdF l x (by rw [← hfvB, ← hFld]; exact hx)
    · intro l hl σ ys hys
      rw [hFeq] at hys ⊢
      exact hokPF l (by rw [← hrP]; exact hl) σ ys hys
  | none =>
    -- an OUTSIDE major: the container's entry, the instantiated constructor
    have hcl := hcls c hc hmb
    obtain ⟨dsa, hdsa, hul, hds, hlenP, -⟩ := tgtOutSatW hμ mpC hcov h R hr hmb hcl ψ
    have hdsaE : dsa = tgtOutDsa mpC.base2.acval envC pp.toBlockShape out ψ c :=
      denoteMetaSpine_eq_map hdsa
    subst hdsaE
    obtain ⟨-, -, -, ab, -, -, -, -, -, hfdE, hfdR, hcrR⟩ :=
      tgtOutOpen R hr hcA hrhs hmb hcl hul hds ψ hdsa hlenP
    have hdsOk0 := tgtOutDsOk h R hr hmb
    have hdsOk : TgtDsOk envC rc.rP Q.fvsPref (tgtMajor out c).ds := by
      rw [hRP, ← hPref] at hdsOk0; exact hdsOk0
    have hcAM : (tgtMajor out c).ctors[j]? = some cA := by
      rw [← tgtRs_ctors hr]; exact hcA
    have hiL : j < (tgtMajor out c).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
    have hcAi : (tgtMajor out c).ctors[j] = cA := (List.getElem?_eq_some_iff.mp hcAM).2
    have hfc0 := hcl.hctor j hiL
    rw [hcAi] at hfc0
    have hwfC := mpC.base2.wf _ (List.mem_of_find?_eq_some hfc0)
    have hct : ConLeche.targetCtorAt (tgtMajor out c) cA.1
        = cA.1.type.instantiateLevelParams cA.1.levelParams (tgtMajor out c).lvls := by
      simp [ConLeche.targetCtorAt, hmb]
    have hFgrad : ∀ q, q < (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length →
        ∀ (σ : Nat → V) (zs ys : List V),
        SpineFit σ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c) zs →
        SpineFit (consList zs σ)
          ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).take q) ys →
        WellDenotedV V (consList ys (consList zs σ))
          ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD q default) := by
      intro q hq σ zs ys hzs hys
      have hcw := tgtOutCrestWd hμ hcov h R hr hcA hrhs hmb hcl ψ σ hzs hcrR
      rw [hfdE] at hq hys ⊢
      exact wdV_mkPisAV_dom hcw q (by simpa using hq) ys hys
    refine ⟨rc, rhs0, Q, hrP, hPref, hFld, hB, hFrEq, hAbs, hbf, hTf, hTb, hTc, hle, hRT3, hdsOk,
      by rw [hct, Expr.hasFvar_instantiateLevelParams]; exact hwfC.1,
      by rw [hct, Expr.looseBVarsBounded_instantiateLevelParams]; exact hwfC.2.2.2.1,
      by
        rw [hct]
        refine constsBound_of_constsResolve _ ?_
        rw [ConLeche.Expr.constsResolve_instantiateLevelParams]
        exact hwfC.2.2.1, hfl, ?_, ?_⟩
    · intro l x hx
      rw [← hRP]
      exact hfdR l x (by rw [← hFld]; exact hx)
    · intro l hl σ ys hys
      exact hokA_of_two hPgrad hFgrad l (by rw [hpl, hfl]; exact hl) σ ys hys

/-- **The frame's walk context** at any spine fitting the prefix and the
target field domains, from `tgtFrame_cls`'s facts (no case split). -/
theorem tgtFrame_walk (hμ : μ.verifiedChecks = true)
    {memR : Nat → Prop} (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs (tgtRs out) memR)
    (ψ : Name → Nat) {c : Nat}
    {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[c]? = some r) {j : Nat} {cA : ConstantVal × Nat}
    {rc : RecShape} {rhs0 rhs : Expr}
    (Q : ConLeche.TargetRuleRun μ F
        (ConLeche.consBlockRecsBareF pp.toBlockShape 0
          ((tgtRs out).map fun r => (r.1, r.2.2.1)) (mkFEnv envC)) (mkFEnv envC) pp.toBlockShape
        (cvTas.map (·.type)) (tgtFam pp.toBlockShape (tgtRs out)) r.1 rc.rP r.1.type
        (tgtMajor out c) cA rhs0 rhs)
    (hrP : rc.rP = pp.toBlockShape.rulePrefixAt c)
    (hTf : r.1.type.hasFvar = false) (hTb : r.1.type.looseBVarsBounded 0 = true)
    (hTc : ConstsBound envC r.1.type)
    (hdsOk : TgtDsOk envC rc.rP Q.fvsPref (tgtMajor out c).ds)
    (hCf : (ConLeche.targetCtorAt (tgtMajor out c) cA.1).hasFvar = false)
    (hCb : (ConLeche.targetCtorAt (tgtMajor out c) cA.1).looseBVarsBounded 0 = true)
    (hCc : ConstsBound envC (ConLeche.targetCtorAt (tgtMajor out c) cA.1))
    (hfl : (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length = cA.2)
    (hF : ∀ (l : Nat) (x : Expr), Q.fvsF[l]? = some x →
        denoteMeta mpC.base2.acval envC ψ (rc.rP + l) x.fvarTypeD
          = some ((tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD l default))
    (hokPF : ∀ l, l < rc.rP + cA.2 → ∀ (σ : Nat → V) (ys : List V),
        SpineFit σ ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).take l) ys →
        WellDenotedV V (consList ys σ)
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).getD l default))
    {ρ : Nat → V} {xs fs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
      ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j) (xs ++ fs)) :
    WalkCtx V mpC.base2 ψ (rc.rP + cA.2) (consList (xs ++ fs) ρ)
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
        ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).reverse
      (Q.fvsPref ++ Q.fvsF).reverse := by
  obtain ⟨-, hlbF, hcbF, hher⟩ := targetFrame_facts Q.hpref Q.hcrest hdsOk Q.hfld hTf hTb hTc
    hCf hCb hCc
  have hpl : (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
      = rc.rP := by rw [blockRulePdomsAV_length hμ mpC h hr ψ, hrP]
  have hdoms : ∀ (q : Nat) (x : Expr), (Q.fvsPref ++ Q.fvsF)[q]? = some x →
      denoteMeta mpC.base2.acval envC ψ q (Expr.fvarTypeD x)
        = some ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).reverse.getD
              (rc.rP + cA.2 - 1 - q) default) := by
    intro q x hx
    have hq := blockRuleHdoms_of (acval := mpC.base2.acval) (envT := envC)
      (ψ := ψ) (ihdoms := []) (fvsIh := []) hpl hfl rfl
      (openPisAtFvars_length _ Q.hpref) (openPisAtFvars_length _ Q.hfld) rfl
      (blockRulePdomsAV_reads hμ mpC h hr _ (by rw [← hrP]; exact Q.hpref)) hF
      (fun l x hx => nomatch hx) q x (by simpa using hx)
    simpa using hq
  have hokΔ : ∀ q, q < rc.rP + cA.2 → ∀ ρ' : Nat → V,
      Sat V (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).reverse ρ' →
      WellDenotedV V (fun l => ρ' (l + (rc.rP + cA.2 - 1 - q) + 1))
        ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c
            ++ tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).reverse.getD
              (rc.rP + cA.2 - 1 - q) default) := by
    intro q hq ρ' hsat
    have hk := blockRuleHokΔ_of (V := V) (ihdoms := []) hpl hfl rfl
      (fun l hl σ' ys hys => by
        have := hokPF l (by simpa using hl) σ' ys (by simpa using hys)
        simpa using this) q (by simpa using hq) ρ' (by simpa using hsat)
    simpa using hk
  have h₃ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (rc.rP + cA.2)
      = some ([], Expr.sort .zero) := rfl
  have hW := walkCtx_blockFrame (V := V) (mT := mpC.base2) (ψ := ψ) (ihdoms := [])
    (ihvals := []) Q.hpref Q.hfld h₃ hpl hfl rfl
    (by simpa using hdoms) (by simpa using hokΔ)
    (by simpa using hlbF) (by simpa using hcbF) (by simpa using hher) hsp (by simp [SpineFit])
  simpa using hW

end Frame

end ConLeche.Model
