module

import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Model.Inductives.TargetNodeCalls
public import ConLeche.Model.Inductives.TargetNodePres
import ConLeche.Model.Inductives.TargetRank
import ConLeche.Model.Inductives.TargetFlatInd
import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.TargetNodeSem
import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.TargetNodeCover
import ConLeche.Model.Inductives.TargetGuardParams
import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Inductives.BlockPosRunCont
import ConLeche.Model.Inductives.BlockModelRecords
import ConLeche.Model.Inductives.BlockHoleGrade
import ConLeche.Model.Annot.BlockLfpMono
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Inductives.BlockCtorReads
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.BlockStageRec
import ConLeche.Verify.Inductives.BlockPartsInv
import ConLeche.Semantics.Inductives.DeclBlockEta
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.NestedRecPins
import ConLeche.Model.Inductives.NestedRecEqs
import ConLeche.Model.Inductives.NestedRecData
import ConLeche.Model.Inductives.TargetSeam
import ConLeche.Model.Inductives.TargetResidue

public section

/-!
# The uniform block step (#315)

`declBlock`: **the P carrier survives the UNIFORM install's run at `k`
members**, nested blocks included — from a covered carrier, some covered
carrier at the installed environment.  It is the fold's block step
(`declStep_preserves`, `Model/Fold.lean`).  One straight path, each stage
read off its own run:

* the formers' and the constructors' stage (`blockTablesStage_of`), the
  operator's monotonicity from positivity (`blockCtorPos_of_run`) and
  the fields' grading (`blockHoleGrade_of_run`), under coverage at the
  formers' carrier (`lfpCover_formers`);
* the constructors consed (`stageBlockCtors`), the block's lfp clause
  recorded, coverage across the conses;
* the recursors' stage (`nestedRecStage`, the four cons-monotonicities
  `BlockRecStagedT`): the generic stage at the target rule data
  (`blockRecStaged_dataR`), its family premise's candidate from the
  induction over the recursor classes (`tgtRecPre_clsI`), which reads the
  class tie to the positivity derivation's nodes (`nestedClassNodes`: the
  node list `nestedRecCtx_nodes`, its admissible frames `nodeAdm` and the
  calls `nestedNodeCalls`, `TargetNodeCalls.lean`);
* the tables (`stageBlockTables`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape BlockParts MemberShape BinderMeta RecRule TargetMajor NestCtx PosTree fueledOps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The recursors' stage -/

/-- **The class tie**: at a nested stage's context, every
choice of the outside classes' data and every prefix spine, a node
presentation (`TgtNodePres`) over the positivity derivation's node list —
the chosen constructors' forests (`nestedRecCtx_nodes`), their keys read
(`NodeListFacts.sp`: `memberCtor_nodesSem` at the formers' model, lifted to
the occurrence and moved across the constructors' conses) — whose
dynamic part is the admissible frames `nodeAdm` (`dyn_hAdm`, `dyn_top`,
`dyn_trans`, at a prefix spine some class is guarded at: the guard fits
the block's parameters, `tgtGuard_params`) with the calls
(`nestedNodeCalls`), and which covers every guarded class, outside
majors included (`TgtNodeHex`). -/
theorem nestedClassNodes (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {nodesR : ConLeche.NestNodes}
    (hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      nodesR)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind)
    (hleg : ConLeche.targetLegacyAux pp.toBlockShape (out.map (·.2.1)) nodesR = some nodesR)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∃ P : TgtNodePres μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type))
      out dR Dc mc cvc ψ ρ xs (fun _ => True), TgtNodeHex P := by
  -- the node list
  have hctx' := hctx
  obtain ⟨hRec, -, -, hnames, -, -, -, -, -, hdR, hlfp, hcov,
    ⟨mk, hmkC, hmk, hag, hsubC, hcoreK, htr⟩, -⟩ := hctx'
  obtain ⟨fvsP, ns, hok, hown, hkids, hpar, hsem, hfrec, hmemF, ⟨par, hPP⟩, hcovN⟩ :=
    nestedRecCtx_nodes hμ hctx mk hmkC hcoreK hleg
  have hsp : ∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
      ((pp.nestCtx fvsP envI.find? envI.consts).nP
        + (nodeHoleConsts (pp.nestCtx fvsP envI.find? envI.consts) t.occ).length) t.key.ds dsa := by
    intro t ht ψ
    obtain ⟨dsa, hdsa⟩ := nodeSem_spOcc (hok t ht) (hsem t ht ψ)
    exact ⟨dsa, DenoteMetaSpine.transport (fun e _ he => htr ψ _ e he) hdsa⟩
  have hF := nodeListFacts_of hctx hok hown hsp
  by_cases hgd : ∃ c, c < (tgtRs out).length ∧
      tgtClsG dR mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
  case neg => exact ⟨TgtNodePres.empty, fun c hc hg => absurd ⟨c, hc, hg⟩ hgd⟩
  -- the dynamic part: the admissible frames and the calls
  have H := dynCtx_of hctx hmkC hmk hag hsubC htr hcoreK hok hown hkids hpar hsem hF
  have hparams := tgtGuard_params hμ hctx hgd.choose_spec.1 hgd.choose_spec.2
  have hxs : dR.nP ≤ xs.length := by
    have hl := SpineFit.length_eq hparams
    have hpl : (dR.params ψ).length = dR.nP := by
      have h0 := H.hΔ0 ψ
      rw [List.length_reverse, BlockData.holeCtx, List.length_append, List.length_map,
        List.length_range] at h0
      have hk : dR.k = (pp.nestCtx fvsP envI.find? envI.consts).names.length := by
        rw [H.hnames]; exact (lfp_namesLen mpC H.hd0).symm
      have hnP := H.hnP
      simp only [ConLeche.NestCtx.hiAt] at h0
      omega
    rw [List.length_take, hpl] at hl
    omega
  have Dy : TgtNodeDyn μ F mpC (pp.nestCtx fvsP envI.find? envI.consts) dR pp.toBlockShape
      (cvTasR.map (·.type)) out Dc mc cvc ns ψ ρ xs (fun _ => True) (fun _ _ => True) := {
    Adm := nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par
    hAdm := dyn_hAdm H ψ ρ xs hparams par
    top := dyn_top H ψ ρ xs hparams hxs hPP
    trans := dyn_trans H ψ ρ xs hparams hxs par
    hcall := nestedNodeCalls hμ hctx hmkC hmk hag hsubC htr hcoreK hok hown hkids hpar hsem hfrec
      hmemF hPP hF hcls hsel hgd hleg }
  -- the class tie at every related pair, read off the stage's run
  obtain ⟨R⟩ := ConLeche.targetRecCheck_run
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have hS := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  have hrs : ∀ c (hc : c < (tgtRs out).length),
      (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := fun c hc => List.getElem?_eq_getElem hc
  refine tgtNodePres_of_list_hex hcov hlfp hF hcls hsel (fun c hc => ?_) (fun c hc =>
      blockRulePdomsAV_length hμ mpC hS (hrs c hc) ψ) (fun c hc hm => ?_) (fun c hc => ?_) Dy
    (fun c hc hM _ => hcovN c hc hM)
  · -- the prefix holds the parameters
    obtain ⟨-, hlen, hall⟩ := ConLeche.recStageG_recNames hS
    obtain ⟨_, _, _, _, -, -, hle, -⟩ := hall c (by rw [← hlen]; exact hc)
    exact hle
  · -- a member class's component is a member
    obtain ⟨ms, hms, -, -⟩ := recStage_ctorsAt (hm := tgtMemAt_of_member hc hm) hS (hrs c hc)
    have hk : pp.toBlockShape.recTgtAt c < dR.toLfp.k := by
      obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
      exact (List.getElem?_eq_some_iff.mp hms).1
    exact Nat.lt_of_lt_of_le hk (mpC.lfpClause_of_mem hlfp).kN
  · -- the carried constructors are the class's
    unfold blockRecNCt
    rw [List.getD_eq_getElem?_getD, hrs c hc, Option.getD_some]
    by_cases hm : (tgtMajor out c).member.isSome = true
    · simp only [tgtClsD, tgtClsM, hm, if_true]
      rw [← tgtCls_hctM hS hdR c _ (tgtMemAt_of_member hc hm) (hrs c hc)]
      rfl
    · have hMo : (tgtMajor out c).member = none := by
        cases h' : (tgtMajor out c).member with
        | none => rfl
        | some _ => rw [h'] at hm; exact absurd rfl hm
      have hm' : (tgtMajor out c).member.isSome = false := by rw [hMo]; rfl
      simp only [tgtClsD, tgtClsM, hm', Bool.false_eq_true, if_false]
      rw [tgtRs_ctors (hrs c hc)]
      exact (hcls c hc hMo).hlen

/-- **THE RECURSORS' STAGE**: at a nested stage's
context, the four cons-monotonicities at the cons at the majors
(`BlockRecStagedT`).  The stage record at any majors
(`recStage_of_targetG`), the cons at the majors as the generic one
(`consBlockRecsT_eq_R`) with its rules' shape (`recRulesShape_tgt`) and the
`.nested` firings' guards (`tgtFireOf_nested`), the per-recursor bounds,
the outside classes' data (`tgtOutCls_of`, chosen), and the family
premise: its type half (`blockRecLevel_run`), its equation half
(`tgtRecEqs_hEqAny`) and its CANDIDATE from the class induction
(`tgtRecPre_clsI` over `nestedClassNodes`).  Further: the
family's names distinct (`recStageG_nodup`), the `.nested` pins free of
empty slots (`tgtFire_pinsNoProj`) and their law (`tgtRecPinsOk`), the
carried constructors stored and read (`tgtRecCtor_in`, `tgtRecCtor_seam`),
the equations' level-parametricity and bound (`blockRecEqs_params_rows`,
`blockRecEqs_below_rows`) and bit validity (`tgtRecEqs_validAny`), the
rules' λ-tower (`tgtRuleTower_run`), the `ℓ = 0` arm (`blockRecTyZ_run`,
`tgtRuleRaZ_seam`), and the rule contract at every fired pair
(`tgtRecDataB`). -/
theorem nestedRecStage (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {nodesR : ConLeche.NestNodes}
    (hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      nodesR) :
    BlockRecStagedT (V := V) μ envC pp.toBlockShape out mpC := by
  have hctx' := hctx
  obtain ⟨hRec, hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov, hmk,
    hover⟩ := hctx'
  obtain ⟨R⟩ := ConLeche.targetRecCheck_run
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have h := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  -- the family's level, chosen by the check's inferred sorts
  obtain ⟨s, hsP, hTy⟩ := blockRecLevel_run (V := V) (mpC := mpC) hμ h
  -- the outside classes' data, chosen
  have hcls0 : ∀ c, ∃ t : Nat × ConstantVal,
      c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (lfpSel mpC dR.toLfp (tgtMajor out c).ind) t.1 t.2 := by
    intro c
    by_cases hc : c < (tgtRs out).length
    · by_cases hm : (tgtMajor out c).member = none
      · obtain ⟨r, hr⟩ : ∃ r, (tgtRs out)[c]? = some r := ⟨_, List.getElem?_eq_getElem hc⟩
        obtain ⟨rc, cvRi, M, u, rhssA, -, -, ho, -, -, -, ⟨E⟩⟩ := ConLeche.targetRecRun_at R hr
        have hM : tgtMajor out c = M := by
          simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
        rw [hM] at hm ⊢
        obtain ⟨mm, cvI, hD⟩ := tgtOutCls_sel hcov dR.toLfp E hm
        exact ⟨(mm, cvI), fun _ _ => hD⟩
      · exact ⟨(0, default), fun _ h' => absurd h' hm⟩
    · exact ⟨(0, default), fun h' => absurd h' hc⟩
  obtain ⟨tc, hcls⟩ := Classical.axiomOfChoice hcls0
  -- the family premise: its type and equation halves, its candidate
  -- from the class induction
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  -- the outside classes' blocks, canonically selected
  let DS : Nat → LfpDatum V := fun c =>
    lfpSel mpC (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).toLfp (tgtMajor out c).ind
  have hmr := blockMembersRun_seam hN hS hcore
  have hmemT : ∀ c, (tgtMajor out c).member.isSome = true → ConLeche.tgtMemAt out c := by
    intro c hc
    cases ho : out[c]? with
    | none => simp [ConLeche.tgtMemAt, ho]
    | some t =>
      simp only [tgtMajor, List.getD_eq_getElem?_getD, ho, Option.getD_some] at hc
      simp [ConLeche.tgtMemAt, ho, hc]
  have hM := blockModelAt_seam h hN hS hcore hlfp
  have hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
        (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ') ψ) ρ := by
    intro ψ ρ
    refine ⟨fun c hc => hTy ψ ρ c hc,
      tgtRecEqs_hEqAny hμ hcov h R (Dc := DS) (mc := fun c => (tc c).1)
        (cvc := fun c => (tc c).2) (fun c hc hm => hcls c hc hm) hN hS hcore hctorsAs hmr hM
        hmemT ψ ρ, ?_⟩
    -- the class induction: walk-free on the route (`tgtClassInd_of_flat`:
    -- an acyclic call graph, or cycles only inside flat outside homes),
    -- else from the positivity walk's nodes
    have hind : TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type)) out
        (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf) DS (fun c => (tc c).1)
        (fun c => (tc c).2) ψ ρ := by
      by_cases hfl : ConLeche.targetFlatRouteOf pp.toBlockShape (out.map (·.2.1)) = true
      · exact tgtClassInd_of_flat hμ hcov h R (fun c hc hm => hcls c hc hm) (fun _ _ _ => rfl)
          ⟨pk, uOfD, ppsOf, rfl⟩ hS hcore hmr hM hlfp hfl ψ ρ
      · have hleg : ConLeche.targetLegacyAux pp.toBlockShape (out.map (·.2.1)) nodesR
            = some nodesR := by
          unfold ConLeche.targetLegacyAux; rw [if_neg hfl]
        exact tgtClassInd_of_pres (nestedClassNodes hμ hctx (fun c hc hm => hcls c hc hm)
          (fun _ _ _ => rfl) hleg ψ ρ)
    obtain ⟨a, ha, hb⟩ := tgtRecPre_clsI hμ hcov h R
      (Dc := DS) (mc := fun c => (tc c).1) (cvc := fun c => (tc c).2)
      (fun c hc hm => hcls c hc hm) ⟨pk, uOfD, ppsOf, rfl⟩ hN hS hcore hmr hM hndM ψ ρ
      hind
    refine ⟨a, ha, fun e he => hb e ?_⟩
    rw [tgtClsEqs_eq hμ h ψ]
    exact he
  unfold BlockRecStagedT
  rw [ConLeche.consBlockRecsT_eq_R]
  exact blockRecStaged_dataR hμ mpC h (ConLeche.recStageG_nodup h hndM)
    (ConLeche.recRulesShape_tgt envC.find? (·.constsResolve envC) pp.toBlockShape out)
    (fun j r hr lvls pins hf => by
      obtain ⟨n1, n2, n3, n4⟩ := ConLeche.tgtFireOf_nested hf
      exact ⟨n1, n2, fun pin hpin => ⟨(n3 pin hpin).1, (n3 pin hpin).2.1,
        (n3 pin hpin).2.2.1, (n3 pin hpin).2.2.2,
        tgtFire_pinsNoProj h j r hr lvls pins hf pin hpin⟩, n4⟩)
    (tgtRecCtor_in R hN hcore hctorsAs hcov)
    (blockRecEqs_below_rows hμ h (tgtRowB hμ R hN hcore hctorsAs hcov (tgtFormer_facts (fe := ConLeche.mkFEnv envC) hmr) h
      hmemT)) (tgtRecEqs_validAny hμ hcov h R hN hS hcore hctorsAs hmr hmemT)
    (fun i r hr ψ₁ ψ₂ hq => ⟨hsP i r hr ψ₁ ψ₂ hq,
      blockRecEqs_params_rows hμ h (fun c r hr j cA rhs hcA hrhs ψ₁ ψ₂ hq => by
        obtain ⟨e1, e2, e3⟩ := tgtRow_params hμ R hN hcore hctorsAs hcov h hr hcA hrhs hq
        obtain ⟨e4, e5⟩ := tgtRule_params (fe := ConLeche.mkFEnv envC) mpC.base2 h R hr hcA hrhs hq
        exact ⟨e1, e2, e4, e3, e5⟩) i r hr ψ₁ ψ₂ hq⟩) hpre
    (fun j r hr => blockRecNCt_ge hr)
    (fun ψ j r hr => blockRulePdomsAV_length hμ mpC h hr ψ)
    (tgtRecCtor_seam R hN hcore hctorsAs hcov)
    (fun j r hr i cA rhs hcA hrhs _ acv ψ Ra hRa =>
      tgtRuleTower_run R j r hr i cA rhs hcA hrhs acv _ ψ Ra hRa)
    (fun m₃ hac φ j r hr _ cA rhs _ _ => tgtRecPinsOk hμ mpC hcov h R m₃ hac φ j r hr cA rhs)
    (tgtRecDataB hμ hcov h R hndM hN hS hcore hctorsAs hlfp hmemT
      (blockRecEqs_below_rows hμ h (tgtRowB hμ R hN hcore hctorsAs hcov
        (tgtFormer_facts (fe := ConLeche.mkFEnv envC) hmr) h hmemT))
      (tgtRecEqs_validAny hμ hcov h R hN hS hcore hctorsAs hmr hmemT)
      (fun i r hr ψ₁ ψ₂ hq => ⟨hsP i r hr ψ₁ ψ₂ hq,
        blockRecEqs_params_rows hμ h (fun c r hr j cA rhs hcA hrhs ψ₁ ψ₂ hq => by
          obtain ⟨e1, e2, e3⟩ := tgtRow_params hμ R hN hcore hctorsAs hcov h hr hcA hrhs hq
          obtain ⟨e4, e5⟩ := tgtRule_params (fe := ConLeche.mkFEnv envC) mpC.base2 h R hr hcA
            hrhs hq
          exact ⟨e1, e2, e4, e3, e5⟩) i r hr ψ₁ ψ₂ hq⟩) hpre)
    (blockRecTyZ_run hμ mpC h)
    (fun j r hr i cA rhs hcA hrhs _ =>
      tgtRuleRaZ_seam (fe := ConLeche.mkFEnv envC) hμ h R hpre
        (tgtFdomsAV_length (fe := ConLeche.mkFEnv envC) h R _ _) j r hr i cA rhs hcA hrhs)

/-! ## The block step -/

/-- **THE UNIFORM BLOCK STEP** (#315): the
install's run from a covered carrier leaves a covered carrier.  The run's
nine conjuncts, one stage at a time: the formers' and the constructors'
stages (conjuncts ①②③⑥⑦, with the two freshness facts of conjunct ⑨
supplied here) with the operator's monotonicity and the fields' grading,
the constructors consed by `stageBlockCtors` (conjunct ②'s install half),
the recursors' stage `nestedRecStage` (conjunct ⑧), and the tables
`stageBlockTables` (conjunct ⑨).  The invariant that crosses all of it is
`BlockCtorsCore` → (at the recursors) `BlockTablesCore`. -/
theorem declBlock (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts}
    (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂) (hcov : LfpCover mp []) :
    ∃ mp' : EnvModelM V μ env₂, LfpCover mp' [] := by
  classical
  obtain ⟨hndC₀, hndM₀, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, kinds, nfs, nodes, isorts, outR,
    hInd, hp, hCtors, hPos, -, helim, hsorts, hRec, hTbl⟩ := hrun
  subst hp
  -- ## the recogniser's facts, moved to the shape the formers' stage completed
  obtain ⟨hshape, -⟩ := ConLeche.blockParts?_inv hdp
  obtain ⟨-, -, -, hmembersOk, -, hClps₀, -, -, -⟩ := ConLeche.blockShape?_inv hshape
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, hcvTas, hq, hcons, htele0, -, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  have hlps₀ : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps :=
    fun ms hms => (hmembersOk ms hms).1
  have hndM : p₁.memberNames.Nodup := by rw [hq]; exact hndM₀
  have hndC : (p₁.allCtors.map (·.1.name)).Nodup := by rw [hq]; exact hndC₀
  have hClps : ∀ c ∈ p₁.allCtors, c.1.levelParams = p₁.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false := by rw [hq]; exact hClps₀
  -- ## the formers' and the constructors' run, read positionally
  obtain ⟨ppsOf₀, sOf₀, hF⟩ := blockFormerFacts_of hμ mp hInd hlps₀
  obtain ⟨hlenCA, hlenSA, -⟩ := ConLeche.checkBlockCtors_inv hCtors
  have hkm : p₁.k = p₁.members.length := rfl
  have hlenCtorsAs : ctorsAs.length = p₁.k := by
    rw [hlenCA, List.length_zip, hF.lenCv, hkm]
    exact Nat.min_self _
  have hlenSortsss : sortsss.length = p₁.k := by
    rw [hlenSA, List.length_zip, hF.lenCv, hkm]
    exact Nat.min_self _
  -- ## the stored constructors are the recogniser's
  have hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = p₁.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) := by
    have hz : (p₁.members.zip cvTas).map Prod.fst = p₁.members :=
      List.map_fst_zip (Nat.le_of_eq (by rw [hF.lenCv]; rfl))
    rw [(ConLeche.Semantics.checkBlockCtors_names hCtors).1, ← hz, List.map_map]
    rfl
  have hmemCtors : ∀ (m : Nat), m < p₁.k →
      ∀ c ∈ (p₁.members.getD m default).ctors, c ∈ p₁.allCtors := by
    intro m hm c hc
    rw [ConLeche.BlockShape.allCtors, List.mem_flatten]
    refine ⟨_, List.mem_map.mpr ⟨_, ?_, rfl⟩, hc⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
    exact List.getElem_mem _
  have hfacts := fun (m : Nat) (cvTa : ConstantVal) (hm : m < p₁.k)
      (hcv : cvTas[m]? = some cvTa) =>
    blockCtorFacts_of (blockCtorRuns_of hCtors hF.nameOf m cvTa hm hcv)
      (fun c hc => hClps c (hmemCtors m hm c hc))
  -- ## the member name, read off the member list
  have hmnameEq : ∀ (m : Nat), m < p₁.k →
      p₁.memberNames.getD m .anonymous = (p₁.members.getD m default).cvT.name := by
    intro m hm
    rw [ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show m < p₁.members.length from hm),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
    rfl
  -- ## the tables' loop's entries, positionally
  have hzipEntry : ∀ (m : Nat), m < p₁.k →
      (p₁.members.zip (ctorsAs.zip sortsss))[m]?
        = some (p₁.members.getD m default, ctorsAs.getD m [], sortsss.getD m []) := by
    intro m hm
    have hc1 : ctorsAs[m]? = some (ctorsAs.getD m []) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenCtorsAs]; exact hm)]
      rfl
    have hs1 : sortsss[m]? = some (sortsss.getD m []) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenSortsss]; exact hm)]
      rfl
    have hm1 : p₁.members[m]? = some (p₁.members.getD m default) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
      rfl
    rw [List.getElem?_zip_eq_some]
    exact ⟨hm1, by rw [List.getElem?_zip_eq_some]; exact ⟨hc1, hs1⟩⟩
  -- ## conjunct ⑨'s two freshness facts, pulled back to the formers'
  -- environment (a name absent above a cons was absent below it)
  have hpull : ∀ n : Name,
      (ConLeche.consBlockRecsT (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        (·.constsResolve (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)) p₁ 0 outR
        (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)).find? n = none → env₁.find? n = none :=
    fun n h => find?_none_consBlockCtors (find?_none_consBlockRecsT h)
  have hfamFree : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < p₁.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (p₁.members.getD m default).nIdx = 0 → 0 < cA.2 →
      env₁.find? (projFnName (p₁.memberNames.getD m .anonymous) 0) = none := by
    intro m cA sorts hm hcA hs hn0 hpos
    rw [hmnameEq m hm]
    exact hpull _ (blockTablesFamFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
      hTbl m _ (hzipEntry m hm) cA sorts hcA hs hn0 hpos)
  have hprojTbl : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < p₁.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (p₁.members.getD m default).nIdx = 0 →
      env₁.find? (projTableName (p₁.memberNames.getD m .anonymous)) = none := by
    intro m cA sorts hm hcA hs hn0
    rw [hmnameEq m hm]
    exact hpull _ (blockTablesTblFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
      hTbl m _ (hzipEntry m hm) cA sorts hcA hs hn0)
  -- ## the formers' and the constructors' stage
  obtain ⟨pk, uOf, ppsOf, mpI, hN, hS, hcore, hEtaI, hfreshC, hnfs, hagI⟩ :=
    blockTablesStage_of hμ mp hE hlps₀ hndM hndC hClps hInd hCtors hsorts
      hPos rfl rfl rfl rfl rfl hfamFree hprojTbl hcov
  have hlenN : p₁.memberNames.length = p₁.k := by
    show (p₁.members.map _).length = _; simp; rfl
  have hcvOfK : ∀ m, m < p₁.k → ∃ cvTb, cvTas[m]? = some cvTb :=
    fun m hm => ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hm)⟩
  have hmemCv : ∀ cvTb ∈ cvTas, env.find? cvTb.name = none := by
    intro cvTb hcvTb
    obtain ⟨m, hm⟩ := List.getElem?_of_mem hcvTb
    exact hF.freshOf m cvTb hm
  -- the formers' model: the input's clauses, the members exempt, `mpI`'s leaves
  have hformers : ∃ mk : EnvModelM V μ env₁, mk.base2 = mpI.base2 ∧
      mk.lfpBlocks = mp.lfpBlocks ∧ LfpCover mk p₁.memberNames :=
    lfpCover_formers mp hcons mpI hmemCv hagI (names := p₁.memberNames)
      (fun cvTb hcvTb => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
        have htk : t < p₁.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hF.lenCv] at this
        rw [hF.nameOf t cvTb ht]
        exact getD_mem _ (by rw [hlenN]; exact htk))
      (fun n hn => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hn
        have htk : t < p₁.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hlenN] at this
        obtain ⟨cvTb, hcv⟩ := hcvOfK t htk
        have hname := hF.nameOf t cvTb hcv
        rw [List.getD_eq_getElem?_getD, ht] at hname
        rw [← show cvTb.name = n from hname]
        exact hF.freshOf t cvTb hcv) hcov
  have hctorsAt : ∀ c, c < p₁.k → ctorsAs[c]? = some (ctorsAs.getD c []) := fun c hc => by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenCtorsAs]; exact hc)]
    rfl
  have hkD : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k
      = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length := by
    simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
      ConLeche.BlockShape.memberNames]
  -- the operator's MONOTONICITY is positivity's: every constructor positive
  -- along the tuple order at the hole frame (at the formers' carrier)
  have hposI := fun hclosed => blockCtorPos_of_run hμ mpI hN hcore.holeCtx hPos rfl rfl rfl rfl
    hkD rfl hlenCtorsAs hctorsAt hclosed hnfs
    (hformers.imp fun _ h => ⟨h.1, h.2.2⟩)
  -- ## the constructors, consed
  have hctorsAs : ∀ c, c < ctorsAs.length →
      ctorsAs[c]? = some ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c) := by
    intro c hc
    show ctorsAs[c]? = some (ctorsAs.getD c [])
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    rfl
  obtain ⟨mpC₀', hEtaC, hcoreC', hagC⟩ :=
    stageBlockCtors hμ hN hN.2.2 hS.toBlockCtorsStage hlenCtorsAs hctorsAs ctorsAs 0 env₁ mpI
      (fun c => by rw [Nat.zero_add]) (Nat.zero_add _) hEtaI hcore
      (fun c _ j cA hj => hfreshC c j cA hj)
  -- ## coverage across the formers' and the constructors' conses:
  -- the stage's carrier, rebuilt with the input's recorded list; the block's
  -- members pending
  -- every constructor's result head is its member (the check's `is_valid_ind_app`)
  have hheadK : ∀ m, m < p₁.k → ∀ cA ∈ ctorsAs.getD m [], ∃ bs body us,
      cA.1.type.stripPis (p₁.nP + cA.2) = some (bs, body) ∧
      body.getAppFn = .const ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m) us := by
    intro m hm cA hcA
    obtain ⟨cvTa, hcv⟩ := hcvOfK m hm
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨c, sorts, -, -, -, -, -, -, -, -, -, -, -, hCtor⟩ := (hfacts m cvTa hm hcv).2 j cA hj
    obtain ⟨-, ⟨cbs, es, hs, -⟩, -⟩ := ConLeche.checkSumCtor_shape hCtor
    exact ⟨cbs, _, List.map Level.param (p₀.complete p₁).lps, hs, by
      rw [getAppFn_mkAppN_const, hN.1 m cvTa hcv]⟩
  -- every constructor concludes in its member at `nP + nIdx` arguments
  have hshapeK : ∀ m, m < p₁.k → ∀ cA ∈ ctorsAs.getD m [], ∃ bs args,
      cA.1.type.stripPis ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP + cA.2)
        = some (bs, Expr.mkAppN (.const ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m)
            (cA.1.levelParams.map .param)) args) ∧
      ∀ ψ, args.length = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP
        + ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).IdsM m ψ).length := by
    intro m hm cA hcA
    obtain ⟨cvTa, hcv⟩ := hcvOfK m hm
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨c, sorts, -, -, -, hlpsA, -, -, -, -, -, -, -, hCtor⟩ :=
      (hfacts m cvTa hm hcv).2 j cA hj
    obtain ⟨-, ⟨cbs, es, hs, hes⟩, -⟩ := ConLeche.checkSumCtor_shape hCtor
    refine ⟨cbs, ConLeche.structPsAt cA.2 p₁.nP ++ es, ?_, fun ψ => ?_⟩
    · rw [hN.1 m cvTa hcv, hlpsA]; exact hs
    · have hlen := (hcoreC'.1 m cvTa hcv).2.2.2.len ψ
      have hIds : ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).IdsM m ψ).length
          = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt m := by
        show (((ppsOf m ψ).drop p₁.nP).map (·.2.2)).length = _
        rw [List.length_map, List.length_drop]
        have : (ppsOf m ψ).length
            = p₁.nP + (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt m := hlen
        omega
      rw [hIds, List.length_append, hes]
      simp [ConLeche.structPsAt]
      rfl
  obtain ⟨newI, hnewI, hnewIall⟩ :=
    consBlockInds_consts (p₁ := p₁) (isRec := isRec) cvTas 0 env
  have henv₁ : env₁.consts = newI ++ env.consts := by rw [hcons]; exact hnewI
  have hnewC : ∀ c ∈ (ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse,
      ∃ m cA, m < p₁.k ∧ cA ∈ ctorsAs.getD m [] ∧ c = .ctorInfo cA.1 p₁.nP cA.2 := by
    intro c hc
    obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
    obtain ⟨l, hl, hcAl⟩ := List.mem_flatten.mp hcA
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hl
    refine ⟨m, cA, by rw [← hlenCtorsAs]; exact hm, ?_, rfl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
    exact hcAl
  obtain ⟨mpC₀, hbC, hlC, hcovC⟩ := lfpCover_append (ex := []) (ex' := cvTas.map (·.name)) mp mpC₀'
    (new := (ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse ++ newI)
    (by rw [consBlockCtors_consts, henv₁, List.append_assoc]; rfl)
    (fun n ci hf => by
      have hfr : ∀ c ∈ (ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse
          ++ newI, env.find? c.name = none := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨m, cA, hm, hcA, rfl⟩ := hnewC c hc
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
          exact consBlockInds_find?_none (hcons ▸ hfreshC m j cA hj)
        · obtain ⟨cv, hcv, j, rfl⟩ := hnewIall c hc
          exact hmemCv cv hcv
      show List.find? _ _ = _
      rw [consBlockCtors_consts, henv₁, ← List.append_assoc]
      exact find?_append_of_fresh hfr hf)
    (fun c hc tbl h => by
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨m, cA, -, -, rfl⟩ := hnewC c hc; exact nomatch h
      · obtain ⟨cv, -, j, rfl⟩ := hnewIall c hc; exact nomatch h)
    (fun n hn => by
      have hnI : (env₁.find? n).isSome = true := by
        rw [hcons]; exact consBlockInds_find?_isSome_mono cvTas 0 env n hn
      rw [hagC n hnI]
      exact hagI n fun cvTb hcvTb h => by
        rw [h, hmemCv cvTb hcvTb] at hn; exact nomatch hn)
    (fun _ h => nomatch h)
    (fun n hn => by
      obtain ⟨cvTb, hcvTb, rfl⟩ := List.mem_map.mp hn
      exact Or.inr (hmemCv cvTb hcvTb))
    (fun c hc cv caps h => by
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨m, cA, -, -, rfl⟩ := hnewC c hc; exact nomatch h
      · obtain ⟨cv', hcv', j, rfl⟩ := hnewIall c hc
        exact List.mem_map.mpr ⟨cv', hcv', rfl⟩)
    (fun c hc C hC => by
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨m, cA, hm, hcA, rfl⟩ := hnewC c hc
        obtain ⟨bs, body, us, hs, hg⟩ := hheadK m hm cA hcA
        rw [ctorEntry_head rfl hs hg hC]
        obtain ⟨cvTa, hcv⟩ := hcvOfK m hm
        rw [hN.1 m cvTa hcv]
        exact Or.inr (Or.inl (hF.freshOf m cvTa hcv))
      · obtain ⟨cv', -, j, rfl⟩ := hnewIall c hc
        simp [ctorEntry] at hC)
  have hcoreC : BlockCtorsCore mpC₀.base2 (blockDataOf V p₁ ctorsAs pk uOf ppsOf) p₁.lps cvTas
      p₁ isRec (blockLeafH (blockDataOf V p₁ ctorsAs pk uOf ppsOf))
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
    rw [hbC]; exact hcoreC'
  -- ## the block's LFP CLAUSE, recorded at the constructors' environment
  -- the representation is built from the stages' three
  -- records (`blockModelAt_of_records`) and its `functor`/`fibre`/`leaf`
  -- enter the invariant (`EnvModelM.addLfp`), so the recursor stage
  -- below — and every later environment — carries it
  have hk0 : 0 < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
    rw [← hN.2.2, hcvTas]; exact Nat.succ_pos _
  -- the operator's MONOTONICITY is positivity's: every
  -- constructor positive along the tuple order at the hole frame, from the
  -- positivity stage's run at the formers' environment (conjunct 3)
  -- the constructors' types are closed (stored in a well-formed environment)
  have hclosedC : ∀ (c j : Nat) (cA : ConstantVal × Nat),
      ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j]? = some cA →
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true := by
    intro c j cA hj
    have hck : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
      rw [← hN.2.2]; exact hN.2.1 c j cA hj
    have hf := (hcoreC.2.2.2 c hck j cA hj).1
    have hw := mpC₀.base2.wf _ (List.mem_of_find?_eq_some hf)
    exact ⟨hw.1, hw.2.2.2.1⟩
  have hposC := hposI
    (fun c j cA hj => by
      have hck : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
        rw [← hN.2.2]; exact hN.2.1 c j cA hj
      have hf := (hcoreC.2.2.2 c hck j cA hj).1
      have hw := mpC₀.base2.wf _ (List.mem_of_find?_eq_some hf)
      exact ⟨hw.1, hw.2.2.2.1⟩)
  have hMC := blockModelAt_of_records hN hS.toBlockCtorsStage hcoreC rfl hk0
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (blockMono_of_pos hN hS.toBlockCtorsStage hcoreC hk0 (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      hposC) (blockFitsMono_of_pos hposC)
  have hLC := blockLfpClause_of_records hN hS.toBlockCtorsStage hcoreC rfl hk0
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) hposC
    -- the fields with holes are small at a `Type`-valued block (the grading)
    (fun ψ ρp hs _ X hX c hc j hj =>
      ((blockHoleGrade_of_run hμ mpI hN hcore.holeCtx hPos rfl rfl rfl rfl rfl hkD rfl hctorsAt
        hlenCtorsAs hclosedC hnfs ψ hc hj).2 ρp hs X hX).1)
  have hstC : LfpStored (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp := by
    refine ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩
    · obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hmm)⟩
      have hname := hN.1 mm cvTb hcv
      exact ⟨cvTb, _, by
        show (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
          ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName mm) = _
        rw [hname]; exact (hcoreC.1 mm cvTb hcv).1⟩
    · have hck : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
        have : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k + 0 := hc
        omega
      have hcj : ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j]?
          = some ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j] :=
        List.getElem?_eq_getElem hj
      refine ⟨((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j].1,
        (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP,
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j].2, ?_⟩
      show (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        (((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c).getD j default).1.name
          = some (.ctorInfo ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j].1
              (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP
              ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j].2)
      rw [List.getD_eq_getElem?_getD, hcj, Option.getD_some]
      exact (hcoreC.2.2.2 c hck j _ hcj).1
  -- each member's stored type reads as its hole telescope
  have hrdC : LfpReads mpC₀.base2.acval (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp := by
    intro mm hmm
    obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hmm)⟩
    have hname := hN.1 mm cvTb hcv
    obtain ⟨hfind, -, -, hFD⟩ := hcoreC.1 mm cvTb hcv
    refine ⟨cvTb, _, by
      show (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName mm) = _
      rw [hname]; exact hfind, fun ψ => ⟨_, hFD.read ψ, ?_, hFD.bits ψ⟩⟩
    show _ = (((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ppsM mm ψ).take
        (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP).map (·.2.2) ++
      (((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ppsM mm ψ).drop
        (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP).map (·.2.2)
    rw [← List.map_append, List.take_append_drop]
  -- each constructor reads as its hole telescope, canonically
  have hkLen : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k
      = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length := by
    simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
      ConLeche.BlockShape.memberNames]
  have hcrC : LfpCtorReads mpC₀.base2.acval (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp :=
    blockCtorReads_of hN hcoreC hkLen
      (fun c cvTb hc hcv => hS.toBlockCtorsStage.lpsT c cvTb hc hcv)
      (fun c j cA hj => by
        have hck : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
          rw [← hN.2.2]; exact hN.2.1 c j cA hj
        have hf := (hcoreC.2.2.2 c hck j cA hj).1
        exact (mpC₀.base2.wf _ (List.mem_of_find?_eq_some hf)).1)
      (canonOcc_of_positivity hPos rfl rfl hkLen
        (fun c hc => hctorsAs c (by rw [hlenCtorsAs]; exact hc)))
      (fun c hc j cA hj ψ ρ hsat =>
        ((hS.toBlockCtorsStage.frames c hc j cA hj).1 ψ ρ).mp
          (hS.toBlockCtorsStage.paramsOf 0 hk0 ψ ρ hsat c hc))
  -- the block's large-elimination licence, recorded (the per-major guard
  -- of a LATER family eliminating out of this block, `LfpLicUniq`): the
  -- elimination restriction (conjunct 5) and the subsingleton criterion
  have hlicC : LfpLicUniq (ConLeche.consBlockCtors (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP
      ctorsAs env₁) (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp := by
    refine blockLfpLicUniq (lps := p₁.lps) hMC (fun mm hmm cv caps hf => ?_) ?_
      (fun mm hmm j cA hcj => ⟨(hcoreC.2.2.2 mm hmm j cA hcj).1,
        (hcoreC.2.2.2 mm hmm j cA hcj).2.1, (hcoreC.2.2.1 mm j cA hcj).2.2.1⟩)
      (fun mm hmm j cA hcj ψ σ =>
        ⟨fun hσ => ((hS.toBlockCtorsStage.frames mm hmm j cA hcj).1 ψ σ).mp
            (hS.toBlockCtorsStage.paramsOf 0 hk0 ψ σ hσ mm hmm),
          fun hσ => hS.toBlockCtorsStage.paramsOf mm hmm ψ σ
            (((hS.toBlockCtorsStage.frames mm hmm j cA hcj).1 ψ σ).mpr hσ) 0 hk0⟩)
      (fun mm hmm ψ => ?_)
    · obtain ⟨cvTb, hcv⟩ := hcvOfK mm hmm
      have hf' := (hcoreC.1 mm cvTb hcv).1
      rw [← hN.1 mm cvTb hcv] at hf'
      rw [show (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp.member mm
        = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName mm from rfl, hf'] at hf
      injection hf with hf; injection hf with hcv' hcaps
      rw [← hcaps]
      unfold ConLeche.blockCapsAt
      split <;> rfl
    · intro hlarge ψ hw
      rcases helim hlarge with hnz | ⟨hk2, hn2⟩
      · exact absurd hw (ConLeche.Level.isNeverZero_sound ψ _ hnz)
      · have hkk : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k = p₁.k := by
          simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
            ConLeche.BlockShape.memberNames]
        have hk2' : p₁.k < 2 := hk2
        have hn2' : p₁.numCtors < 2 := hn2
        refine ⟨by omega, fun mm => ?_⟩
        show (ctorsAs.getD mm []).length ≤ 1
        by_cases hmm : mm < ctorsAs.length
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hmm, Option.getD_some]
          have hl := congrArg (fun l => (l[mm]?).map List.length) hnames
          simp only [List.getElem?_map, List.getElem?_eq_getElem hmm, Option.map_some,
            List.length_map] at hl
          have hmk : mm < p₁.members.length := by rw [← hkm, ← hlenCtorsAs]; exact hmm
          rw [List.getElem?_eq_getElem hmk] at hl
          simp only [Option.map_some, List.length_map, Option.some.injEq] at hl
          rw [hl]
          exact Nat.le_trans (numCtorsOf_ge_of_mem (List.getElem_mem hmk)) (by
            show p₁.numCtors ≤ 1; omega)
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
          exact Nat.zero_le _
    · obtain ⟨cvTb, hcv⟩ := hcvOfK mm hmm
      obtain ⟨-, -, -, hFD⟩ := hcoreC.1 mm cvTb hcv
      rw [BlockData.IdsM, List.length_map, List.length_drop, hFD.len ψ]
      omega
  let mpC := mpC₀.addLfp (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp hLC hstC hrdC
    hcrC hlicC
  -- ## coverage at the block's record: the members leave the
  -- exemption list; the block owns its constructors
  have hlpsNd : p₁.lps.Nodup := by
    have h0 := checkBlockTele_nodup htele0
    rw [hlps₀ ms0 (by rw [hmem0]; exact List.mem_cons_self)] at h0
    rw [hq]; exact h0
  have hcovMpC : LfpCover mpC [] :=
    (hcovC hcov).addLfp_to _ _ _ _ _ _ hndM hkLen.symm
      (fun mm hmm cv caps hf => by
        obtain ⟨cvTb, hcv⟩ := hcvOfK mm hmm
        have hf' := (hcoreC.1 mm cvTb hcv).1
        rw [← hN.1 mm cvTb hcv] at hf'
        rw [show (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp.member mm
          = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName mm from rfl, hf'] at hf
        injection hf with hf; injection hf with hcv' hcaps
        rw [← hcaps, blockCapsAt_all]; rfl)
      (blockLfpOwn (d := blockDataOf V p₁ ctorsAs pk uOf ppsOf) (lps := p₁.lps)
        (consBlockCtors_consts p₁.nP ctorsAs env₁)
        (fun m hm => by
          rw [henv₁, List.filterMap_append]
          obtain ⟨cvTa, hcv⟩ := hcvOfK m hm
          have hnil : newI.filterMap
              (ctorEntry ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m)) = [] := by
            rw [List.filterMap_eq_nil_iff]
            intro c hc
            obtain ⟨cv', -, j, rfl⟩ := hnewIall c hc
            rfl
          rw [hnil, List.nil_append]
          exact ctorEntries_fresh mp.base2.wf (by rw [hN.1 m cvTa hcv]; exact hF.freshOf m cvTa hcv))
        hlenCtorsAs (fun _ => rfl) hndM hkLen.symm hheadK
        (fun m hm => by
          obtain ⟨cvTb, hcv⟩ := hcvOfK m hm
          refine ⟨cvTb, _, by rw [hN.1 m cvTb hcv]; exact (hcoreC.1 m cvTb hcv).1,
            blockCapsAt_nparams _ _ _, hF.lpsOf m cvTb hcv⟩)
        hlpsNd
        (fun ψ => by
          obtain ⟨cvTb, hcv⟩ := hcvOfK 0 hk0
          have hlen := (hcoreC.1 0 cvTb hcv).2.2.2.len ψ
          show (((ppsOf 0 ψ).take p₁.nP).map (·.2.2)).length = p₁.nP
          rw [List.length_map, List.length_take]
          have : (ppsOf 0 ψ).length
              = p₁.nP + (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt 0 := hlen
          omega)
        (fun c hc j cA hj => (hcoreC.2.2.2 c hc j cA hj).1) hshapeK)
      (by
        rw [List.filter_eq_nil_iff]
        intro n hn
        obtain ⟨cvTb, hcvTb, rfl⟩ := List.mem_map.mp hn
        obtain ⟨m, hm⟩ := List.getElem?_of_mem hcvTb
        have hmk : m < p₁.k := by
          rw [← hF.lenCv]; exact (List.getElem?_eq_some_iff.mp hm).1
        simp only [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
          Classical.not_not]
        rw [← hN.1 m cvTb hm]
        exact getD_mem _ (by
          show m < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length
          rw [← hkLen]; exact hmk))
  -- ## every member's projection slots, free at the constructors' environment
  have hnpEnvC : ∀ c, c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k →
      (∃ cA, (blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c = [cA]) →
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt c = 0 → ∀ j,
      NoProjEnv (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c) j := by
    intro c hc h1 h2 j
    obtain ⟨cvTa, hcv⟩ : ∃ cvTa, cvTas[c]? = some cvTa :=
      ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hc)⟩
    have hname : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c = cvTa.name :=
      (hF.nameOf c cvTa hcv).symm
    have h0 : NoProjEnv env
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c) j := by
      rw [hname]
      exact noProjEnv_of_fresh mp.base2.wf (hF.freshOf c cvTa hcv) j
    have h1' : NoProjEnv env₁
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c) j := by
      rw [hcons]
      refine noProjEnv_consBlockInds h0 (fun cvTb hcvTb => ?_)
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      exact hS.noProjT c t cvTb hc ht j
    refine noProjEnv_consBlockCtors h1' (fun ctorsA hl cA hcA => ?_)
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hl
    obtain ⟨jj, hjj⟩ := List.getElem?_of_mem hcA
    refine hS.noProjC c t jj cA hc h1 h2 ?_ j
    show (ctorsAs.getD t [])[jj]? = some cA
    rw [List.getD_eq_getElem?_getD, ht]
    exact hjj
  -- ## every member's projection TABLE is absent at the constructors'
  -- environment: the tables' stage checked it free above the
  -- recursors, and a name absent there was absent below them
  have hslotC : ∀ c, c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k →
      (∃ cA, (blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c = [cA]) →
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt c = 0 → ∀ j,
      (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).findProj?
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c) j = none := by
    intro c hc h1 h2 j
    obtain ⟨cA, hcA⟩ := h1
    have hck : c < p₁.k := hc
    have hcAs : ctorsAs.getD c [] = [cA] := by
      rw [List.getD_eq_getElem?_getD,
        hctorsAs c (by rw [hlenCtorsAs]; exact hck), hcA]
      rfl
    -- the member's sorts list is a singleton, because it is as long as
    -- its constructor list (`checkSumCtors_inv`)
    obtain ⟨sorts, hs⟩ : ∃ sorts, sortsss.getD c [] = [sorts] := by
      obtain ⟨-, -, hall⟩ := ConLeche.checkBlockCtors_inv hCtors
      obtain ⟨mc, hmc⟩ : ∃ mc, (p₁.members.zip cvTas)[c]? = some mc := by
        refine ⟨_, List.getElem?_eq_getElem ?_⟩
        rw [List.length_zip, hF.lenCv, hkm, Nat.min_self]
        exact Nat.lt_of_lt_of_eq hck hkm
      obtain ⟨ctorsA, sortss, hcs, hss, hsum⟩ := hall c mc hmc
      obtain ⟨hlc, hls, -⟩ := ConLeche.checkSumCtors_inv hsum
      have hlen1 : sortss.length = 1 := by
        rw [hls, ← hlc]
        have : ctorsA = ctorsAs.getD c [] := by
          rw [List.getD_eq_getElem?_getD, hcs]; rfl
        rw [this, hcAs]
        rfl
      match sortss, hlen1 with
      | [sorts], _ => exact ⟨sorts, by rw [List.getD_eq_getElem?_getD, hss]; rfl⟩
    have hn0 : (p₁.members.getD c default).nIdx = 0 := by
      rw [← blockNIdxs_getD (q := p₁) (j := c) (Nat.lt_of_lt_of_eq hck hkm)]
      exact h2
    have hfree := find?_none_consBlockRecsT
      (blockTablesTblFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
        hTbl c _ (hzipEntry c hck) cA sorts hcAs hs hn0)
    have hname : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c
        = (p₁.members.getD c default).cvT.name := hmnameEq c hck
    have hfree' : (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        (projTableName (p₁.members.getD c default).cvT.name) = none := hfree
    rw [hname, ConLeche.Env.findProj?, hfree']
  -- ## the block over the input environment
  have hover : BlockOverEnv (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
      (p₀.complete p₁).toBlockShape.memberNames := by
    show BlockOverEnv _ p₁.memberNames
    refine ⟨env, mp.base2.wf, fun n hn => ?_, fun n ci hf => ?_⟩
    · obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hn
      have hmk : m < p₁.k := by
        have : m < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length := hm
        rw [← hkLen] at this; exact this
      obtain ⟨cvTb, hcv⟩ := hcvOfK m hmk
      have hname : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m = cvTb.name :=
        hN.1 m cvTb hcv
      have hget : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m = p₁.memberNames[m] := by
        show p₁.memberNames.getD m .anonymous = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
        rfl
      show env.find? p₁.memberNames[m] = none
      rw [← hget, hname]
      exact hF.freshOf m cvTb hcv
    · have hcs : (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).consts
          = (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 p₁.nP c.2).reverse
            ++ (newI ++ env.consts) := by
        rw [consBlockCtors_consts, henv₁]
      unfold ConLeche.Env.find? at hf
      rw [hcs, List.find?_append, List.find?_append] at hf
      cases h1 : List.find? (fun x => x.name == n)
          (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 p₁.nP c.2).reverse with
      | some ci' =>
        rw [h1] at hf
        obtain rfl : ci' = ci := Option.some.inj hf
        have hmem := List.mem_of_find?_eq_some h1
        rw [List.mem_reverse, List.mem_map] at hmem
        obtain ⟨cA, hcA, rfl⟩ := hmem
        obtain ⟨l, hl, hcAl⟩ := List.mem_flatten.mp hcA
        obtain ⟨m, hm⟩ := List.getElem?_of_mem hl
        have hmk : m < p₁.k := by
          have := (List.getElem?_eq_some_iff.mp hm).1
          rw [hlenCtorsAs] at this; exact this
        have hgl : ctorsAs.getD m [] = l := by
          rw [List.getD_eq_getElem?_getD, hm]; rfl
        obtain ⟨bs, body, us, hs, hhd⟩ := hheadK m hmk cA (by rw [hgl]; exact hcAl)
        refine Or.inr (Or.inr ⟨cA.1, p₁.nP, cA.2, bs, body, us, _, rfl, hs, hhd, ?_⟩)
        exact getD_mem _ (by
          show m < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length
          rw [← hkLen]; exact hmk)
      | none =>
        rw [h1, Option.none_or] at hf
        cases h2 : List.find? (fun x => x.name == n) newI with
        | some ci' =>
          rw [h2] at hf
          obtain rfl : ci' = ci := Option.some.inj hf
          obtain ⟨cv, -, j, rfl⟩ := hnewIall _ (List.mem_of_find?_eq_some h2)
          exact Or.inr (Or.inl ⟨cv, _, rfl⟩)
        | none =>
          rw [h2, Option.none_or] at hf
          exact Or.inl hf
  -- ## the positivity model at the formers' environment: the input's clauses, the members exempt, `mpC`'s leaves
  have hmkI : FormersModelAt (V := V) env₁ (p₀.complete p₁).toBlockShape.memberNames mpC
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf) p₁.lps cvTas p₁ isRec := by
    obtain ⟨mk, hbk, hlk, hck⟩ := hformers
    have hagk : ∀ n, (env₁.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n := by
      intro n hn
      show mpC₀.base2.acval n = mk.base2.acval n
      rw [hbC, hbk]
      exact hagC n hn
    -- the constructors' conses keep every lookup (their names fresh at `env₁`)
    have hEq : ConLeche.consBlockCtors p₁.nP ctorsAs env₁
        = ⟨(ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse
            ++ env₁.consts⟩ := by
      rw [← consBlockCtors_consts]
    have hfrC : ∀ c ∈ (ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse,
        env₁.find? c.name = none := by
      intro c hc
      obtain ⟨m, cA, -, hcA, rfl⟩ := hnewC c hc
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
      exact hfreshC m j cA hj
    have hfwdC : ∀ (n : Name) (ci : ConstantInfo), env₁.find? n = some ci →
        (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find? n = some ci := by
      intro n ci hf
      rw [hEq]
      exact find?_append_of_fresh hfrC hf
    have hprojC : ∀ (sn : Name) (i : Nat), env₁.findProj? sn i = none →
        (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).findProj? sn i = none := by
      intro sn i h
      rw [hEq]
      exact findProj?_append_none (fun c hc tbl h' => by
        obtain ⟨m, cA, -, -, rfl⟩ := hnewC c hc; exact nomatch h') sn i h
    refine ⟨mk, hck, fun D hD => ?_, hagk, fun D hD => ?_, ?_, ?_⟩
    · rw [hlk, ← hlC] at hD
      exact List.mem_cons_of_mem _ hD
    · rcases List.mem_cons.mp hD with rfl | hD
      · exact Or.inl rfl
      · rw [hlC, ← hlk] at hD
        exact Or.inr hD
    · rw [hbk]; exact hcore.holeCtx
    · intro ψ dd e ea h
      refine denoteMeta_envExtend_mono_ok (fun hf => hfwdC _ _ hf)
        ⟨natLitSupported_mono_of_keep hfwdC, strLitSupported_mono_of_keep hfwdC⟩ hprojC dd e ?_
      rw [denoteMeta_acval_congr (env := env₁) (acval₂ := mk.base2.acval) hagk]
      exact h
  -- ## the recursors' stage, and the tables' invariant across it
  obtain ⟨mpR₀, hag, hfindMono, hden, hnpMono⟩ :=
    nestedRecStage (mpC := mpC) (A := blockLeafH (blockDataOf V p₁ ctorsAs pk uOf ppsOf)) hμ
      ⟨hRec, hPos, rfl, hnames, hndM, hN, hS.toBlockCtorsStage, hcoreC,
        fun c hc => hctorsAs c hc, ⟨pk, uOf, ppsOf, rfl⟩,
        EnvModelM.mem_addLfp mpC₀ _ hLC hstC hrdC hcrC hlicC, hcovMpC, hmkI, hover⟩
  have hcoreT :=
    (blockTablesCore_of hN hcoreC hnpEnvC).consRecs hag hfindMono hden hnpMono hslotC
  -- ## coverage across the recursors' conses: only recursors
  -- are stored, every old name keeps its leaf
  obtain ⟨newR, hnewR, hnewRall⟩ := consBlockRecsT_consts
    (find? := (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?)
    (res := (·.constsResolve (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)))
    (q := (p₀.complete p₁).toBlockShape) 0 outR
    (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
  obtain ⟨mpR, hbR, -, hcovR⟩ := lfpCover_append (ex := []) (ex' := []) mpC mpR₀ hnewR hfindMono
    (fun c hc tbl h => by obtain ⟨r, -, mI, rP, rules, rfl⟩ := hnewRall c hc; exact nomatch h)
    hag (fun _ h => h) (fun _ h => Or.inl h)
    (fun c hc cv caps h => by obtain ⟨r, -, mI, rP, rules, rfl⟩ := hnewRall c hc; exact nomatch h)
    (fun c hc C hC => by
      obtain ⟨r, -, mI, rP, rules, rfl⟩ := hnewRall c hc
      simp [ctorEntry] at hC)
  rw [← hbR] at hcoreT
  -- ## the tables
  suffices hT : CoverTo mpR [] env₂ [] by
    obtain ⟨mpF, hF'⟩ := hT
    exact ⟨mpF, hF' (hcovR hcovMpC)⟩
  refine stageBlockTables hN hS rfl rfl rfl (p₁.members.zip (ctorsAs.zip sortsss)) 0 _ env₂
    mpR ?_ hTbl hcoreT
  intro c e hce
  have hck : c < p₁.k := by
    have h := (List.getElem?_eq_some_iff.mp hce).1
    rw [List.length_zip, List.length_zip, hlenCtorsAs, hlenSortsss] at h
    simp only [Nat.min_self] at h
    rw [hkm]
    omega
  obtain rfl : e = (p₁.members.getD c default, ctorsAs.getD c [], sortsss.getD c []) :=
    Option.some.inj (hce.symm.trans (hzipEntry c hck))
  refine ⟨by rw [Nat.zero_add]; exact hck, ?_, ?_, ?_, ?_⟩
  · rw [Nat.zero_add]; exact (hmnameEq c hck).symm
  · rw [Nat.zero_add]
    show (p₁.members.getD c default).nIdx = p₁.nIdxs.getD c 0
    rw [blockNIdxs_getD (q := p₁) (j := c) (show c < p₁.members.length from hck)]
  · rw [Nat.zero_add]; rfl
  · intro sorts hss
    rw [Nat.zero_add]
    show sorts = (sortsss.getD c []).getD 0 []
    have hss' : sortsss.getD c [] = [sorts] := hss
    rw [hss']
    rfl

end ConLeche.Model
