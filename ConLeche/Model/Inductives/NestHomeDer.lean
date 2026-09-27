module

import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Model.Inductives.TargetRank
public import ConLeche.Model.Inductives.TargetFlatInd
import ConLeche.Model.Inductives.NestHomeNodes
import ConLeche.Model.Inductives.NestHomeWalk
import ConLeche.Model.Inductives.TargetNodeCalls
import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.TargetNodeSem
import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.TargetNodeCover
import ConLeche.Model.Inductives.TargetGuardParams
import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Model.Inductives.BlockRecData

public section

/-!
# A hot layer's derivations (PRIMREC / NESTHOME)

`homeLayer_der`: at a family on the route (`targetRouteOf`) and a hot
layer `n` of its call graph (`targetHot`) — its classes covered by the
home table — every element of a class of the layer has a derivation
along the calls inside the layer (`Der`), the lane's completeness fact,
consumed by `tgtClassInd_of_route` (`layerStep_of_der`).

The node route at the layer (`TgtNodePres` over the positivity
derivation's node list, `tgtNodePres_of_list`) with the layer as `S`
and the home table's node filter (`homeOkN`: a class related to the
empty-stack node at exactly the key the table recomputed it at): the
calls at the admissible frames (`nestedNodeCallsG`) from the table's
facts (`homeFacts_of`, `NestHomeCalls.lean`); every guarded class of
the layer is related (a member class at node `0`, an outside class at
its entry's node); the derivation is the presentation's recursion on
the nodes (`tgtDer_of_pres`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  NestCtx PosTree fueledOps)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A hot layer's derivations** (see the module docstring). -/
theorem homeLayer_der (hμ : μ.verifiedChecks = true) {F : Nat}
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
    (hroute : ConLeche.targetRouteOf pp.toBlockShape (out.map (·.2.1)) = true)
    (n : Nat) (hhot : ConLeche.targetHot pp.toBlockShape (out.map (·.2.1)) n = true)
    (ψ : Name → Nat) (ρ : Nat → V) :
    ∀ xs c, c < (tgtRs out).length → tgtRank pp.toBlockShape c = n →
      ∀ t, t ∈ˢ tgtClsIs dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c →
      ∀ y, y ∈ˢ app (tgtClsCr dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) t →
        Der (Is := tgtClsIs dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (Cr := tgtClsCr dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (injX := tgtClsInj dR Dc mc cvc pp.toBlockShape out ψ)
          (nCt := blockRecNCt (tgtRs out)) (K := (tgtRs out).length)
          (fit := tgtClsFit dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ)
          (call := tgtCall μ F (mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out
            mpC.base2.acval envC ψ (tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ) ρ)
          xs (fun c' => tgtRank pp.toBlockShape c' = n) (tagged c t y) := by
  classical
  intro xs c hc hrc t ht y hy
  have hg : tgtClsG dR mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c := by
    by_cases hg : tgtClsG dR mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
    · exact hg
    · rw [tgtClsIs_unguarded hg] at ht
      exact absurd ht (not_mem_empty t)
  -- the node list, at no coverage of the outside classes
  have hctx' := hctx
  obtain ⟨hRec, hPos, -, hnames, -, -, -, -, -, hdR, hlfp, hcov,
    ⟨mk, hmkC, hmk, hag, hsubC, hcoreK, htr⟩, -⟩ := hctx'
  obtain ⟨fvsP, ns, hok, hown, hkids, hpar, hsem, hfrec, hmemF, ⟨par, hPP⟩, -⟩ :=
    nestedRecCtx_nodes hμ hctx mk hmkC hcoreK (Lg := False) (fun h => h.elim)
  have hsp : ∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
      ((pp.nestCtx fvsP envI.find? envI.consts).nP
        + (nodeHoleConsts (pp.nestCtx fvsP envI.find? envI.consts) t.occ).length) t.key.ds dsa := by
    intro t ht ψ
    obtain ⟨dsa, hdsa⟩ := nodeSem_spOcc (hok t ht) (hsem t ht ψ)
    exact ⟨dsa, DenoteMetaSpine.transport (fun e _ he => htr ψ _ e he) hdsa⟩
  have hF := nodeListFacts_of hctx hok hown hsp
  -- the dynamic part
  have H := dynCtx_of hctx hmkC hmk hag hsubC htr hcoreK hok hown hkids hpar hsem hF
  have hparams := tgtGuard_params hμ hctx hc hg
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
  -- the recursor check's run, the positivity stage's table
  obtain ⟨R, hRaux⟩ := ConLeche.targetRecCheck_run_aux
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have hμv := ConLeche.CheckMode.eq_verified hμ
  subst hμv
  obtain ⟨cvTa0', fvsP', rest', holes', st, homes, hcv', hop', hholes', -, -, htab, hnodes⟩ :=
    ConLeche.checkBlockPositivity_split hPos
  have hmemF' := hmemF
  obtain ⟨cvTa0, rest, holes, hcv0, hop0, hholes0, hMF⟩ := hmemF'
  rw [hcv0] at hcv'
  obtain rfl := Option.some.inj hcv'
  rw [hop0] at hop'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using hop'
  rw [hholes0] at hholes'
  obtain rfl := Option.some.inj hholes'
  have hW := homeWalk_of hmkC hok hkids hMF
  have hpar0 : ∀ x ∈ (pp.nestCtx fvsP envI.find? envI.consts).params,
      ∃ i ty, x = .fvar i ty ∧ i < (pp.nestCtx fvsP envI.find? envI.consts).nP := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨ty, hty⟩ := ConLeche.openPisAtFvars_index _ _ _ hop0 i _ (List.getElem?_eq_getElem hi)
    refine ⟨i, ty, by rw [hty, Nat.zero_add], ?_⟩
    have := ConLeche.Verify.openPisAtFvars_length _ hop0
    show i < pp.nP
    have hi' : i < fvsP.length := hi
    omega
  have htab' : ConLeche.homeTableAt (fueledOps .verified F) envI
      (pp.nestCtx fvsP envI.find? envI.consts) holes ctorsAsR st.nodes.size = .ok R.aux.homes := by
    rw [hRaux, hnodes]; exact htab
  have HF := homeFacts_of R hroute hhot hW hholes0 hpar0 rfl rfl rfl htab'
  -- the presentation at the layer, the table's node filter
  have Dy : TgtNodeDyn .verified F mpC (pp.nestCtx fvsP envI.find? envI.consts) dR pp.toBlockShape
      (cvTasR.map (·.type)) out Dc mc cvc ns ψ ρ xs (fun c' => tgtRank pp.toBlockShape c' = n)
      (homeOkN (homeR pp.toBlockShape R.aux out)) := {
    Adm := nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par
    hAdm := dyn_hAdm H ψ ρ xs hparams par
    top := dyn_top H ψ ρ xs hparams hxs hPP
    trans := dyn_trans H ψ ρ xs hparams hxs par
    hcall := nestedNodeCallsG hμ hctx hmkC hmk hag hsubC htr hcoreK hok hown hkids hpar hsem
      hmemF hPP hF hcls hsel ⟨c, hc, hg⟩ home_hMode (home_hokFrame HF) (home_hokKid HF)
      (home_hOut HF rfl) (home_hN0 HF) (home_hND HF) }
  have hS := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  have hrs : ∀ c (hc : c < (tgtRs out).length),
      (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := fun c hc => List.getElem?_eq_getElem hc
  obtain ⟨P, hP⟩ := tgtNodePres_of_list hcov hlfp hF hcls hsel (fun c hc => by
      obtain ⟨-, hlen, hall⟩ := ConLeche.recStageG_recNames hS
      obtain ⟨_, _, _, _, -, -, hle, -⟩ := hall c (by rw [← hlen]; exact hc)
      exact hle)
    (fun c hc => blockRulePdomsAV_length hμ mpC hS (hrs c hc) ψ)
    (fun c hc hm => by
      obtain ⟨ms, hms, -, -⟩ := recStage_ctorsAt (hm := tgtMemAt_of_member hc hm) hS (hrs c hc)
      have hk : pp.toBlockShape.recTgtAt c < dR.toLfp.k := by
        obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
        exact (List.getElem?_eq_some_iff.mp hms).1
      exact Nat.lt_of_lt_of_le hk (mpC.lfpClause_of_mem hlfp).kN)
    (fun c hc => by
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
        exact (hcls c hc hMo).hlen) Dy
  -- the class is related: a member class at node `0`, an outside class at its entry's node
  have hrel : ∃ b, P.Rel c b := by
    cases hmb : (tgtMajor out c).member with
    | some tm => exact ⟨0, (hP c 0).mpr ⟨hg, Or.inl ⟨by rw [hmb]; rfl, rfl⟩, hrc⟩⟩
    | none =>
      obtain ⟨-, r, hr, -⟩ := HF.hS c hc hrc
      obtain ⟨-, -, hgood⟩ := HF.hgood c r hr
      have hmo' : ((homeCls out).getD c default).member = none := by
        rw [HF.hmember c hc]; exact hmb
      cases hk : r.key with
      | none =>
        rw [hk] at hgood
        obtain ⟨t, ht, -⟩ := hgood
        rw [hmo'] at ht; exact nomatch ht
      | some dsW =>
        rw [hk] at hgood
        obtain ⟨-, -, -, hdsE, u, hu, hanc, hds, hlv, hgrp⟩ := hgood
        obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
        have hbelow := posNodeOk_ds_below0 (hok ns[i] hu) hanc
        refine ⟨i + 1, (hP c (i + 1)).mpr ⟨hg, Or.inr ⟨by omega, by omega, ?_, ?_⟩, hrc⟩⟩
        · simp only [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
            Option.getD_some]
          refine ⟨hmb, ?_, ?_, ?_⟩
          · rw [hgrp, HF.hind c hc]; exact List.mem_singleton_self _
          · rw [hlv, HF.hlvls c hc]
          · refine (erasedEqL_nodeRb_iff hbelow).mpr ?_
            rw [← HF.hds c hc, hdsE, hds]
            try rfl
        · simp only [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
            Option.getD_some]
          exact ⟨hanc, r, hr, by rw [hk, hds]⟩
  -- the calls stay in the family
  have hcallK : ∀ c, c < (tgtRs out).length → ∀ j, j < blockRecNCt (tgtRs out) c → ∀ fs c' t' y',
      tgtCall .verified F (mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval
        envC ψ (tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ) ρ xs c j fs (tagged c' t' y') →
      c' < (tgtRs out).length := by
    intro c hc j hj fs c' t' y' hcall
    obtain ⟨-, hcg, -⟩ := tgtCallee_edge hS R hc hj (tgtCall_callee hcall)
    have h1 := ConLeche.targetGraphOf_length pp.toBlockShape
    obtain ⟨-, hlen, -⟩ := ConLeche.recStageG_recNames hS
    unfold ConLeche.targetGraphOf at h1
    omega
  exact tgtDer_of_pres P hcallK hc hrc hrel ht hy

end ConLeche.Model
