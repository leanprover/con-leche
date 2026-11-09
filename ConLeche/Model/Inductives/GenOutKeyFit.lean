module

import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Model.Inductives.TargetOutRow
public import ConLeche.Verify.Inductives.GenRecRun
public import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Model.Inductives.GenNodeList
import ConLeche.Semantics.Inductives.DeclBlockEta
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.TargetNodeSem
import ConLeche.Verify.EnvBound
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Env.LfpFormer
import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.GenOutFacts
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Model.Inductives.GenRecParams
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.BlockDatum
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Rules.Inputs
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Inductives.GenRecScoped

public section

/-!
# An outside class's parameters fit its family's telescope

The class check types an outside class's key against the family's telescope, at the block's
parameters (`targetMajorPins`). The key is over the block's canonical parameters, which open the
first member's telescope, so it is read at those binders; a recursor's prefix starts with the same
binders (`genParams_fit_run`). Together: at every fitting prefix of a recursor, the class's parameters
satisfy the family's parameter telescope.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps BlockShape NestCtx
  TargetMajor mkFEnv fueledOps tgtRs)

universe w

variable {V : Type w} [SetTheory V]

/-- **An outside class's parameters fit**, at every fitting prefix of its recursor. -/
theorem genOut_keyFit {F : Nat} {envC envI : Env} {pp : BlockShape} {mpC : EnvModelM V envC} {dR : BlockData V}
    {isRec : Bool} {A : Nat → (Name → Nat) → Term}
    {kinds : List (List (List ConLeche.NestFieldKind))} {nfs : List (List Expr)}
    {pos : ConLeche.NestState} {nb : Bool} {block : List ConstantInfo}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    (hctx : RecCtxBase V F envC envI pp mpC dR isRec A kinds nfs pos)
    (R : ConLeche.GenRecRun .verified F (mkFEnv envI) envI (mkFEnv envC) pp nb pos
      block out)
    (hg : ConLeche.ClassGenScoped R.g)
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    {c : Nat} (hc : c < (tgtRs out).length) (hMo : (tgtMajor out c).member = none)
    {D : LfpDatum V} {mm : Nat} {cvI : ConstantVal} (hcl : TgtOutCls mpC (tgtMajor out c) D mm cvI)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hfit : SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ c) xs)
    {dsa : List Term}
    (hdsa : DenoteSpine mpC.base2.acval envC ψ (tgtRP pp c) (tgtMajor out c).ds dsa) :
    Sat V (D.params (Level.substFn ψ cvI.levelParams (tgtMajor out c).lvls)).reverse
      (keyFrame dsa (tgtRP pp c) (consList xs ρ)) := by
  obtain ⟨-, henvC, -, -, hN, hS, hcore, -, hdR, -, hcovC,
    ⟨mk, -, hreads, -, -, -, hsubC, hcoreK, htr⟩, -, -⟩ := hctx
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hmr := blockMembersRun_seam hN hS hcore
  have hnPq : (blockDataOf V pp pk uOfD ppsOf).nP = pp.nP := rfl
  -- the recursor's prefix, on the block's parameters
  have hpf := genParams_fit_run mpC R hg h hmr c hc ψ ρ xs hfit
  have hsat₀ : Sat V ((blockDataOf V pp pk uOfD ppsOf).params ψ).reverse
      (consList (xs.take pp.nP) ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hpf
    rwa [List.append_nil] at this
  -- the class, as the pre-block run checked it
  obtain ⟨cls, -, -, -, hgc, hM', -, -, -, hRP, -⟩ := genRun_binders R hg h mpC ψ hc
  have hi : cls < R.Ms.length := by rw [← hgc]; exact genRun_cls_lt R hc
  obtain ⟨key, M₀, nfs₀, hMs, hMs₀, ⟨CR⟩⟩ := genRun_class R hi
  have hMe : tgtMajor out c = { M₀ with nfs := nfs₀ } := by
    rw [hM']
    show R.Ms.getD cls default = _
    rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
  have hMo₀ : M₀.member = none := by rw [hMe] at hMo; exact hMo
  have hkey := ConLeche.targetMajorPins_key
    (ConLeche.classMajors_pins R.hMs₀ M₀ (List.mem_of_getElem? hMs₀)) hMo₀
  have hkey' : ConLeche.familyKeyCheck (fueledOps .verified F) envI envI.find? pp.nP
      (tgtMajor out c).ind (tgtMajor out c).lvls (tgtMajor out c).ds = .ok () := by
    rw [hMe, show envI.find? = (mkFEnv envI).find? from (funext (ConLeche.mkFEnv_find? envI)).symm]
    exact hkey
  -- its family, a block of the formers' model
  obtain ⟨caps, hfC⟩ := hcl.hfind
  have hfE : envI.find? (tgtMajor out c).ind = some (.indInfo cvI caps) := by
    rw [henvC] at hfC
    exact ConLeche.Semantics.consBlockCtors_find?_indInfo hfC
  obtain ⟨sI, hnone, -, hct, hdsLen, -, -⟩ := CR.outside_of hMo₀
  have hDm : D ∈ mk.lfpBlocks := by
    rcases hsubC D hcl.hD with rfl | hD
    · exfalso
      have hmemN := hcl.hmem
      rw [hMe] at hmemN
      have hin : (M₀.ind) ∈ pp.memberNames := by
        rw [← show (blockDataOf V pp pk uOfD ppsOf).toLfp.member mm = M₀.ind
          from hmemN]
        show pp.memberNames.getD mm .anonymous ∈ _
        exact getD_mem _ (by
          have := hcl.hmm
          simpa [BlockData.toLfp, blockDataOf, blockDataPre, BlockData.withPhi,
            ConLeche.BlockShape.k, ConLeche.BlockShape.memberNames] using this)
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hin
      have hall := List.findIdx?_eq_none_iff.mp hnone
      have := hall _ (List.mem_of_getElem? ht)
      simp at this
    · exact hD
  -- the key's certificates, at the telescope the block read
  obtain ⟨tyC, -, hfam, hsp⟩ := familyKeyCheck_inv hfE hkey'
  rw [hreads F D hDm mm cvI caps tyC hcl.hmm (by rw [hcl.hmem]; exact hfE) hfam] at hsp
  have hcerts := checkSpineAt_certs hsp
  -- the block's parameters, opened at the formers' model
  obtain ⟨cvT0, rest, h0, hop, -, -⟩ := ConLeche.genRun_ctx R
  have h0' : pp.formers[0]? = some cvT0 := by rwa [List.head?_eq_getElem?] at h0
  obtain ⟨⟨_, -, hD0⟩, hFD0⟩ := hcoreK.1 0 cvT0 h0'
  have hlen0 := hFD0.len ψ
  have hread0 := hFD0.read ψ
  rw [← List.take_append_drop pp.nP ((blockDataOf V pp pk uOfD ppsOf).ppsM 0 ψ),
    mkPisAV_append'] at hread0
  have hO := opened_of_peel (m := mk.base2) (φ := ψ) hop hD0.readFvar hD0.readBounded hread0
    (by rw [List.length_take, hlen0, hnPq]; omega) (fun ρ' => by
      have hok := hFD0.okTy ψ ρ'
      rwa [← List.take_append_drop pp.nP
        ((blockDataOf V pp pk uOfD ppsOf).ppsM 0 ψ), mkPisAV_append'] at hok)
  -- the key over them
  have hTsc : ∀ cv ∈ pp.formers, ConLeche.ScB 0 cv.type := fun cv hcv => by
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hcv
    obtain ⟨⟨_, -, hDt⟩, -⟩ := hcoreK.1 t cv ht
    exact ConLeche.ScB.of_closed hDt.readFvar hDt.readBounded 0
  have hds : ∀ x ∈ (tgtMajor out c).ds, ConLeche.ScB pp.nP x := by
    have hgds := hg.ds cls
    intro x hx
    rw [hM'] at hx
    exact hgds x hx
  have hleaves : ∀ x ∈ (tgtMajor out c).ds, ∀ l ∈ x.fvarLeaves,
      Expr.fvar l.1 l.2 ∈ R.ctx.params := by
    have hMC : R.Ms[cls]? = some { M₀ with nfs := nfs₀ } := hMs
    have := ConLeche.genRun_out_leaves R hTsc hMC hMo₀
    rw [hMe]
    exact this
  have hC : ∀ x ∈ (tgtMajor out c).ds, CtxOk mk.base2 ψ pp.nP
      ((blockDataOf V pp pk uOfD ppsOf).params ψ).reverse x := fun x hx => by
    have := hO.ctx (Nat.le_refl _) (hds x hx).1 (hleaves x hx)
    rw [Nat.sub_self, List.drop_zero] at this
    exact this
  have hLds : ∀ x ∈ (tgtMajor out c).ds, Expr.LeavesBounded x := by
    intro x hx l hl
    obtain ⟨i, hi⟩ := List.getElem?_of_mem (hleaves x hx l hl)
    exact (hO.var i _ hi).2.2.1
  obtain ⟨dsa₀, hdsa₀⟩ := familyKey_reads mk.base2 ψ hkey' (fun x hx => (hds x hx).1)
    (fun x hx => (hds x hx).2) hLds
  have hfitK := (keyParamsFit mk (Rules.RulesInputs.ofSem mk ψ) hDm hcl.hmm
    (by rw [hcl.hmem]; exact hfE) hcerts
    (by
      rw [genOutParamsLen hcovC hcl (by rw [hMe]; exact hct) (by rw [hMe]; exact hdsLen) ψ])
    (by
      rw [List.length_reverse]
      show (List.take _ _).length = _
      rw [List.length_take, hlen0, hnPq]
      omega)
    (fun x hx => ⟨⟨(hds x hx).1, (hds x hx).2, hLds x hx⟩, CtxOk.toS (hC x hx)⟩) hdsa₀
    (consList (xs.take pp.nP) ρ) hsat₀ (fun x hx => CtxOk.leavesGr (hC x hx) hsat₀)).1
  -- the frame at the recursor's prefix is the frame at the block's parameters
  have hnP : pp.nP ≤ tgtRP pp c := by
    show pp.nP ≤ pp.rulePrefixAt c
    rw [hRP, (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1]
    exact Nat.le_add_right _ _
  obtain ⟨vs, hvs, rfl⟩ := DenoteSpine.unlift (m := mpC.base2) (φ := ψ) hnP
    (fun x hx => (hds x hx).1) hdsa
  have hvs₀ : vs = dsa₀ :=
    DenoteSpine.unique hvs (DenoteSpine.transport (fun e _ he => htr ψ _ e he) hdsa₀)
  subst hvs₀
  have hlenx : xs.length = tgtRP pp c := by
    rw [hfit.length_eq, blockRulePdomsAV_length mpC h (List.getElem?_eq_getElem hc) ψ]; rfl
  have hsplit : consList xs ρ = consList (xs.drop pp.nP) (consList (xs.take pp.nP) ρ) := by
    conv => lhs; rw [← List.take_append_drop pp.nP xs]
    rw [consList_append]
  have hkl := keyFrame_lift vs pp.nP (xs.drop pp.nP) (consList (xs.take pp.nP) ρ)
  have hdl : (xs.drop pp.nP).length = tgtRP pp c - pp.nP := by
    rw [List.length_drop, hlenx]
  rw [hdl, show pp.nP + (tgtRP pp c - pp.nP) = tgtRP pp c by omega,
    ← hsplit] at hkl
  rw [hkl]
  exact hfitK

end ConLeche.Model
