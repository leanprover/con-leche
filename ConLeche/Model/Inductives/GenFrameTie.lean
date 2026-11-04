module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.GenNodeList
import ConLeche.Model.Inductives.TargetDefeqTie
import ConLeche.Model.Inductives.TargetCallCore
import ConLeche.Model.Inductives.TargetCallCarrier
import ConLeche.Model.Inductives.TargetFrame
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.NestPosRed
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Verify.Denote.Inst
import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Verify.Denote.Lemmas
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Inductives.PositivityInv

public section

/-!
# The frame half of the class tie at the generated stage (lane GENREC-B2)

`genNodeFrameTie` — `NodeFrameTie` from the generated stage's run.  Every
class is checked over the block's CANONICAL parameters (`R.ctx.params`,
the positivity context's `fvsP`), so the class match's defeq soundness
(`param_read_eq`) runs at the parameters' own walk context (the first
former's parameter telescope at the prefix's first `nP` values, which fit
the block's parameters by `hparG`), and the two readings move to the rule
prefix's depth (`tgtRP`) unchanged: both spines name only the parameters.

That soundness is conditional: a pair reads alike where neither reading
is the point.  Both spines fit ONE telescope of types — the class's own
former's parameter binders at the class's levels (`LfpReads`, a graded
Π-tower): the class's parameters because its major's domain is a graded
application of the family (`GenClsRd.hsat`), the node's recorded
instantiation because the node's true frame satisfies its recorded
block's parameters (`hnodeSat`, the dynamic part's `hAdm` at `top`), the
two blocks and level assignments being one (`lfpSel_eq_of_mem`, the
match's level comparison).  Position by position the conditional
equations are then equations (`spineFit_eq_of_cond_getD`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  GenRecRun fueledOps mkFEnv NestState)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A reading over the parameters, lifted**: a term whose free
variables lie below the openers `pfvs` (each at its own index, scoped)
reads at any longer spine as at the spine's first `|pfvs|` values. -/
theorem readParams_lift {acval : Name → (Name → Nat) → Term} {env : Env} {φ : Name → Nat}
    (hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {pfvs : List Expr} (hp : ∀ (i : Nat) (x : Expr), pfvs[i]? = some x → ∃ ty, x = .fvar i ty)
    (hpW : ∀ x ∈ pfvs, Expr.WScoped pfvs.length x) {a : Expr} (ha : a.fvarB ≤ pfvs.length)
    (xs : List V) (hle : pfvs.length ≤ xs.length) (ρ : Nat → V) :
    (denote acval env φ xs.length a).map (interp V (consList xs ρ))
      = (denote acval env φ pfvs.length a).map
          (interp V (consList (xs.take pfvs.length) ρ)) := by
  have haB : a.fvarsBelow pfvs.length :=
    ConLeche.Expr.fvarsBelow_iff.mpr (ConLeche.Expr.fvarB_eq a ▸ ha)
  have hE := canon_erasedEq hp a haB
  rw [← denote_erasedEq (acval := acval) (env := env) (φ := φ) hE xs.length,
    ← denote_erasedEq (acval := acval) (env := env) (φ := φ) hE pfvs.length,
    denote_lift hacl1 (ConLeche.targetCanonParams_WScoped hpW a haB) xs.length hle,
    Option.map_map]
  congr 1
  funext T
  have hsplit : consList xs ρ
      = consList (xs.drop pfvs.length) (consList (xs.take pfvs.length) ρ) := by
    rw [← consList_append, List.take_append_drop]
  have hdl : xs.length - pfvs.length = (xs.drop pfvs.length).length := by
    rw [List.length_drop]
  simp only [Function.comp_apply]
  rw [hsplit, hdl, interp_liftN_consList]

/-- **The frame tie at the generated stage** (see the module docstring). -/
theorem genNodeFrameTie (hμ : μ.verifiedChecks = true) {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → Term}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : NestState} {nested : Bool}
    (hctx : RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR)
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nested posR cvTasR
      block ctorsAsR out)
    (h : ConLeche.RecStageG μ F envC pp cvTasR (ConLeche.tgtRs out))
    (hparG : ∀ c, c < (ConLeche.tgtRs out).length → ∀ (ψ : Name → Nat) (ρ : Nat → V)
      (xs : List V),
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (ConLeche.tgtRs out) ψ c)
        xs → SpineFit ρ (dR.params ψ) (xs.take dR.nP))
    (hg : ConLeche.ClassGenScoped R.g)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (ConLeche.tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (ConLeche.tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind)
    {fvsP : List Expr} (hctxR : R.ctx = pp.nestCtx fvsP envI.find?)
    (ns : List ConLeche.PosTree)
    (hF : NodeListFacts mpC (pp.nestCtx fvsP envI.find?) ns)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hnodeSat : ∀ t ∈ ns,
      Sat V ((lfpSel mpC dR.toLfp t.key.cname).params (nodeψ envC ψ t)).reverse
        (nodeFr mpC.base2.acval envC (pp.nestCtx fvsP envI.find?) ψ ρ xs t)) :
    NodeFrameTie mpC.base2.acval (pp.nestCtx fvsP envI.find?) pp.toBlockShape out ns
      ψ ρ xs envC F (cvTasR.map (·.type)) := by
  intro c hc t ht hNM hsp
  obtain ⟨-, -, -, -, hN, hS, hcore, -, hdR, -, hcov, -⟩ := hctx
  have hmr : BlockMembersRun mpC.base2 dR pp.toBlockShape cvTasR := by
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; exact blockMembersRun_seam hN hS hcore
  have hnPq : dR.nP = pp.nP := hmr.1
  -- the canonical parameters: the head former's opened telescope
  obtain ⟨cvTa0, fvsP', rest, hcv, hop, hctxR', -⟩ := ConLeche.blockNestCtx_inv R.hctx
  obtain rfl : fvsP = fvsP' := congrArg ConLeche.NestCtx.params (hctxR.symm.trans hctxR')
  have hlenP : fvsP.length = pp.nP := ConLeche.Verify.openPisAtFvars_length _ hop
  -- the class's openers are the canonical parameters
  obtain ⟨_, M₀, nfs, -, -, -, -, hM, ⟨hCR⟩, -⟩ := genTgtMajor R hc
  have hpf : (tgtMajor out c).pfvs = fvsP := by
    rw [hM]; show M₀.pfvs = fvsP; rw [ConLeche.ClassMajorRun.pfvs_eq hCR, hctxR']; rfl
  obtain ⟨-, hPD⟩ := ConLeche.targetClassMatch_true hNM.2.2
  rw [hpf] at hPD
  -- the head former's data
  have hcv0 : cvTasR[0]? = some cvTa0 := by
    rw [List.head?_eq_getElem?] at hcv; exact hcv
  obtain ⟨-, -, -, hfvT, hbndT, hFD⟩ := hmr.2.2.2.1 0 cvTa0 hcv0
  have hppsLen : (dR.ppsM 0 ψ).length = dR.nP + dR.nIdxAt 0 := hFD.len ψ
  obtain ⟨ppsT, bT, hstT, -, -, hbindT⟩ :=
    denote_openPis (acval := mpC.base2.acval) (env := envC) (φ := ψ) pp.nP hop (hFD.read ψ)
  have hppsT : ppsT = (dR.ppsM 0 ψ).take pp.nP := by
    have := stripPisAV_mkPisAV_take pp.nP (dR.ppsM 0 ψ)
      (.sort (dR.resSort.eval ψ)) (by rw [hppsLen, hnPq]; omega)
    rw [this] at hstT
    exact congrArg Prod.fst (Option.some.inj hstT.symm)
  have hpl : (dR.params ψ).length = pp.nP := by
    rw [BlockData.params, List.length_take, hppsLen]; omega
  have hP : ∀ (l : Nat) (x : Expr), fvsP[l]? = some x →
      denote mpC.base2.acval envC ψ l (Expr.fvarTypeD x) = some ((dR.params ψ).getD l default) := by
    intro l x hx
    obtain ⟨pd, hpd, hreadD⟩ := hbindT l x hx
    rw [Nat.zero_add] at hreadD
    rw [hreadD, BlockData.params, hnPq, ← hppsT, List.getD_eq_getElem?_getD, hpd]
    rfl
  have hdoms := blockRuleHdoms_of (acval := mpC.base2.acval) (envT := envC) (ψ := ψ)
    (fdoms := []) (ihdoms := []) (fvsF := []) (fvsIh := []) hpl rfl rfl hlenP rfl rfl hP
    (fun l x hx => nomatch hx) (fun l x hx => nomatch hx)
  have hokΔ := blockRuleHokΔ_of (V := V) (pdoms := dR.params ψ) (fdoms := []) (ihdoms := [])
    hpl rfl rfl (fun l hl σ' ys hys => by
      simp only [List.append_nil] at hl hys ⊢
      exact prefixDoms_graded_of_tower (V := V) (cc := .sort (dR.resSort.eval ψ))
        (by rw [hppsLen]; omega) (fun ρ'' => hFD.okTy ψ ρ'') (by simp at hl; omega) hys)
  -- the parameters' scoping
  have hTc : ConstsBound envC cvTa0.type :=
    constsBound_of_read 0 cvTa0.type (hFD.read ψ) (by
      rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hfvT]; intro l hl; exact nomatch hl)
  have hcr : ConLeche.instPisWith [] (Expr.sort .zero) = some (Expr.sort .zero) := rfl
  have h₂ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) pp.nP = some ([], Expr.sort .zero) := rfl
  obtain ⟨hFr, hlbF, hcbF, hher⟩ := targetFrame_facts (envT := envC) hop hcr
    (fun a ha => nomatch ha) h₂ hfvT hbndT hTc rfl rfl (by simp)
  simp only [List.append_nil, Nat.add_zero] at hFr hlbF hcbF hher
  -- the parameters' fit, and the walk context
  have hfit := hparG c hc ψ ρ xs hsp
  rw [hnPq] at hfit
  have h₃ : ConLeche.openPisAtFvars 0 (Expr.sort .zero) (pp.nP + 0)
      = some ([], Expr.sort .zero) := rfl
  have hW := walkCtx_blockFrame (V := V) (mT := mpC.base2) (ψ := ψ) (ihdoms := [])
    (ihvals := []) (fdoms := []) (fs := []) hop h₂ h₃ hpl rfl rfl
    (by simpa using hdoms) (by simpa using hokΔ)
    (by simpa using hlbF) (by simpa using hcbF) (by simpa using hher)
    (by simpa using hfit) (by simp [SpineFit])
  simp only [Nat.add_zero, List.append_nil, List.reverse_nil, List.nil_append] at hW
  rw [← hlenP] at hFr
  have hW' : WalkCtx V mpC.base2 ψ fvsP.length (consList (xs.take pp.nP) ρ)
      (dR.params ψ).reverse fvsP.reverse := by rw [hlenP]; simpa using hW
  -- the spine's length
  have hr : (ConLeche.tgtRs out)[c]? = some (ConLeche.tgtRs out)[c] := List.getElem?_eq_getElem hc
  have hxl : xs.length = tgtRP pp.toBlockShape c := by
    rw [SpineFit.length_eq hsp, blockRulePdomsAV_length hμ mpC h hr ψ]; rfl
  have hnle : pp.nP ≤ xs.length := by
    have := SpineFit.length_eq hfit
    rw [List.length_take, hpl] at this; omega
  -- the members' holes
  let hv : List V := (List.range cvTasR.length).map fun t =>
    interp V ρ (mpC.base2.acval (dR.memberName t) ψ)
  have hvl : hv.length = (cvTasR.map (·.type)).length := by simp [hv]
  have hvget : ∀ t, t < cvTasR.length →
      hv.getD t pt = interp V ρ (mpC.base2.acval (dR.memberName t) ψ) := by
    intro t ht; simp [hv, List.getD_eq_getElem?_getD, List.getElem?_range ht]
  have hnames := memberHoles_names (pp := pp) hN hmr ψ ρ (hvC := fun t => hv.getD t pt) hvget
  have hformer := memberHoles_formers (mpC := mpC) hmr ψ ρ (memberHoles_ty hmr ψ ρ hvget)
  have hacl : ∀ (n : Name) (ψ' : Name → Nat) (m k : Nat),
      (mpC.base2.acval n ψ').liftN m k = mpC.base2.acval n ψ' :=
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closed n ψ') k m
  have hacl1 : ∀ (n : Name) (ψ' : Name → Nat) (k : Nat),
      (mpC.base2.acval n ψ').liftN 1 k = mpC.base2.acval n ψ' := fun n ψ' k => hacl n ψ' 1 k
  have hp := fun i x (hx : fvsP[i]? = some x) => fvarList_rev_getElem hFr hx
  have hpW : ∀ x ∈ fvsP, Expr.WScoped fvsP.length x :=
    fun x hx => hFr.2.2 x (List.mem_reverse.mpr hx)
  -- the class: an outside one, its datum and level assignment
  have hMo : (tgtMajor out c).member = none := hNM.1
  have hlv := (ConLeche.targetClassMatch_true hNM.2.2).1
  have hcl := hcls c hc hMo
  have hnPc : pp.nP ≤ pp.toBlockShape.rulePrefixAt c := by
    obtain ⟨-, -, -, -, -, -, -, -, -, hRP, -⟩ := genRun_binders hμ R hg h mpC (fun _ => 0) hc
    rw [hRP, (ConLeche.ClassGen.prefixBinders_scoped hg hg.pre).1]
    exact Nat.le_add_right _ _
  obtain ⟨Rd, -⟩ := genClsRd_out (d := dR) hμ R hg hcov h hc hMo hcl hnPc
  have hDe : tgtClsD dR Dc out c = Dc c := by simp [tgtClsD, hMo]
  generalize hψc : Level.substFn ψ (cvc c).levelParams (tgtMajor out c).lvls = ψc
  -- the node: the same datum, at the same levels
  obtain ⟨Dn, hDn, h1, h2⟩ := hF.blk t ht _ hNM.2.1
  have hDsel : lfpSel mpC dR.toLfp t.key.cname = Dc c := by
    rw [hsel c hc hMo]; exact lfpSel_eq_of_mem hcov _ hDn h2 h1
  have hψn : nodeψ envC ψ t = ψc := by
    rw [← hψc]
    obtain ⟨caps, hf⟩ := hcl.hfind
    have hl : (cvc c).levelParams = lpsOf envC (tgtMajor out c).ind := by
      simp only [lpsOf, hf]; rfl
    simp only [nodeψ, hl, hF.lps t ht _ hNM.2.1]
    exact (ConLeche.Level.substFn_congr (ConLeche.Level.isEquivList_sound hlv ψ)).symm
  -- the shared telescope: the class's own former's parameter binders, a
  -- telescope of types (the stored type's reading is a graded Π-tower)
  obtain ⟨hC, -, hrd, -⟩ := mpC.lfp_ok (Dc c) hcl.hD
  obtain ⟨cvm, capsm, hfm, hab⟩ := hrd (mc c) hcl.hmm
  obtain ⟨ab, hta, hmap⟩ := hab ψc
  have hTy : SpineTy ρ ((Dc c).pars (mc c) ψc) := by
    have hwd := (mpC.type_wellDenotedTy _ (ConLeche.Env.find?_mem hfm) ψc _ hta ρ).1
    have := (spineTy_of_wellDenoted_mkPisAV hwd).take ((Dc c).pars (mc c) ψc).length
    rwa [hmap, List.take_left] at this
  have hparsL := hC.parsLen (mc c) hcl.hmm ψc
  -- the prefix's tail
  have hkf : ∀ dsa : List Term, keyFrame dsa xs.length (consList xs ρ)
      = consList (dsa.map (interp V (consList xs ρ))) ρ := by
    intro dsa
    unfold keyFrame
    congr 1
    funext j
    exact consList_apply_add xs ρ j
  -- pair by pair: the class match's soundness at the parameters, lifted
  obtain ⟨hl, hall⟩ := ConLeche.targetParamsDefEq_true hPD
  have hnP' : (pp.nestCtx fvsP envI.find?).nP ≤ tgtRP pp.toBlockShape c := hnPc
  obtain ⟨dsaK, hspK⟩ := hF.sp t ht ψ
  obtain ⟨ebs, hebs, -⟩ := readback_spine mpC.base2 ((hF.read t ht).hs ψ hnP') ρ (hF.ws t ht) hspK
  have hkfN := keyFrame_readback (V := V) mpC.base2 ((hF.read t ht).hs ψ hnP') (hF.ws t ht) hspK
    (erasedEqL_refl _) (consList xs ρ)
  have hdsaC := Rd.hdsa ψ
  have hsatC := Rd.hsat ψ ρ xs hsp
  rw [hDe, Rd.hψ, hψc] at hsatC
  have hsatN := hnodeSat t ht
  rw [hDsel, hψn] at hsatN
  unfold nodeFr at hsatN
  rw [← denoteSpine_eq_map hspK, ← substE_nodeImgX_trueVal mpC.base2 ψ ρ hnle, hxl,
    ← hkfN, ← hxl] at hsatN
  unfold tgtOutDsa at hsatC hdsaC
  rw [← hxl] at hsatC hdsaC hebs ⊢
  rw [hkf] at hsatC hsatN
  generalize t.key.ds.map (nodeRb (pp.nestCtx fvsP envI.find?) t.occ) = eds at hl hall hsatN hebs ⊢
  rw [List.map_map] at hsatC hsatN
  have hsatC' := hC.parsSat (mc c) hcl.hmm ψc _ hsatC
  have hsatN' := hC.parsSat (mc c) hcl.hmm ψc _ hsatN
  have hlenC : (tgtMajor out c).ds.length = ((Dc c).params ψc).length := by
    have := Rd.hlenP ψ
    rw [hDe, Rd.hψ, hψc] at this
    exact this.symm
  have hfitC := spineFit_of_sat_consList (by rw [List.length_map, hparsL, hlenC]) hsatC'
  have hfitN := spineFit_of_sat_consList (by rw [List.length_map, hparsL, ← hl, hlenC]) hsatN'
  refine spineFit_eq_of_cond_getD hTy hfitC hfitN fun i hi hxn hyn => ?_
  have hiC : i < (tgtMajor out c).ds.length := by rw [hlenC, ← hparsL]; exact hi
  have hiN : i < eds.length := by rw [← hl]; exact hiC
  have ha : (tgtMajor out c).ds[i]? = some ((tgtMajor out c).ds[i]) := List.getElem?_eq_getElem hiC
  have hb : eds[i]? = some eds[i] := List.getElem?_eq_getElem hiN
  have hm := hall i _ _ ha hb
  have hr' := param_read_eq (μ := .verified) rfl hacl (Rules.RulesInputs.ofSem mpC ψ)
    (pfvs := fvsP) hFr hW' hvl hformer hnames hm
  have hA := readParams_lift (env := envC) (φ := ψ) hacl1 hp hpW hm.2.2.1 xs
    (by omega) ρ
  have hB := readParams_lift (env := envC) (φ := ψ) hacl1 hp hpW hm.2.2.2.1 xs
    (by omega) ρ
  rw [hlenP] at hA hB hr'
  have hra := hdsaC.getD (tgtMajor out c).ds[i] i hiC
  have hrb := hebs.getD eds[i] i hiN
  rw [List.getD_eq_getElem?_getD, ha, Option.getD_some] at hra
  rw [List.getD_eq_getElem?_getD, hb, Option.getD_some] at hrb
  obtain ⟨va, hra⟩ : ∃ va, _ = some va := ⟨_, hra⟩
  obtain ⟨vb, hrb⟩ : ∃ vb, _ = some vb := ⟨_, hrb⟩
  rw [hra, Option.map_some] at hA
  rw [hrb, Option.map_some] at hB
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map, ha, hb, Option.map_some,
    Option.getD_some, hra, hrb] at hxn hyn ⊢
  exact hr' _ _ hA.symm hB.symm hxn hyn

end ConLeche.Model
