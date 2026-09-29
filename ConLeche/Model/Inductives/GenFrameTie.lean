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
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Rules.Inputs
import ConLeche.Verify.Inductives.ClassMatchRun
import ConLeche.Verify.Inductives.RecCheckScope
import ConLeche.Verify.Inductives.PositivityInv

public section

/-!
# The frame half of the class tie at the generated stage (lane GENREC-B2)

`genNodeFrameTie` — `NodeFrameTie` from the generated stage's run.  Every
class is checked over the block's CANONICAL parameters (`R.ctx.params`,
the positivity context's `fvsP`), so the class match's defeq soundness
(`params_read_eq`) runs at the parameters' own walk context (the first
former's parameter telescope at the prefix's first `nP` values, which fit
the block's parameters by `hparG`), and the two readings move to the rule
prefix's depth (`tgtRP`) unchanged: both spines name only the parameters.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  GenRecRun fueledOps mkFEnv NestState)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **A reading over the parameters, lifted**: a term whose free
variables lie below the openers `pfvs` (each at its own index, scoped)
reads at any longer spine as at the spine's first `|pfvs|` values. -/
theorem readParams_lift {acval : Name → (Name → Nat) → AnnotTerm} {env : Env} {φ : Name → Nat}
    (hacl1 : ∀ (n : Name) (ψ : Name → Nat) (k : Nat), (acval n ψ).liftN 1 k = acval n ψ)
    {pfvs : List Expr} (hp : ∀ (i : Nat) (x : Expr), pfvs[i]? = some x → ∃ ty, x = .fvar i ty)
    (hpW : ∀ x ∈ pfvs, Expr.WScoped pfvs.length x) {a : Expr} (ha : a.fvarB ≤ pfvs.length)
    (xs : List V) (hle : pfvs.length ≤ xs.length) (ρ : Nat → V) :
    (denoteMeta acval env φ xs.length a).map (interp V (consList xs ρ))
      = (denoteMeta acval env φ pfvs.length a).map
          (interp V (consList (xs.take pfvs.length) ρ)) := by
  have haB : a.fvarsBelow pfvs.length :=
    ConLeche.Expr.fvarsBelow_iff.mpr (ConLeche.Expr.fvarB_eq a ▸ ha)
  have hE := canon_erasedEq hp a haB
  rw [← denoteMeta_erasedEq (acval := acval) (env := env) (φ := φ) hE xs.length,
    ← denoteMeta_erasedEq (acval := acval) (env := env) (φ := φ) hE pfvs.length,
    denoteMeta_lift hacl1 (ConLeche.targetCanonParams_WScoped hpW a haB) xs.length hle,
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

theorem getD_eq_of_map_eq {α : Type _} {g : AnnotTerm → α} {o₁ o₂ : Option AnnotTerm}
    (h : o₁.map g = o₂.map g) : g (o₁.getD default) = g (o₂.getD default) := by
  cases o₁ <;> cases o₂ <;> simp_all

/-- **The frame tie at the generated stage** (see the module docstring). -/
theorem genNodeFrameTie (hμ : μ.verifiedChecks = true) {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : NestState} {nested : Bool}
    (hctx : RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR)
    (R : GenRecRun μ F (mkFEnv envI) envI (mkFEnv envC) pp.toBlockShape nested posR cvTasR
      block ctorsAsR out)
    (h : ConLeche.RecStageG μ F envC pp cvTasR ctorsAsR (ConLeche.tgtRs out) (fun _ => False))
    (hparG : ∀ c, c < (ConLeche.tgtRs out).length → ∀ (ψ : Name → Nat) (ρ : Nat → V)
      (xs : List V),
      SpineFit ρ (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (ConLeche.tgtRs out) ψ c)
        xs → SpineFit ρ (dR.params ψ) (xs.take dR.nP))
    {fvsP : List Expr} (hctxR : R.ctx = pp.nestCtx fvsP envI.find?)
    (ns : List ConLeche.PosTree) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    NodeFrameTie mpC.base2.acval (pp.nestCtx fvsP envI.find?) pp.toBlockShape out ns
      ψ ρ xs envC F (cvTasR.map (·.type)) := by
  intro c hc t _ hNM hsp
  obtain ⟨-, -, -, -, hN, hS, hcore, -, hdR, -⟩ := hctx
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
    denoteMeta_openPis (acval := mpC.base2.acval) (env := envC) (φ := ψ) pp.nP hop (hFD.read ψ)
  have hppsT : ppsT = (dR.ppsM 0 ψ).take pp.nP := by
    have := stripPisAV_mkPisAV_take pp.nP (dR.ppsM 0 ψ)
      (.sort (dR.resSort.eval ψ)) (by rw [hppsLen, hnPq]; omega)
    rw [this] at hstT
    exact congrArg Prod.fst (Option.some.inj hstT.symm)
  have hpl : (dR.params ψ).length = pp.nP := by
    rw [BlockData.params, List.length_map, List.length_take, hppsLen]; omega
  have hP : ∀ (l : Nat) (x : Expr), fvsP[l]? = some x →
      denoteMeta mpC.base2.acval envC ψ l (Expr.fvarTypeD x) = some ((dR.params ψ).getD l default) := by
    intro l x hx
    obtain ⟨pd, hpd, -, hreadD⟩ := hbindT l x hx
    rw [Nat.zero_add] at hreadD
    rw [hreadD, BlockData.params, hnPq, ← hppsT, List.getD_eq_getElem?_getD, List.getElem?_map, hpd]
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
    fun n ψ' m k => liftN_eq_self_of_closed (mpC.base2.cval_closedL n ψ') k m
  have hacl1 : ∀ (n : Name) (ψ' : Name → Nat) (k : Nat),
      (mpC.base2.acval n ψ').liftN 1 k = mpC.base2.acval n ψ' := fun n ψ' k => hacl n ψ' 1 k
  have hp := fun i x (hx : fvsP[i]? = some x) => fvarList_rev_getElem hFr hx
  have hpW : ∀ x ∈ fvsP, Expr.WScoped fvsP.length x :=
    fun x hx => hFr.2.2 x (List.mem_reverse.mpr hx)
  -- pair by pair: the class match's soundness at the parameters, lifted
  obtain ⟨hl, hall⟩ := ConLeche.targetParamsDefEq_true hPD
  rw [← hxl]
  generalize t.key.ds.map (nodeRb (pp.nestCtx fvsP envI.find?) t.occ) = eds at hl hall ⊢
  refine List.ext_getElem? fun i => ?_
  simp only [List.getElem?_map]
  cases hx : (tgtMajor out c).ds[i]? with
  | none =>
    have : eds[i]? = none :=
      List.getElem?_eq_none (by have := List.getElem?_eq_none_iff.mp hx; omega)
    rw [this]
  | some a =>
    obtain ⟨b, hb⟩ : ∃ b, eds[i]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by have := (List.getElem?_eq_some_iff.mp hx).1; omega)⟩
    rw [hb]
    have hm := hall i a b hx hb
    have hr' := param_read_eq (μ := .verified) rfl hacl (Rules.RulesInputs.ofSem mpC ψ)
      (pfvs := fvsP) hFr hW' hvl hformer hnames hm
    have hA := readParams_lift (env := envC) (φ := ψ) hacl1 hp hpW hm.2.2.1 xs
      (by omega) ρ
    have hB := readParams_lift (env := envC) (φ := ψ) hacl1 hp hpW hm.2.2.2.1 xs
      (by omega) ρ
    rw [hlenP] at hA hB hr'
    simp only [Option.map_some, Option.some.injEq]
    exact getD_eq_of_map_eq (hA.trans (hr'.trans hB.symm))

end ConLeche.Model
