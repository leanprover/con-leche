module

public import ConLeche.Model.Inductives.GenRecAssembly
public import ConLeche.Model.Inductives.TargetNodePres
import ConLeche.Model.Inductives.GenNodeCalls
import ConLeche.Model.Inductives.GenFrameTie
import ConLeche.Model.Inductives.GenRecParams
import ConLeche.Model.Inductives.GenRecStage
import ConLeche.Model.Inductives.TargetNodeSem
import ConLeche.Model.Inductives.TargetNodeDynOf
import ConLeche.Model.Inductives.TargetNodeCover
import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockRecPreRun

public section

/-!
# The class induction at the GENERATED calls (lane GENREC-B2)

`genClassInd` — `GenClassInd` (`GenRecAssembly.lean`) over the old node
route: the node presentation over the positivity derivation's node list
(`TgtNodePres`, generic over the call relation), its calls re-proved for
the generated calls (`genCallT`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The generated stage's context holds the shared one. -/
theorem GenRecCtx.base {F : Nat} {block : List ConstantInfo} {envC envI : Env}
    {pp : BlockParts} {cvTasR : List ConstantVal} {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (h : GenRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      posR) :
    RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- **The class tie at the generated stage** (`nestedClassNodes`): at the
generated stage's context, every choice of the outside classes' data and
every prefix spine, a node presentation at the GENERATED calls over the
positivity derivation's node list (`genRecCtx_nodes`), whose dynamic part
is the admissible frames with the generated calls (`genNodeCalls`), and
which covers every guarded class. -/
theorem genClassNodes {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : GenRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      posR)
    (R : GenRecRun μ F (ConLeche.mkFEnv envI) envI (ConLeche.mkFEnv envC) pp.toBlockShape
      (ConLeche.blockNestedBit pp.toBlockShape kindsR) posR cvTasR block ctorsAsR out)
    (hg : ConLeche.ClassGenScoped R.g)
    (hTbl : ∀ e ∈ R.st.ctorNfs.toList, ConLeche.ScB pp.nP e.ty)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∃ P : TgtNodePres envC mpC.base2.acval pp.toBlockShape out dR Dc mc cvc ψ ρ xs
      (genCallT (tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ) ρ
        (fun c j => genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j)),
      TgtNodeHex P := by
  have hbase := hctx.base
  have hbase' := hbase
  obtain ⟨-, -, -, hndM, hN, hS, hcore, -, hdR, hlfp, hcov,
    ⟨mk, hmkC, hmk, hag, hsubC, hcoreK, htr⟩, -⟩ := hbase'
  have h := recStage_of_gen hμ R hg
  have hmr : BlockMembersRun mpC.base2 dR pp.toBlockShape cvTasR := by
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; exact blockMembersRun_seam hN hS hcore
  have hparG := genParams_fit_run hμ mpC R hg h hmr
  -- the node list
  obtain ⟨fvsP, ns, hctxR, hok, hkids, hpar, hsem, hfrec, hmemF, ⟨par, hPP⟩, hcovN⟩ :=
    genRecCtx_nodes hμ hbase R mk hmkC hcoreK
  have hsp : ∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
      ((pp.nestCtx fvsP envI.find?).hiAt t.occ.length) t.key.ds dsa := by
    intro t ht ψ
    obtain ⟨dsa, hdsa⟩ := nodeSem_spOcc (hok t ht) (hsem t ht ψ)
    exact ⟨dsa, DenoteMetaSpine.transport (fun e _ he => htr ψ _ e he) hdsa⟩
  obtain ⟨hparF, hparS⟩ := canonPars_of_forests hbase hmemF
  have hF := nodeListFacts_of hbase hok hpar hparF hparS hsp
  by_cases hgd : ∃ c, c < (tgtRs out).length ∧
      tgtClsG dR mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c
  case neg => exact ⟨TgtNodePres.empty, fun c hc hg => absurd ⟨c, hc, hg⟩ hgd⟩
  -- the frame half of the class tie
  have hfrT := genNodeFrameTie hμ hbase R h hparG hctxR ns ψ ρ xs
  -- the dynamic part: the admissible frames and the calls
  have H := dynCtx_of hbase hmkC hmk hag hsubC htr hcoreK hok hkids hpar hsem hF hparF hparS
  have hparams : SpineFit ρ (dR.params ψ) (xs.take dR.nP) := by
    obtain ⟨c0, hc0, hg0⟩ := hgd
    refine hparG c0 hc0 ψ ρ xs ?_
    unfold tgtClsG at hg0
    split at hg0
    · exact hg0.2
    · exact hg0
  have hxs : dR.nP ≤ xs.length := by
    have hl := SpineFit.length_eq hparams
    have hpl : (dR.params ψ).length = dR.nP := by
      have h0 := H.hΔ0 ψ
      rw [List.length_reverse, BlockData.holeCtx, List.length_append, List.length_map,
        List.length_range] at h0
      have hk : dR.k = (pp.nestCtx fvsP envI.find?).names.length := by
        rw [H.hnames]; exact (lfp_namesLen mpC H.hd0).symm
      have hnP := H.hnP
      simp only [ConLeche.NestCtx.hiAt] at h0
      omega
    rw [List.length_take, hpl] at hl
    omega
  have Dy : TgtNodeDyn μ F mpC (pp.nestCtx fvsP envI.find?) dR pp.toBlockShape
      (cvTasR.map (·.type)) out Dc mc cvc ns ψ ρ xs
      (genCallT (tgtClsTup dR Dc mc cvc pp.toBlockShape out ψ) ρ
        (fun c j => genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j)) := {
    Adm := nodeAdm mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs par
    hAdm := dyn_hAdm H ψ ρ xs hparams par
    top := dyn_top H ψ ρ xs hparams hxs hPP
    trans := dyn_trans H ψ ρ xs hparams hxs par
    hcall := genNodeCalls hμ hbase R h hg hTbl hmkC hmk hag hsubC htr hcoreK hok
      hkids hpar hsem hctxR hfrec hmemF hPP hF hcls hsel hparams hxs hfrT }
  have hrs : ∀ c (hc : c < (tgtRs out).length),
      (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := fun c hc => List.getElem?_eq_getElem hc
  refine tgtNodePres_of_list hcov hlfp hF hcls hsel (fun c hc => ?_) (fun c hc =>
      blockRulePdomsAV_length hμ mpC h (hrs c hc) ψ) (fun c hc hm => ?_) (fun c hc => ?_) Dy hfrT
    (fun c hc hM _ => hcovN c hc hM)
  · -- the prefix holds the parameters
    obtain ⟨hrP, -, hpl, -⟩ := genRec_at R hg hc
    show pp.nP ≤ _
    rw [hrP, hpl]; omega
  · -- a member class's component is a member
    obtain ⟨m, hmb⟩ : ∃ m, (tgtMajor out c).member = some m := Option.isSome_iff_exists.mp hm
    obtain ⟨hrt, -, hfi, -⟩ := (genRec_at R hg hc).2.2.2 m hmb
    rw [hrt]
    have hmk : m < dR.toLfp.k := by
      have h1 := (List.findIdx?_eq_some_iff_getElem.mp hfi).1
      have h2 : m < pp.toBlockShape.members.length := by
        simpa [ConLeche.BlockShape.memberNames] using h1
      obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
      exact h2
    exact Nat.lt_of_lt_of_le hmk (mpC.lfpClause_of_mem hlfp).kN
  · -- the carried constructors are the class's
    rw [genNCt R hg hdR hcls hc]
    have hco : c < out.length := by simpa [tgtRs] using hc
    unfold blockRecNCt tgtMajor
    simp [tgtRs, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hco]

/-- **THE CLASS INDUCTION AT THE GENERATED CALLS** (lane GENREC-B2's
target): `GenClassInd` at every level assignment and context value, from
the generated stage's context and run, the outside classes' data. -/
theorem genClassInd {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : GenRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      posR)
    (R : GenRecRun μ F (ConLeche.mkFEnv envI) envI (ConLeche.mkFEnv envC) pp.toBlockShape
      (ConLeche.blockNestedBit pp.toBlockShape kindsR) posR cvTasR block ctorsAsR out)
    (hg : ConLeche.ClassGenScoped R.g)
    (hTbl : ∀ e ∈ R.st.ctorNfs.toList, ConLeche.ScB pp.nP e.ty)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind) :
    ∀ ψ ρ, GenClassInd mpC.base2.acval envC pp.toBlockShape out dR Dc mc cvc
      (fun c j => genIhdAV mpC.base2.acval envC R.g R.rd (genBit pp ψ) ψ c j) ψ ρ := by
  intro ψ ρ
  exact tgtClassInd_of_pres fun xs =>
    genClassNodes hμ hctx R hg hTbl hcls hsel ψ ρ xs

end ConLeche.Model
