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
import ConLeche.Model.Inductives.TargetNodeCalls
import ConLeche.Model.Inductives.TargetNodeAdm
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.FamilyRun

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

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockShape TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun)

universe w

variable {V : Type w} [SetTheory V]

/-- The generated stage's context holds the shared one. -/
theorem GenRecCtx.base {F : Nat} {block : List ConstantInfo} {envC envI : Env}
    {pp : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → Term}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (h : GenRecCtx V F block envC envI pp out mpC dR isRecR A kindsR nfsR
      posR) :
    RecCtxBase V F envC envI pp mpC dR isRecR A kindsR nfsR posR := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -, h14⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14⟩

/-- **A listed node's key at its true frame fits each group member's run**:
the node's frame check types the key against every member's run
(`familyKeyCheck`, (g)), and the true valuation satisfies the node's stack
context (`dyn_trueVal_sat`), so the key's values fit the run's parameter
binders there (`keyRunFit`) — whether or not the node's frame fits its block. -/
private theorem dyn_nodeRunFit {F : Nat} {envI envC : Env} {mk : EnvModelM V envI}
    {mpC : EnvModelM V envC} {ctx : ConLeche.NestCtx} {d : BlockData V} {ns : List ConLeche.PosTree}
    (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {t : ConLeche.PosTree} (ht : t ∈ ns) {n : Name} (hn : n ∈ t.grp.map (·.1))
    {cv : ConstantVal} {caps : ConLeche.IndCaps} {ty : Expr}
    (hf : envI.find? n = some (.indInfo cv caps))
    (hrun : ConLeche.familyTelescope (ConLeche.fueledOps .verified F) envI cv caps = .ok ty)
    {ab : List Term} {u : Nat}
    (hta : denote mpC.base2.acval envC (nodeψ envC ψ t) 0 ty = some (mkPisAV ab (.sort u))) :
    SpineFit ρ (ab.take t.key.ds.length)
      (frameIdx t.key.ds.length (nodeFr mpC.base2.acval envC ctx ψ ρ xs t)) := by
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
  have hok := H.hok t ht
  -- the node's frame check of the member, against its run
  have hk := posD_frame_ktys hok.1 p hp
  obtain ⟨tyK, -, hfamK, hsp⟩ := familyKeyCheck_inv (by rw [H.hcov.find]; exact hf) hk
  rw [hrun] at hfamK
  obtain rfl : ty = tyK := by simpa using hfamK
  have hcerts := checkSpineAt_certs hsp
  -- the member's block, its run read
  obtain ⟨hD, -, hnN, hkN, -, _, _, _, cv0, _, _, hlps, hlpsOf, -, -, hlenP, -, hg⟩ :=
    dyn_nodeBlock H ht
  obtain ⟨mm', hmm', hpm⟩ := (hg.2.2 p hp).1
  obtain ⟨cv', caps', hf', hl'⟩ := hlps mm' hmm'
  rw [← hpm, hf] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  have hψ : nodeψ envC ψ t = Level.substFn ψ cv.levelParams t.key.lvls := by
    unfold nodeψ; rw [hlpsOf, hl']
  obtain ⟨hcl0, hbb0, -, hrd⟩ := familyRead mk hD hmm' (by rw [← hpm]; exact hf) hrun
  obtain ⟨ab', u', hta', hl, hv⟩ := hrd (Level.substFn ψ cv.levelParams t.key.lvls)
  rw [hψ, H.htr _ _ _ hta'] at hta
  obtain ⟨rfl, rfl⟩ := mkPisAV_sort_inj (Option.some.inj hta).symm
  -- the key's values at the true valuation fit the run's parameter binders
  have hpl := ((mk.lfpClause_of_mem hD).parsLen mm' hmm'
    (Level.substFn ψ cv.levelParams t.key.lvls)).trans (hlenP _)
  have hws := posNodeOk_dsAnc hok
  have hdsa := dyn_dsaI H ht ψ
  obtain ⟨-, hC, hL⟩ := H.hsem t ht ψ
  have hsT := dyn_trueVal_sat H ψ ρ xs hparams hxs _ t ht (Nat.le_refl _)
  have hfit := (keyRunFit mk (Rules.RulesInputs.ofSem mk ψ) hcl0 hbb0 hcerts hta'
    (fun ρ' => (hv ρ').2.1) (by rw [hl, List.length_append, hpl]; omega)
    (stackCtx_length_hi (m := mk.base2) (φ := ψ) (H.hΔ0 ψ) t.anc)
    (fun x hx => ⟨⟨(hws x hx).1, (hws x hx).2, hL x hx⟩, CtxOk.toS (hC x hx).toCtxOk⟩) hdsa
    _ hsT (fun x hx => CtxOk.leavesGr (hC x hx).toCtxOk hsT)).1
  have hxs' : ctx.nP ≤ xs.length := by rw [H.hnP]; exact hxs
  have htail : (fun j => trueVal mpC ctx ψ ρ xs t.anc (j + ctx.hiAt t.anc.length)) = ρ :=
    funext fun j => trueVal_tail mpC ctx ψ ρ xs hxs' t.anc j
  rw [htail] at hfit
  -- the node's true frame: the key at the true valuation
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ht
  have hget : ns.getD (i + 1 - 1) default = ns[i] := by
    rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
      Option.getD_some]
  have hfr := dyn_nlFr H (b := i + 1) (by omega) (by rw [hget]; exact ht) ψ ρ xs
  simp only [nlFr, Nat.add_one_ne_zero, ite_false, hget] at hfr
  rw [hfr]
  unfold keyFrame
  have hdl : (nodeDsaI mk ctx ψ ns[i]).length = ns[i].key.ds.length := by
    simp [nodeDsaI]
  have := frameIdx_consList' ((nodeDsaI mk ctx ψ ns[i]).map
    (interp V (trueVal mpC ctx ψ ρ xs ns[i].anc)))
    (fun j => trueVal mpC ctx ψ ρ xs ns[i].anc (j + ctx.hiAt ns[i].anc.length))
  rw [List.length_map, hdl] at this
  rw [this]
  exact hfit

/-- **The class tie at the generated stage** (`nestedClassNodes`): at the
generated stage's context, every choice of the outside classes' data and
every prefix spine, a node presentation at the GENERATED calls over the
positivity derivation's node list (`genRecCtx_nodes`), whose dynamic part
is the admissible frames with the generated calls (`genNodeCalls`), and
which covers every guarded class. -/
theorem genClassNodes {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → Term}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : GenRecCtx V F block envC envI pp out mpC dR isRecR A kindsR nfsR
      posR)
    (R : GenRecRun .verified F (ConLeche.mkFEnv envI) envI (ConLeche.mkFEnv envC) pp
      (ConLeche.blockNestedBit pp kindsR) posR block out)
    (hg : ConLeche.ClassGenScoped R.g)
    (hTbl : ∀ e ∈ R.st.ctorNfs.toList, ConLeche.ScB pp.nP e.ty)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind)
    (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    ∃ P : TgtNodePres envC mpC.base2.acval pp out dR Dc mc cvc ψ ρ xs
      (genCallT (tgtClsTup dR Dc mc cvc pp out ψ) ρ
        (fun c j => genIhdAV mpC.base2.acval envC R.g R.rd ψ c j)),
      TgtNodeHex P := by
  have hbase := hctx.base
  have hbase' := hbase
  obtain ⟨-, -, -, hndM, hN, hS, hcore, -, hdR, hlfp, hcov,
    ⟨mk, hmkC, hmk, hag, hsubC, hcoreK, htr⟩, -⟩ := hbase'
  have h := recStage_of_gen R hg
  have hmr : BlockMembersRun mpC.base2 dR pp := by
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; exact blockMembersRun_seam hN hS hcore
  have hparG := genParams_fit_run mpC R hg h hmr
  -- the node list
  obtain ⟨fvsP, ns, hctxR, hok, hkids, hpar, hsem, hfrec, hmemF, ⟨par, hPP⟩, hcovN⟩ :=
    genRecCtx_nodes hbase R mk hmkC hcoreK
  have hsp : ∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteSpine mpC.base2.acval envC ψ
      ((pp.nestCtx fvsP envI.find?).hiAt t.occ.length) t.key.ds dsa := by
    intro t ht ψ
    obtain ⟨dsa, hdsa⟩ := nodeSem_spOcc (hok t ht) (hsem t ht ψ)
    exact ⟨dsa, DenoteSpine.transport (fun e _ he => htr ψ _ e he) hdsa⟩
  obtain ⟨hparF, hparS⟩ := canonPars_of_forests hbase hmemF
  have hF := nodeListFacts_of hbase hok hpar hparF hparS hsp
  by_cases hgd : ∃ c, c < (tgtRs out).length ∧
      tgtClsG dR mpC.base2.acval envC pp out ψ ρ xs c
  case neg => exact ⟨TgtNodePres.empty, fun c hc hg => absurd ⟨c, hc, hg⟩ hgd⟩
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
  -- the frame half of the class tie: every listed node's key fits its members' runs
  have hfrT := genNodeFrameTie hbase R h hparG hg hcls hsel hctxR ns hF ψ ρ xs
    fun t ht n hn cv caps ty hf hrun ab u hta =>
      dyn_nodeRunFit H ψ ρ xs hparams hxs ht hn hf hrun hta
  have Dy : TgtNodeDyn F mpC (pp.nestCtx fvsP envI.find?) dR pp
      (pp.formers.map (·.type)) out Dc mc cvc ns ψ ρ xs
      (genCallT (tgtClsTup dR Dc mc cvc pp out ψ) ρ
        (fun c j => genIhdAV mpC.base2.acval envC R.g R.rd ψ c j)) := {
    Adm := nodeAdm mk mpC (pp.nestCtx fvsP envI.find?) dR ns ψ ρ xs par
    hAdm := dyn_hAdm H ψ ρ xs hparams hxs par
    top := dyn_top H ψ ρ xs hparams hxs hPP
    trans := dyn_trans H ψ ρ xs hparams hxs par
    hcall := genNodeCalls hbase R h hg hTbl hmkC hmk hag hsubC htr hcoreK hok
      hkids hpar hsem hctxR hfrec hmemF hPP hF hcls hsel hparams hxs hfrT }
  have hrs : ∀ c (hc : c < (tgtRs out).length),
      (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := fun c hc => List.getElem?_eq_getElem hc
  refine tgtNodePres_of_list hcov hlfp hF hcls hsel (fun c hc => ?_) (fun c hc =>
      blockRulePdomsAV_length mpC h (hrs c hc) ψ) (fun c hc hm => ?_) (fun c hc => ?_) Dy hfrT
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
      have h2 : m < pp.members.length := by
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
theorem genClassInd {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockShape}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → Term}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : GenRecCtx V F block envC envI pp out mpC dR isRecR A kindsR nfsR
      posR)
    (R : GenRecRun .verified F (ConLeche.mkFEnv envI) envI (ConLeche.mkFEnv envC) pp
      (ConLeche.blockNestedBit pp kindsR) posR block out)
    (hg : ConLeche.ClassGenScoped R.g)
    (hTbl : ∀ e ∈ R.st.ctorNfs.toList, ConLeche.ScB pp.nP e.ty)
    {Dc : Nat → LfpDatum V} {mc : Nat → Nat} {cvc : Nat → ConstantVal}
    (hcls : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c))
    (hsel : ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
      Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind) :
    ∀ ψ ρ, GenClassInd mpC.base2.acval envC pp out dR Dc mc cvc
      (fun c j => genIhdAV mpC.base2.acval envC R.g R.rd ψ c j) ψ ρ := by
  intro ψ ρ
  exact tgtClassInd_of_pres fun xs =>
    genClassNodes hctx R hg hTbl hcls hsel ψ ρ xs

end ConLeche.Model
