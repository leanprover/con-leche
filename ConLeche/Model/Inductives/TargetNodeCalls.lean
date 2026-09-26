module

public import ConLeche.Model.Inductives.TargetCallPatch
public import ConLeche.Model.Inductives.TargetCallKid
public import ConLeche.Model.Inductives.TargetCallAdm
public import ConLeche.Model.Inductives.TargetCallEval
public import ConLeche.Model.Inductives.TargetCallEntry
public import ConLeche.Model.Inductives.TargetCallFrame
public import ConLeche.Model.Inductives.TargetCallData
public import ConLeche.Model.Inductives.TargetCallWalk
import ConLeche.Model.Inductives.TargetCallLand
import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.TargetNestKit
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.TargetClasses
import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.TargetGuardParams
import ConLeche.Model.Inductives.BlockHoleRead
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Verify.Inductives.NestCallRun
import ConLeche.Verify.Inductives.PosNodes
import ConLeche.Semantics.EnvFacts
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.TargetNodeCover
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.BlockDeclRun

public section

/-!
# The calls at the admissible frames (lane NESTIND, session 28)

`NestedNodeCallsOwed` — every call of a rule at a related (class, node)
pair lands (`NodeLands`) — assembled from the calls' kit:

* the RULE side (`tgtCall_data`): the call's key, telescope and target,
  its typing (`targetCallOk`, K.53′) and the callee's major opened
  (`callMajor_open`);
* the WALK side at the node: the constructor's walked telescope at the
  node's frame (`dyn_ctorFit` at a derived node, `blk_ctorFit` at node
  `0`), its recorded entry (`FrameRec`, `nestMemberNfs`) and K.53′ there
  (`k53_pos`, `k53_zero`), the called field's leaf (`callWalkSyn`);
* the SEMANTICS at an admissible visit: the node's valuation (a derived
  node's group holes over its admissible valuation, `admVal_kid`; node
  `0`'s patched frame, `admVal_patch`), the call's target in the leaf's
  reading (`fieldCall_core`), and the landing per leaf: a member hole
  (`admVal_memberLand`), a frame hole (`admVal_frameLand`), a container
  instance at a kid (`former_foldl_mem`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx
  NestHole NestCtorNf NestNodes BinderMeta BlockParts BlockShape TargetMajor fueledOps PosD PosTree
  PosKind PosNodeOk nestHoleConst closeTelescope targetPiDomsWith targetMajorNfs targetFieldNfs
  openPisAtFvars)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Small kit -/

theorem Expr.ErasedEqL.symm : ∀ {as bs : List Expr}, Expr.ErasedEqL as bs → Expr.ErasedEqL bs as
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨ConLeche.Expr.ErasedEq.symm h1, Expr.ErasedEqL.symm h2⟩

theorem Expr.ErasedEqL.length_eq : ∀ {as bs : List Expr}, Expr.ErasedEqL as bs →
    as.length = bs.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h2⟩ => by simp [Expr.ErasedEqL.length_eq h2]

/-- **The least tuple reads only the index sets below its width.** -/
theorem lfpTuple_congr_Is {w k : Nat} {Is Is' : Nat → V} {Φ : (Nat → V) → Nat → V}
    (h : ∀ m, m < k → Is m = Is' m) {m : Nat} (hm : m < k) :
    lfpTuple w k Is Φ m = lfpTuple w k Is' Φ m := by
  have hP : IsClosedTuple w k Is Φ = IsClosedTuple w k Is' Φ := by
    funext X
    apply propext
    unfold IsClosedTuple InTupleSpace TupleLe
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun c hc => h c hc ▸ h1 c hc, fun c hc => h c hc ▸ h2 c hc⟩
    · rintro ⟨h1, h2⟩
      exact ⟨fun c hc => (h c hc).symm ▸ h1 c hc, fun c hc => (h c hc).symm ▸ h2 c hc⟩
  have hch : ∀ {p q : (Nat → V) → Prop} (e : p = q) (hp : ∃ L, p L) (hq : ∃ L, q L),
      Classical.choose hp = Classical.choose hq := by
    intro p q e hp hq; subst e; rfl
  unfold lfpTuple
  rw [h m hm]
  by_cases hc : ∃ L, IsClosedTuple w k Is Φ L
  · have hc' : ∃ L, IsClosedTuple w k Is' Φ L := hP ▸ hc
    rw [dif_pos hc, dif_pos hc', hch hP hc hc', hP]
  · have hc' : ¬ ∃ L, IsClosedTuple w k Is' Φ L := hP ▸ hc
    rw [dif_neg hc, dif_neg hc']

/-- **A carrier at an admissible frame is the clause's** there, the index
sets agreeing below the width. -/
theorem lfpSClause_carrier_of {D : LfpDatum V} {ψ : Name → Nat} {ρp : Nat → V} {Is : Nat → V}
    (hIs : ∀ c, c < D.N → D.idx ψ ρp c = Is c) {m : Nat} (hm : m < D.N) :
    (lfpSClause D ψ Is).carrier ρp m = D.carrier ψ ρp m :=
  (lfpTuple_congr_Is hIs hm).symm

/-! ## K.53′ at the node's own entry -/

/-- **K.53′ at a derived node**: the constructor's walked telescope at the
node's frame is recorded (`FrameRec`); its entry is among the class's
normal forms (the major is the node's key read back, `NodeMajor`), so the
called field of that telescope, opened at the rule's fields, is the
callee's major type under the field's telescope, up to annotations. -/
theorem k53_pos {ops : ConLeche.CheckerOps CheckM} {envI : Env} {ctx : NestCtx} {aux : NestNodes}
    {u : PosTree} (hok : PosNodeOk ops envI ctx u)
    (hfrec : ConLeche.FrameRec ops envI ctx aux.ctors u.anc u.key.lvls u.key.ds u.grp)
    {M : TargetMajor} (hNM : NodeMajor ctx M u) (hnfs : M.nfs = targetMajorNfs aux M.lvls M.ds)
    {ctors : List (ConstantVal × Nat)}
    (hctors : ConLeche.groupCtors ctx u.key.ds.length (u.grp.map (·.1)) = some ctors)
    {x : ConstantVal × Nat} (hx : x ∈ ctors) {crest : Expr} {ks : List PosKind}
    {nds : List (Expr × BinderMeta)} {cur : Expr} {ts' : List PosTree}
    (hcr : ConLeche.instPisWith u.key.ds ((x.1.type.instantiateLevelParams x.1.levelParams
      u.key.lvls).replaceConsts (ConLeche.grpSub u.key.lvls (ctx.hiAt u.anc.length) u.grp))
      = some crest)
    (hd : PosD ops envI ctx (.tele ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length)
      u.grp).reverse ++ u.anc) (ctx.hiAt u.anc.length + u.grp.length) x.2 0 crest ks nds cur) ts')
    {cn : Name} (hcn : x.1.name = cn)
    {μ' : CheckMode} {F' : Nat} {envW : Env} {fam : ConLeche.TargetFamily}
    {fvsPref fvsF fnorm : List Expr} {teles : List (List (Expr × BinderMeta))}
    {absM : Expr → Expr} {base k : Nat} {pw : ConLeche.PropWhen} {ih : ConLeche.TargetIh}
    (hcall : ConLeche.targetCallOk (ConLeche.fueledOps μ' F') envW cn fam fvsPref fvsF fnorm teles
      absM base k pw (targetFieldNfs M cn fvsF) ih = .ok ())
    (C : ConLeche.TargetCallRun μ' F' envW fam fvsPref fvsF fnorm teles absM base k pw ih) :
    ((targetPiDomsWith fvsF ((closeTelescope nds (ctx.hiAt ((ConLeche.grpNews u.key.lvls u.key.ds
        (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc).length) cur).replaceFVars
        (nestHoleConst ctx ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length)
          u.grp).reverse ++ u.anc)))).getD [])[ih.field]?.map Expr.eraseFVarTys
      = some (Expr.mkPisOf (teles.getD ih.field []) C.majDom).eraseFVarTys := by
  have he := hfrec.entry hctors hx hcr hd
  have hhi : ctx.hiAt ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length)
      u.grp).reverse ++ u.anc).length = ctx.hiAt u.anc.length + u.grp.length := by
    simp only [List.length_append, List.length_reverse, ConLeche.grpNews, List.length_map,
      ConLeche.NestCtx.hiAt]
    omega
  rw [hhi]
  refine k53_entry hcall C hnfs he hcn hNM.2.2.1.symm ?_
  show Expr.ErasedEqL (u.key.ds.map (·.replaceFVars (nestHoleConst ctx
    ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc))))
    M.ds
  rw [entryDs_readback hok]
  exact Expr.ErasedEqL.symm hNM.2.2.2

/-! ## The parameters and the tail of a valuation -/

section ParTail

variable {μ : CheckMode} {envC : Env} (mpC : EnvModelM V μ envC) (ctx : NestCtx) (ψ : Name → Nat)
  (ρ : Nat → V) (xs : List V)

/-- The true valuation's parameters are the prefix's. -/
theorem trueVal_param (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) {v : Nat}
    (hv : v < ctx.nP) : trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - v) = xs.getD v pt := by
  unfold trueVal nodeTrueVal
  have hlv : (nodeHv mpC.base2.acval envC ctx ψ prog).length = ctx.names.length + prog.length := by
    simp [nodeHv, nodeHoleConsts]
  rw [consList_append]
  have hl2 : ((nodeHv mpC.base2.acval envC ctx ψ prog).map (interp V ρ)).length
      = ctx.names.length + prog.length := by rw [List.length_map, hlv]
  have e : ctx.hiAt prog.length - 1 - v
      = (ctx.nP - 1 - v) + ((nodeHv mpC.base2.acval envC ctx ψ prog).map (interp V ρ)).length := by
    rw [hl2]; simp only [ConLeche.NestCtx.hiAt]; omega
  rw [e, consList_apply_add, consList_getD_of_lt _ _ _ (by rw [List.length_take]; omega),
    List.length_take, show min ctx.nP xs.length - 1 - (ctx.nP - 1 - v) = v by omega,
    List.getD_eq_getElem?_getD, List.getElem?_take, if_pos hv, ← List.getD_eq_getElem?_getD]

/-- The true valuation's tail is the context's. -/
theorem trueVal_tail (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) (q : Nat) :
    trueVal mpC ctx ψ ρ xs prog (q + ctx.hiAt prog.length) = ρ q := by
  unfold trueVal nodeTrueVal
  have hlv : (xs.take ctx.nP ++ (nodeHv mpC.base2.acval envC ctx ψ prog).map (interp V ρ)).length
      = ctx.hiAt prog.length := by
    simp [nodeHv, nodeHoleConsts, ConLeche.NestCtx.hiAt]; omega
  rw [← hlv, consList_apply_add]

/-- **Off the holes, the true valuation's**: a valuation agreeing with the
true one off the holes has its parameters and its tail. -/
theorem parTail_of_agree (hxs : ctx.nP ≤ xs.length) {prog : List NestHole} {σ : Nat → V}
    (hag : AgreeOff (holeP (ctx.hiAt prog.length) ctx.nP (ctx.hiAt prog.length)) σ
      (trueVal mpC ctx ψ ρ xs prog)) :
    (∀ v, v < ctx.nP → σ (ctx.hiAt prog.length - 1 - v) = xs.getD v pt) ∧
    (∀ q, σ (q + ctx.hiAt prog.length) = ρ q) := by
  refine ⟨fun v hv => ?_, fun q => ?_⟩
  · rw [hag _ fun h => by have := h.2.1; simp only [ConLeche.NestCtx.hiAt] at this ⊢; omega]
    exact trueVal_param mpC ctx ψ ρ xs hxs prog hv
  · rw [hag _ fun h => by have := h.1; omega]
    exact trueVal_tail mpC ctx ψ ρ xs hxs prog q

end ParTail

/-- **A derived node's constructor stack is read**: its holes — the
members, its frames' and its group's — are stored constants at their
level counts at the constructors' environment. -/
theorem nodeHolesRead_grp {μ : CheckMode} {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI}
    {mpC : EnvModelM V μ envC} {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}
    (H : DynCtx F mk mpC ctx d ns) {u : PosTree} (hu : u ∈ ns)
    (hrd : NodeHolesRead envC ctx u.occ) :
    NodeHolesRead envC ctx
      ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc) := by
  intro a ha
  simp only [nodeHoleConsts, List.mem_append, List.mem_map, List.reverse_append,
    List.reverse_reverse] at ha
  rcases ha with ⟨n, hn, rfl⟩ | ⟨hk, hkm, rfl⟩
  · exact hrd _ (by simp only [nodeHoleConsts, List.mem_append, List.mem_map]; exact Or.inl ⟨n, hn, rfl⟩)
  · rcases hkm with hkm | hkm
    · -- a frame below: the node's own stack
      obtain ⟨-, -, -, -, -, hanc⟩ := H.hok u hu
      rcases hanc with ⟨hao, -⟩ | ⟨han, -⟩
      · refine hrd _ ?_
        simp only [nodeHoleConsts, List.mem_append, List.mem_map, List.mem_reverse]
        exact Or.inr ⟨hk, by rw [← hao]; exact List.mem_reverse.mp hkm, rfl⟩
      · rw [han] at hkm; exact nomatch hkm
    · -- the node's own group
      simp only [ConLeche.grpNews, List.mem_map] at hkm
      obtain ⟨p, hp, rfl⟩ := hkm
      obtain ⟨-, -, -, hinst, -⟩ := posD_frame_inv (H.hok u hu).1
      obtain ⟨nI, hrun⟩ := hinst p hp
      obtain ⟨cvC, capsC, hfC, hlv⟩ := ConLeche.nestInstType_lvls hrun
      obtain ⟨D, hD, -, h2⟩ := posNodeOk_blk H.hcov (H.hok u hu) p.1 (List.mem_map_of_mem hp)
      obtain ⟨nPc, ctorsAs, henvC⟩ := H.henvC
      obtain ⟨lps, hl⟩ := blk_lps_envC H.hcov H.hsub henvC hD
      obtain ⟨i, hi, hpi⟩ := exists_member_of_mem_names (lfp_namesLen mk hD) h2
      obtain ⟨cv, caps, hf, hfI, -⟩ := hl i hi
      rw [hpi] at hf hfI
      rw [H.hcov.find, hfI] at hfC
      obtain ⟨rfl, rfl⟩ : cv = cvC ∧ caps = capsC := by simpa using hfC
      exact ⟨p.1, _, _, rfl, hf, hlv⟩

/-! ## THE CALLS -/

set_option maxHeartbeats 16000000 in
/-- **THE CALLS AT THE ADMISSIBLE FRAMES** (see the module docstring). -/
theorem nestedNodeCallsOwed {μ : CheckMode} (hμ : μ.verifiedChecks = true) (F : Nat)
    (block : List ConstantInfo) : NestedNodeCallsOwed V μ F block := by
  intro envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hctx mk hmkC hmk hag
    hsubC htr hcoreK fvsP ns hok hown hkids hpar hsem hfrec hmemF par hPP hF Dc mc cvc hcls hsel ψ ρ
    xs hgd c b hc hR t j fs ht hHF c' t' y hc' ht' hy hcall
  have H := dynCtx_of hctx hmkC hmk hag hsubC htr hcoreK hok hown hkids hpar hsem hF
  have hctx' := hctx
  obtain ⟨hRec, hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov, -, -⟩ := hctx'
  obtain ⟨R, hRaux⟩ := ConLeche.targetRecCheck_run_aux
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have h := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  have hmr : BlockMembersRun mpC.base2 dR pp.toBlockShape cvTasR := by
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; exact blockMembersRun_seam hN hS hcore
  have hM : BlockModelAt mpC.base2 dR.memberNames dR := by
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR; exact blockModelAt_seam h hN hS hcore hlfp
  -- the prefix's parameters
  have hparams : SpineFit ρ (dR.params ψ) (xs.take dR.nP) := by
    obtain ⟨c0, hc0, hg0⟩ := hgd
    exact tgtGuard_params hμ hctx hc0 hg0
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
  have hrs : ∀ c (hc : c < (tgtRs out).length),
      (tgtRs out)[c]? = some ((tgtRs out)[c]'hc) := fun c hc => List.getElem?_eq_getElem hc
  have hnPc : ∀ c, c < (tgtRs out).length →
      (pp.nestCtx fvsP envI.find? envI.consts).nP ≤ tgtRP pp.toBlockShape c := by
    intro c hc
    obtain ⟨-, hlen, hall⟩ := ConLeche.recStageG_recNames h
    obtain ⟨_, _, _, _, -, -, hle, -⟩ := hall c (by rw [← hlen]; exact hc)
    exact hle
  have hpd : ∀ c, c < (tgtRs out).length →
      (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
        = tgtRP pp.toBlockShape c := fun c hc => blockRulePdomsAV_length hμ mpC h (hrs c hc) ψ
  -- the rule side: the class's decoding, fitting the rule
  obtain ⟨hDeq, hψeq, hFreq⟩ := nlRel_tie (Dc := Dc) (mc := mc) (cvc := cvc) hcov hF hcls hsel
    hnPc hpd hc hR
  have hti : t ∈ˢ tgtClsIs dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c := by
    unfold tgtClsIs; rw [if_pos hR.1, hDeq, hψeq, hFreq]; exact ht
  have hfitC : tgtClsFit dR Dc mc cvc mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c t j fs := by
    unfold tgtClsFit; rw [hDeq, hψeq, hFreq]; exact hHF
  have hjC : j < blockRecNCt (tgtRs out) c := by
    have hj0 := hHF.1
    rw [← hDeq] at hj0
    have hnCt : blockRecNCt (tgtRs out) c
        = (tgtClsD dR Dc out c).nctors (tgtClsM mc pp.toBlockShape out c) := by
      unfold blockRecNCt
      rw [List.getD_eq_getElem?_getD, hrs c hc, Option.getD_some]
      by_cases hm : (tgtMajor out c).member.isSome = true
      · simp only [tgtClsD, tgtClsM, hm, if_true]
        rw [← tgtCls_hctM h hdR c _ (tgtMemAt_of_member hc hm) (hrs c hc)]
        rfl
      · have hMo : (tgtMajor out c).member = none := by
          cases h' : (tgtMajor out c).member with
          | none => rfl
          | some _ => rw [h'] at hm; exact absurd rfl hm
        have hm' : (tgtMajor out c).member.isSome = false := by rw [hMo]; rfl
        simp only [tgtClsD, tgtClsM, hm', Bool.false_eq_true, if_false]
        rw [tgtRs_ctors (hrs c hc)]
        exact (hcls c hc hMo).hlen
    rw [hnCt]; exact hj0
  have hspF := tgtCls_hspF hμ hcov h R hcls hdR hcore hmr hM ψ ρ 0 xs c hc j hjC t fs hti hfitC
  rw [tgtFdomsK, liftDomsK_zero] at hspF
  have hxsP : xs.length = pp.toBlockShape.rulePrefixAt c :=
    (tgtClsIs_pref hti).length_eq.trans (blockRulePdomsAV_length hμ mpC h (hrs c hc) ψ)
  obtain ⟨rc, rhs0, rhs, cA, Q, ih, bs, hcA, hrP, hQF, hQP, hfvF, hfvP, hfvW, hih, hfld, hfsl, hxl,
    hcallOk, hidxLen, hrPc, hcal, hidxB, hbs, hv⟩ :=
    tgtCall_data hμ hcov h R hcls hdR hS hcore hmr ψ ρ hc hjC hspF hxsP _ hcall
  obtain ⟨C⟩ := ConLeche.targetCallOk_run hcallOk
  -- the callee's major, opened at the call's telescope
  generalize htele : (Q.fnorm.map fun t => t.piBinders.1).getD ih.field [] = tele at hidxB hbs hv C
  have hosL := locOpen_locList (rc.rP + cA.2) tele.length
  obtain ⟨I, us, P, hmajO, hment, hshape⟩ := callMajor_open h R C hQP hfvP hcal hidxLen hrPc
    hosL.allFvars (by rw [hosL.1]; exact fun x hx => (hidxB x hx).1)
  have hctxN : (pp.nestCtx fvsP envI.find? envI.consts).names = pp.toBlockShape.memberNames := rfl
  have hfvF' : ∀ l, l < Q.fvsF.length → ∃ ty, Q.fvsF[l]? = some (.fvar (rc.rP + l) ty) :=
    fun l hl => hfvF l (hQF ▸ hl)
  have hmajO' : C.majDom.instantiateList (locOpen (rc.rP + Q.fvsF.length) tele.length) 0
      = Expr.mkAppN (.const I us) (P ++ ih.idx.map (·.instantiateList
        (locOpen (rc.rP + cA.2) tele.length) 0)) := by rw [hQF]; exact hmajO
  have hwb : ∀ d e w, (fueledOps .verified F).whnf envI d e = .ok w →
      e.looseBVarsBounded 0 = true → w.looseBVarsBounded 0 = true :=
    fun d e w hw hb => ConLeche.whnf_looseBVars mk.base2.wf F hw hb
  have hnPr : (pp.nestCtx fvsP envI.find? envI.consts).nP ≤ rc.rP := by
    rw [hrP]
    simpa [ConLeche.BlockShape.rulePrefixAt, List.getD_eq_getElem?_getD, tgtRP] using hnPc c hc
  have hxsC : (pp.nestCtx fvsP envI.find? envI.consts).nP ≤ xs.length := by rw [H.hnP]; exact hxs
  have hfvWF : ∀ x ∈ Q.fvsF, Expr.WScoped (rc.rP + Q.fvsF.length) x := by rw [hQF]; exact hfvW
  have hflF : fs.length = Q.fvsF.length := by rw [hQF, hfsl]
  by_cases hb0 : b = 0
  · sorry
  /- ### A derived node -/
  have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
  obtain ⟨-, ⟨-, hb0'⟩ | ⟨-, hbl, hNM⟩⟩ := hR
  · exact absurd hb0' hb0
  have hu : ns.getD (b - 1) default ∈ ns := getD_mem_of_lt hbpos hbl
  generalize hub : ns.getD (b - 1) default = u at hu hNM
  have hMo : (tgtMajor out c).member = none := hNM.1
  have hTO := hcls c hc hMo
  have hnlDb : nlDb mpC dR ns b = lfpSel mpC dR.toLfp u.key.cname := by
    unfold nlDb; rw [if_neg hb0, hub]
  have hnlψ : nlψ envC ns ψ b = nodeψ envC ψ u := by unfold nlψ; rw [if_neg hb0, hub]
  have hDc : Dc c = lfpSel mpC dR.toLfp u.key.cname := by
    have := hDeq; rw [hnlDb] at this; simpa [tgtClsD, hMo] using this
  have hmc : tgtClsM mc pp.toBlockShape out c = mc c := by simp [tgtClsM, hMo]
  have hm : mc c < (lfpSel mpC dR.toLfp u.key.cname).k := hDc ▸ hTO.hmm
  have hjn : j < (lfpSel mpC dR.toLfp u.key.cname).nctors (mc c) := by
    have := hHF.1; rwa [hnlDb, hmc] at this
  obtain ⟨cv, nF, ctors, crest, ks, nds, cur, ts', hcvI, hctors, hxmem, hcr, hd, hts', hndl, hcrC,
    hcurC, hndC, hsemU⟩ := dyn_ctorFit H hu ψ hm hjn
  -- the rule's constructor is the node's
  have hcAM : (tgtMajor out c).ctors[j]? = some cA := by
    rw [← tgtRs_ctors (hrs c hc)]; exact hcA
  have hjM : j < (tgtMajor out c).ctors.length := (List.getElem?_eq_some_iff.mp hcAM).1
  have hcAj : (tgtMajor out c).ctors[j] = cA := by
    rw [List.getElem?_eq_getElem hjM] at hcAM; exact Option.some.inj hcAM
  have hcn : (cv, nF).1.name = cA.1.name := by
    have e1 := ConLeche.Semantics.Env.find?_name hcvI
    have e2 := ConLeche.Semantics.Env.find?_name (hTO.hctor j hjM)
    rw [hDc] at e2
    simp only [ConLeche.ConstantInfo.name] at e1 e2
    rw [hcAj] at e2
    exact e1.trans e2.symm
  have hnfs : (tgtMajor out c).nfs = targetMajorNfs nodesR (tgtMajor out c).lvls
      (tgtMajor out c).ds := by
    have hmem : out.getD c default ∈ out := by
      have hco : c < out.length := by simpa [tgtRs] using hc
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hco, Option.getD_some]
      exact List.getElem_mem hco
    rw [← hRaux]; exact ConLeche.targetRecRun_nfs R _ hmem
  have hK := k53_pos (H.hok u hu) (hfrec u hu) hNM hnfs hctors hxmem hcr hd hcn hcallOk C
  rw [htele] at hK
  generalize hprog : (ConLeche.grpNews u.key.lvls u.key.ds
    ((pp.nestCtx fvsP envI.find? envI.consts).hiAt u.anc.length) u.grp).reverse ++ u.anc = prog
    at hK
  have hhiP : (pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length
      = (pp.nestCtx fvsP envI.find? envI.consts).hiAt u.anc.length + u.grp.length := by
    rw [← hprog]
    simp only [List.length_append, List.length_reverse, ConLeche.grpNews, List.length_map,
      ConLeche.NestCtx.hiAt]
    omega
  rw [hprog, ← hhiP] at hd
  rw [← hhiP] at hndC
  -- the node's constructor at an admissible visit
  have hvisit : ∀ (G : Nat → Nat → V → V → Prop) (ρ' : Nat → V),
      nodeAdm mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs par b G ρ' →
      ∀ Y, InTupleSpace ((nlDb mpC dR ns b).w (nlψ envC ns ψ b)) (nlDb mpC dR ns b).N
          ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
            (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y →
      (nlDb mpC dR ns b).HFits (nlψ envC ns ψ b) ρ' Y t (tgtClsM mc pp.toBlockShape out c) j fs →
      ∃ σN, AdmVal mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs
          (fun i => if i < u.anc.length then holeOwner ns par b i else b)
          (addOwn G b (nlDb mpC dR ns b).N ((nlDb mpC dR ns b).idx (nlψ envC ns ψ b)
            (nlFr mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns ψ ρ xs b)) Y) prog σN ∧
        fs.length = nF ∧
        ∀ (i : Nat) (nd : Expr), nds[i]?.map (·.1) = some nd →
          ∃ nda, denoteMeta mpC.base2.acval envC ψ
              ((pp.nestCtx fvsP envI.find? envI.consts).hiAt prog.length + i) nd = some nda ∧
            fs.getD i pt ∈ˢ interp V (consList (fs.take i) σN) nda ∧
            AnnotValid V (consList (fs.take i) σN) nda := by
    intro G ρ' hA Y hY hH
    have hA' := hA
    unfold nodeAdm at hA'
    rw [if_neg hb0, hub] at hA'
    obtain ⟨σ, hσ, rfl⟩ := hA'
    have hidxEq := (dyn_hAdm H ψ ρ xs hparams par b (by omega) G _ hA).2
    rw [hnlDb, hnlψ, hmc] at hH
    rw [hnlDb, hnlψ] at hidxEq
    have hY' : InTupleSpace ((lfpSel mpC dR.toLfp u.key.cname).w (nodeψ envC ψ u))
        (lfpSel mpC dR.toLfp u.key.cname).N ((lfpSel mpC dR.toLfp u.key.cname).idx (nodeψ envC ψ u)
          (keyFrame (nodeDsaI mk (pp.nestCtx fvsP envI.find? envI.consts) ψ u)
            ((pp.nestCtx fvsP envI.find? envI.consts).hiAt u.anc.length) σ)) Y := by
      intro m' hm'
      rw [hidxEq m' hm']
      have := hY m' (by rw [hnlDb]; exact hm')
      rwa [hnlDb, hnlψ] at this
    obtain ⟨hsatN, hfl, hmem⟩ := hsemU σ hσ.sat Y hY' t fs hH
    refine ⟨_, admVal_kid H hbpos hbl hub hσ hsatN (fun i => rfl)
      (u' := .node [] prog default [] []) hprog.symm, hfl, fun i nd hnd => ?_⟩
    obtain ⟨nda, hnda, hmemI, hval⟩ := hmem i nd hnd
    rw [← hhiP] at hnda
    exact ⟨nda, H.htr ψ _ nd hnda, hmemI, hval⟩
  sorry

end ConLeche.Model
