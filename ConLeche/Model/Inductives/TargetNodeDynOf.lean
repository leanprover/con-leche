module

public import ConLeche.Model.Inductives.TargetNodeAdm
public import ConLeche.Model.Inductives.TargetNodeSem
import ConLeche.Model.Inductives.TargetNodeDyn
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.BlockHoleGrade
import ConLeche.Verify.Level
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.ContLeaf
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Verify.Inductives.PositivityInv
import ConLeche.Verify.Inductives.PosAnn
import ConLeche.Model.Env.LfpFormer
import ConLeche.Model.Inductives.TargetCallEntry

public section

/-!
# The node presentation's dynamic part: `hAdm`, `top`, `trans`

At the admissible frames `nodeAdm` (`TargetNodeAdm.lean`), which only a
LIVE node has (`nlLive`: its true frame fits its recorded block):

* the true valuation satisfies every node's stack context, live or not
  (`dyn_trueVal_sat`: a frame hole holds its container applied to the key,
  which inhabits the hole's type, the container's run instantiated at the
  key — the key fits the run's parameter binders, `grpRun_fit`);
* `hAdm` — an admissible frame fits the block where the true one does (the
  valuations agree off the holes, `keyFit_agree`), so it satisfies the
  node's parameter telescope, and reads the true frame's index sets (N2,
  `grp_idx_eq`);
* `top` — the TRUE valuation (the holes' constants) of a live node is
  admissible once the shallower live nodes' true elements satisfy `G`: a
  constant applied at full arity at its live owner's parameters is the
  owner's true carrier (`leaf`);
* `trans` — an admissible valuation is below the true one along a hole
  relation once `G`'s elements are true, so the frame's monotonicity
  (`FrameMono`, `posD_mono` at the node's derivation) moves a fit to the
  true frame (`trans_of_frameConcl`).

Node `0` (the block) is visited at its true frame only (`lfp_trans_self`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockShape BlockShape fueledOps PosTree PosNodeOk PosD)

universe w

variable {V : Type w} [SetTheory V]

/-! ## Readings -/

/-! ## The true valuation -/

section True

variable {envC : Env} (mpC : EnvModelM V envC) (ctx : NestCtx) (ψ : Name → Nat) (ρ : Nat → V)
  (xs : List V)

/-- **The true valuation of a stack grown by holes on top**: the new
holes' read-backs' values consed on the old stack's. -/
theorem trueVal_append (hs prog : List NestHole) :
    trueVal mpC ctx ψ ρ xs (hs ++ prog)
      = consList (((List.range hs.length).map fun j =>
          (denote mpC.base2.acval envC ψ xs.length
            (nodeImg ctx (hs ++ prog) (ctx.hiAt prog.length + j))).getD .prf).map
            (interp V (consList xs ρ))) (trueVal mpC ctx ψ ρ xs prog) := by
  unfold trueVal nodeTrueVal nodeHv
  rw [← consList_append, List.append_assoc, ← List.map_append]
  congr 3
  have hl : ctx.hiAt (hs ++ prog).length - ctx.nP
      = (ctx.hiAt prog.length - ctx.nP) + hs.length := by
    simp only [NestCtx.hiAt, List.length_append]; omega
  rw [hl, List.range_add, List.map_append, List.map_map]
  congr 1
  · refine List.map_congr_left fun i hi => ?_
    have hi' := List.mem_range.mp hi
    rw [nodeImg_suffix ctx hs prog (by simp only [NestCtx.hiAt] at hi' ⊢; omega)]
  · refine List.map_congr_left fun j _ => ?_
    simp only [Function.comp_apply]
    rw [show ctx.nP + (ctx.hiAt prog.length - ctx.nP + j) = ctx.hiAt prog.length + j by
      simp only [NestCtx.hiAt]; omega]

end True

/-! ## The context, bundled -/

/-- **What the dynamic part reads** (`nestedClassNodes`' node context,
bundled): the constructors' model `mpC` covered and recording the block;
the formers' model `mk` covering the walk's context, its blocks among
`mpC`'s (and `mpC`'s the block's or `mk`'s), its readings `mpC`'s; the
list's nodes, owned, closed under kids and parents, read in their stack
contexts; the class tie's node facts; the walk's context the block's. -/
structure DynCtx (F : Nat) {envI envC : Env} (mk : EnvModelM V envI) (mpC : EnvModelM V envC)
    (ctx : NestCtx) (d : BlockData V) (ns : List PosTree) : Prop where
  hcovC : LfpCover mpC []
  hd0 : d.toLfp ∈ mpC.lfpBlocks
  hcov : ContCover mk ctx
  hsub : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks
  hag : ∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n
  hsubC : ∀ D ∈ mpC.lfpBlocks, D = d.toLfp ∨ D ∈ mk.lfpBlocks
  htr : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : Term},
    denote mk.base2.acval envI ψ dd e = some ea → denote mpC.base2.acval envC ψ dd e = some ea
  henvC : ∃ (nP : Nat) (memberCtors : List (Name × List (ConstantVal × Nat))),
    envC = ConLeche.consBlockCtors nP memberCtors envI
  hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI ctx t
  hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns
  hpar : ∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids
  hsem : ∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ ctx (d.holeCtx ψ).reverse t
  hF : NodeListFacts mpC ctx ns
  hnP : ctx.nP = d.nP
  /-- the canonical parameters: the variables `0 ..< nP`, closed below -/
  hparF : ctx.params.length = ctx.nP ∧ ∀ (i : Nat) (x : Expr), ctx.params[i]? = some x →
    ∃ ty, x = .fvar i ty
  hparS : ∀ x ∈ ctx.params, ConLeche.ScB ctx.nP x
  hnames : ctx.names = d.toLfp.names
  hΔ0 : ∀ ψ, ((d.holeCtx ψ).reverse).length = ctx.hiAt 0
  hlpsM : ∀ n ∈ ctx.names, ∃ cv caps, envI.find? n = some (.indInfo cv caps) ∧
    cv.levelParams = ctx.lps
  hformers : ∃ (formers : List ConstantVal) (p : BlockShape) (isRec : Bool),
    BlockNamesOk (V := V) d formers ∧
    ∀ (c : Nat) (cvTb : ConstantVal), formers[c]? = some cvTb →
      FormerInEnv mk.base2 cvTb (ConLeche.blockCapsAt p c isRec) ∧
      FormerData mk.base2 cvTb (d.nP + d.nIdxAt c) d.resSort (d.ppsM c)

/-! ## A listed node's recorded block -/

/-- **A derived frame's group, its constructors and its walk**
(`PosD.frame`, inverted). -/
theorem posD_frame_full {ops : ConLeche.CheckerOps CheckM} {env : Env} {ctx : NestCtx}
    {prog : List NestHole} {us : List Level} {ds : List Expr} {grp : List (Name × Expr)}
    {ts : List PosTree} (h : PosD ops env ctx (.frame prog us ds grp) ts) :
    (grp.map (·.1)).Nodup ∧
    grp.map (·.1) = (grp.headD default).1 :: ConLeche.nestFrameMates ctx (grp.headD default).1 ∧
    ∃ ctors, ConLeche.groupCtors ctx ds.length (grp.map (·.1)) = some ctors ∧
      PosD ops env ctx (.ctors ((ConLeche.grpNews us ds (ctx.hiAt prog.length) grp).reverse ++ prog)
        (ctx.hiAt prog.length + grp.length) us ds (grp.map (·.1))
        (ConLeche.grpHoles (ctx.hiAt prog.length) grp) ctors) ts := by
  cases h with
  | frame _ _ _ hnd _ _ hgrp hctors _ hwalk => exact ⟨hnd, hgrp, _, hctors, hwalk⟩

/-- **A listed node's recorded block** (`nlDb` at the node): the block
`lfpSel` selects for the key's container is the formers' model's, as wide
as its members, every member in the frame's group (N2), the group's
head one of them, all at the head's level parameters (distinct), the
key's parameters its parameter count, the group well formed. -/
theorem dyn_nodeBlock {F : Nat} {envI envC : Env} {mk : EnvModelM V envI}
    {mpC : EnvModelM V envC} {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}
    (H : DynCtx F mk mpC ctx d ns) {t : PosTree} (ht : t ∈ ns) :
    lfpSel mpC d.toLfp t.key.cname ∈ mk.lfpBlocks ∧
    (lfpSel mpC d.toLfp t.key.cname).N = (lfpSel mpC d.toLfp t.key.cname).k ∧
    (lfpSel mpC d.toLfp t.key.cname).names.Nodup ∧
    (lfpSel mpC d.toLfp t.key.cname).names.length = (lfpSel mpC d.toLfp t.key.cname).k ∧
    (∀ c, c < (lfpSel mpC d.toLfp t.key.cname).k → InGrp (lfpSel mpC d.toLfp t.key.cname) t.grp c) ∧
    ∃ mm, mm < (lfpSel mpC d.toLfp t.key.cname).k ∧
      (lfpSel mpC d.toLfp t.key.cname).member mm = (t.grp.headD default).1 ∧
    ∃ cv caps, envI.find? ((lfpSel mpC d.toLfp t.key.cname).member mm) = some (.indInfo cv caps) ∧
      (∀ mm', mm' < (lfpSel mpC d.toLfp t.key.cname).k → ∃ cv' caps',
        envI.find? ((lfpSel mpC d.toLfp t.key.cname).member mm') = some (.indInfo cv' caps') ∧
        cv'.levelParams = cv.levelParams) ∧
      lpsOf envC t.key.cname = cv.levelParams ∧ cv.levelParams.Nodup ∧
      t.key.lvls.length = cv.levelParams.length ∧
      (∀ ψ', ((lfpSel mpC d.toLfp t.key.cname).params ψ').length = t.key.ds.length) ∧
      ((∃ nP' L, ConLeche.nestContainer ctx ((lfpSel mpC d.toLfp t.key.cname).member mm)
          = some (nP', L) ∧ L ≠ []) ∨ cv.levelParams.Nodup) ∧
      GrpWf envI ctx (lfpSel mpC d.toLfp t.key.cname) (ctx.hiAt t.anc.length) t.key.lvls t.key.ds
        t.grp := by
  have hok := H.hok t ht
  obtain ⟨hne, ⟨hnm, hquot⟩, ⟨L, hq⟩, hinst, hblk⟩ := posD_frame_inv hok.1
  obtain ⟨hnd, hgrp, ctors, hctors, hwalk⟩ := posD_frame_full hok.1
  -- the head and the key's container lie in one block of `mk`
  have hheadG : (t.grp.headD default).1 ∈ t.grp.map (·.1) := by
    obtain ⟨p₀, ps, hp⟩ := List.exists_cons_of_ne_nil hne
    rw [hp]; simp
  obtain ⟨D'', hD'', hC'', hH''⟩ := posNodeOk_blk H.hcov hok _ hheadG
  have hD''C := H.hsub D'' hD''
  obtain ⟨i, hi, hiC⟩ := exists_member_of_mem_names (lfp_namesLen mk hD'') hC''
  obtain ⟨cvC, capsC, hfC⟩ := LfpCover.member_find (mp := mpC) hD''C hi
  rw [hiC] at hfC
  obtain ⟨hDC, hDnames, hCD⟩ := lfpSel_spec H.hcovC d.toLfp hD''C hC'' hfC
  have hD''n := lfp_names_all H.hcovC hD''C hC'' hfC
  generalize hDdef : lfpSel mpC d.toLfp t.key.cname = D at *
  have hnames : D.names = D''.names := by rw [hDnames, hD''n]
  -- `D` is not the block itself: its head is no member
  have hD : D ∈ mk.lfpBlocks := by
    rcases H.hsubC D hDC with rfl | hD
    · exfalso
      have : (t.grp.headD default).1 ∈ ctx.names := by rw [H.hnames, hnames]; exact hH''
      rw [← List.contains_iff_mem] at this
      rw [hnm] at this
      exact Bool.false_ne_true this
    · exact hD
  have hkN := lfp_namesLen mk hD
  have hblkD := H.hcov.block D hD
  obtain ⟨mm, hmm, hmmH⟩ := exists_member_of_mem_names hkN (by rw [hnames]; exact hH'')
  -- the head's former
  obtain ⟨cv, caps, hfc⟩ := nestContainer_find hq
  rw [H.hcov.find] at hfc
  rw [← hmmH] at hfc hq
  obtain ⟨lps, hlps, hlenP0, hcvl, hnL⟩ := contBlock_facts mk H.hcov hD hmm hfc hq
  subst hcvl
  have hndl : cv.levelParams.Nodup :=
    frame_lps_nodup mk H.hcov hD hmm hlps (by rw [hmmH]; exact hheadG) hctors
      (posD_ctors_nodup hwalk) (hnL.imp (fun ⟨L', hL', hne'⟩ => ⟨_, L', hL', hne'⟩) id)
  -- the group's names are the block's (N2)
  have hall : ConLeche.nestBlockOf ctx ((t.grp.headD default).1) = D.names := by
    unfold ConLeche.nestBlockOf
    rw [← hmmH, H.hcov.find, hfc]
    exact hblkD.all mm hmm cv caps hfc
  have hgrpN : ∀ n ∈ t.grp.map (·.1), n ∈ D.names := by
    intro n hn
    rw [hgrp] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · rw [← hmmH]; exact getD_mem _ (by rw [hkN]; exact hmm)
    · unfold ConLeche.nestFrameMates at hn
      rw [hall] at hn
      exact List.mem_eraseDups.mp (List.mem_filter.mp hn).1
  -- the key's levels: at the head's count (K.51)
  obtain ⟨p₀, ps, hp⟩ := List.exists_cons_of_ne_nil hne
  have hp₀ : p₀ ∈ t.grp := by rw [hp]; exact List.mem_cons_self
  have hp₀H : p₀.1 = (t.grp.headD default).1 := by rw [hp]; rfl
  obtain ⟨nI, hnI⟩ := hinst p₀ hp₀
  obtain ⟨cvI, capsI, _, hfI, -, hFI⟩ := ConLeche.nestInstType_inv hnI
  have hul := hFI.lvls
  rw [H.hcov.find, hp₀H, ← hmmH, hfc] at hfI
  obtain ⟨rfl, rfl⟩ : cv = cvI ∧ caps = capsI := by simpa using hfI
  -- the key's container's level parameters, at the constructors' environment
  obtain ⟨nPc, memberCtors, henvC⟩ := H.henvC
  have hlpsC := posNodeOk_lps H.hcov H.hsub henvC hok _ hheadG
  obtain ⟨lps', hl'⟩ := blk_lps_envC H.hcov H.hsub henvC hD
  obtain ⟨cv', caps', hfC', hfI', hcl'⟩ := hl' mm hmm
  rw [hfc] at hfI'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hfI'
  refine ⟨hD, H.hcovC.wid D hDC, hblkD.nodup, hkN, fun c hc => ⟨hc, ?_⟩, mm, hmm, hmmH, cv, caps,
    hfc, hlps, ?_, hndl, hul, fun ψ' => hlenP0 ψ',
    hnL.imp (fun ⟨L', hL', hne'⟩ => ⟨_, L', hL', hne'⟩) id,
    (frame_grpOk mk H.hcov hne hnd hinst hgrp (posD_frame_ktys hok.1) hD hmm hmmH hlps).2⟩
  · -- every member is in the group
    have hmem : D.member c ∈ D.names := getD_mem _ (by rw [hkN]; exact hc)
    rw [List.contains_iff_mem, hgrp]
    by_cases hc0 : D.member c = (t.grp.headD default).1
    · rw [hc0]; exact List.mem_cons_self
    · refine List.mem_cons_of_mem _ ?_
      unfold ConLeche.nestFrameMates
      rw [hall]
      exact List.mem_filter.mpr ⟨List.mem_eraseDups.mpr hmem, by simpa using hc0⟩
  · rw [hlpsC]
    unfold lpsOf
    rw [← hmmH, hfC']
    rfl

/-! ## The true valuation's holes -/

section Pos

variable {envC : Env} (mpC : EnvModelM V envC) (ctx : NestCtx) (ψ : Name → Nat) (ρ : Nat → V)
  (xs : List V)

theorem trueVal_pos (prog : List NestHole) {k : Nat} (hk : k < ctx.names.length + prog.length)
    (hxs : ctx.nP ≤ xs.length) :
    trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.nP + k))
      = interp V (consList xs ρ) ((denote mpC.base2.acval envC ψ xs.length
          (nodeImg ctx prog (ctx.nP + k))).getD .prf) := by
  unfold trueVal nodeTrueVal
  have hlv : (nodeHv mpC.base2.acval envC ctx ψ prog xs.length).length
      = ctx.names.length + prog.length := by
    simp only [nodeHv, List.length_map, List.length_range, NestCtx.hiAt]; omega
  have hlen : (xs.take ctx.nP ++ (nodeHv mpC.base2.acval envC ctx ψ prog xs.length).map
      (interp V (consList xs ρ))).length = ctx.hiAt prog.length := by
    rw [List.length_append, List.length_take, List.length_map, hlv]
    simp only [ConLeche.NestCtx.hiAt]; omega
  rw [consList_apply_lt _ _ _ (by rw [hlen]; simp only [ConLeche.NestCtx.hiAt]; omega), hlen,
    show ctx.hiAt prog.length - 1 - (ctx.hiAt prog.length - 1 - (ctx.nP + k)) = ctx.nP + k by
      simp only [ConLeche.NestCtx.hiAt]; omega,
    List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
    show ctx.nP + k - min ctx.nP xs.length = k by omega, List.getElem?_map]
  unfold nodeHv
  rw [List.getElem?_map, List.getElem?_range (by simp only [NestCtx.hiAt]; omega)]
  simp

/-- **A member hole's read-back, read at the prefix**: the member applied to
the block's parameters (the prefix's). -/
theorem memberImg_val (hpar : ctx.params.length = ctx.nP ∧ ∀ (i : Nat) (x : Expr),
      ctx.params[i]? = some x → ∃ ty, x = .fvar i ty)
    (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) {t : Nat} (ht : t < ctx.names.length)
    (hc : denote mpC.base2.acval envC ψ xs.length
      (.const (ctx.names[t]'ht) (ctx.lps.map Level.param))
        = some (mpC.base2.acval (ctx.names[t]'ht) ψ)) :
    interp V (consList xs ρ) ((denote mpC.base2.acval envC ψ xs.length
        (nodeImg ctx prog (ctx.nP + t))).getD .prf)
      = (xs.take ctx.nP).foldl app (interp V ρ (mpC.base2.acval (ctx.names[t]'ht) ψ)) := by
  have himg : nodeImg ctx prog (ctx.nP + t)
      = Expr.mkAppN (.const (ctx.names[t]'ht) (ctx.lps.map Level.param)) ctx.params := by
    unfold nodeImg
    rw [ite_eq_right (by omega)]
    have := ConLeche.nestHoleImg_suffix (ctx := ctx) prog [] (v := ctx.nP + t)
      (by simp only [NestCtx.hiAt, List.length_nil]; omega)
    rw [List.append_nil] at this
    rw [this]
    simp only [ConLeche.nestHoleImg]
    rw [ite_eq_left ⟨by omega, by simp only [NestCtx.hiAt]; omega⟩,
      show ctx.nP + t - ctx.nP = t by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem ht, Option.getD_some]
    rfl
  have hsp := denoteSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
    xs.length ctx.params 0 (fun i x hx => by simpa using hpar.2 i x hx)
  rw [himg, denote_mkAppN hsp hc, Option.getD_some, interp_mkAppN_foldl,
    acval_interp_closed mpC.base2 _ ψ _ ρ, List.map_map]
  congr 1
  rw [hpar.1]
  refine List.ext_getElem (by simp; omega) fun i h1 h2 => ?_
  simp only [List.getElem_map, List.getElem_range, Function.comp_apply, List.getElem_take,
    Nat.zero_add]
  rw [interp_bvar, consList_getD_of_lt _ _ _ (by simp at h1; omega),
    show xs.length - 1 - (xs.length - 1 - i) = i by simp at h1; omega,
    List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at h1; omega), Option.getD_some]

/-- **A member hole of the true valuation** holds the member applied to the
block's parameters (the prefix's). -/
theorem trueVal_member (hpar : ctx.params.length = ctx.nP ∧ ∀ (i : Nat) (x : Expr),
      ctx.params[i]? = some x → ∃ ty, x = .fvar i ty)
    (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) {t : Nat} (ht : t < ctx.names.length)
    (hc : denote mpC.base2.acval envC ψ xs.length
      (.const (ctx.names[t]'ht) (ctx.lps.map Level.param))
        = some (mpC.base2.acval (ctx.names[t]'ht) ψ)) :
    trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.nP + t))
      = (xs.take ctx.nP).foldl app (interp V ρ (mpC.base2.acval (ctx.names[t]'ht) ψ)) := by
  rw [trueVal_pos mpC ctx ψ ρ xs prog (by omega) hxs]
  exact memberImg_val mpC ctx ψ ρ xs hpar hxs prog ht hc

end Pos

/-! ## Owners -/

/-! ## A listed node's true frame -/

section Frames

variable {F : Nat} {envI envC : Env} {mk : EnvModelM V envI} {mpC : EnvModelM V envC}
  {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}

/-- A listed node's key is read where its frame is derived: `nodeDsaI`. -/
theorem dyn_dsaI (H : DynCtx F mk mpC ctx d ns) {t : PosTree} (ht : t ∈ ns) (ψ : Name → Nat) :
    DenoteSpine mk.base2.acval envI ψ (ctx.hiAt t.anc.length) t.key.ds (nodeDsaI mk ctx ψ t) := by
  obtain ⟨dsa, hdsa⟩ := (H.hsem t ht ψ).1
  rw [nodeDsaI, DenoteSpine.getD_eq hdsa]
  exact hdsa

/-- **A listed node's TRUE frame** (`nlFr`) is its key read where its frame
is derived (`nodeDsaI`, the formers' model) at the true valuation of those
frames. -/
theorem dyn_nlFr (H : DynCtx F mk mpC ctx d ns) {b : Nat} (hb : b ≠ 0)
    (ht : ns.getD (b - 1) default ∈ ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) :
    nlFr mpC ctx d ns ψ ρ xs b
      = keyFrame (nodeDsaI mk ctx ψ (ns.getD (b - 1) default))
          (ctx.hiAt (ns.getD (b - 1) default).anc.length)
          (trueVal mpC ctx ψ ρ xs (ns.getD (b - 1) default).anc) := by
  unfold nlFr
  rw [ite_eq_right hb]
  generalize ns.getD (b - 1) default = t at ht ⊢
  obtain ⟨dsa, hdsa⟩ := (H.hsem t ht ψ).1
  have hI : nodeDsaI mk ctx ψ t = dsa := by rw [nodeDsaI, DenoteSpine.getD_eq hdsa]
  rw [hI]
  unfold nodeFr
  obtain ⟨-, -, -, -, -, hanc⟩ := H.hok t ht
  rcases hanc with ⟨hao, -⟩ | ⟨han, hds⟩
  · rw [hao] at hdsa ⊢
    rw [DenoteSpine.getD_eq (DenoteSpine.transport (fun e _ he => H.htr ψ _ e he) hdsa)]
    rfl
  · rw [han] at hdsa ⊢
    have hlift := DenoteSpine.lift (m := mk.base2) (φ := ψ) (h := ctx.hiAt 0)
      (D := ctx.hiAt t.occ.length) (by simp only [NestCtx.hiAt]; omega) (fun x hx => (hds x hx).2)
      hdsa
    rw [DenoteSpine.getD_eq (DenoteSpine.transport (fun e _ he => H.htr ψ _ e he) hlift)]
    have htv : nodeTrueVal ctx.nP (nodeHv mpC.base2.acval envC ctx ψ t.occ xs.length) xs ρ
        = trueVal mpC ctx ψ ρ xs (t.occ ++ []) := by rw [List.append_nil]; rfl
    rw [htv, trueVal_append]
    generalize hvs : (List.map (interp V (consList xs ρ)) (List.map (fun j =>
      (denote mpC.base2.acval envC ψ xs.length
        (nodeImg ctx (t.occ ++ []) (ctx.hiAt ([] : List NestHole).length + j))).getD .prf)
        (List.range t.occ.length))) = vs
    have hvl : vs.length = t.occ.length := by rw [← hvs]; simp
    have e1 : ctx.hiAt t.occ.length - ctx.hiAt 0 = vs.length := by
      rw [hvl]; simp only [NestCtx.hiAt]; omega
    have e2 : ctx.hiAt t.occ.length = ctx.hiAt 0 + vs.length := by
      rw [hvl]; simp only [NestCtx.hiAt]; omega
    rw [e1, e2, keyFrame_lift]
    rfl

/-- **A frame hole of the true valuation** (the `i`-th of a stack whose
suffix below it ends in its owner `o`'s frames) holds its container applied
to the owner's key at the owner's true valuation: its read-back is its
container applied to the owner's key read back, which reads as the key there
(`readback_spine`). -/
theorem trueVal_frameApp (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hxs : ctx.nP ≤ xs.length) {o : PosTree} (ho : o ∈ ns)
    {prog : List NestHole} {i : Nat} {hk : NestHole} (hi : prog.reverse[i]? = some hk)
    (hsuf : ∃ Y, prog.drop (prog.length - i) = Y ++ o.anc)
    (hkm : hk ∈ ConLeche.grpNews o.key.lvls o.key.ds (ctx.hiAt o.anc.length) o.grp) :
    trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))
      = ((nodeDsaI mk ctx ψ o).map (interp V (trueVal mpC ctx ψ ρ xs o.anc))).foldl app
          (interp V (trueVal mpC ctx ψ ρ xs o.anc) (mk.base2.acval hk.key.cname (nodeψ envC ψ o))) := by
  have hil : i < prog.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1; simpa using this
  obtain ⟨hD, -, hnN, hkN, -, mm, hmm, hmmH, cv, caps, hfc, hlps, hlpsOf, -, hul, hlenP, -, hg⟩ :=
    dyn_nodeBlock H ho
  generalize lfpSel mpC d.toLfp o.key.cname = D at *
  have hψ : nodeψ envC ψ o = Level.substFn ψ cv.levelParams o.key.lvls := by
    unfold nodeψ; rw [hlpsOf]
  rw [hψ]
  -- the hole's member
  simp only [ConLeche.grpNews, List.mem_map] at hkm
  obtain ⟨p, hp, rfl⟩ := hkm
  obtain ⟨mm', hmm', hpm⟩ := (hg.2.2 p hp).1
  simp only
  rw [hpm]
  obtain ⟨cv', caps', hf', hl'⟩ := hlps mm' hmm'
  -- its position and read-back
  have e : ctx.hiAt 0 + i = ctx.nP + (ctx.names.length + i) := by
    simp only [NestCtx.hiAt]; omega
  rw [e, trueVal_pos mpC ctx ψ ρ xs prog (by omega) hxs]
  have himg : nodeImg ctx prog (ctx.nP + (ctx.names.length + i))
      = Expr.mkAppN (.const (D.member mm') o.key.lvls) (o.key.ds.map (nodeRb ctx o.anc)) := by
    unfold nodeImg
    rw [ite_eq_right (by omega)]
    have hfi := ConLeche.nestHoleImg_frame (ctx := ctx) hi
    rw [show ctx.hiAt i = ctx.nP + (ctx.names.length + i) by simp only [NestCtx.hiAt]; omega]
      at hfi
    rw [hfi, Option.getD_some]
    simp only
    rw [hpm]
    obtain ⟨Y, hY⟩ := hsuf
    rw [hY]
    congr 1
    refine List.map_congr_left fun x hx => ?_
    unfold nodeRb
    exact replaceFVars_congr_below (fun v hv => ConLeche.nestHoleImg_suffix Y o.anc hv) x
      (posNodeOk_dsAnc (H.hok o ho) x hx).1.fvarsBelow
  -- the read-back key, read
  have hrd : NodeHolesRead mpC.base2.acval envC ctx o.anc := by
    have h := H.hF.read o ho
    obtain ⟨-, -, -, -, -, hanc⟩ := H.hok o ho
    rcases hanc with ⟨hao, -⟩ | ⟨han, -⟩
    · rwa [hao]
    · rw [han]
      have h' : NodeHolesRead mpC.base2.acval envC ctx (o.occ ++ []) := by
        rwa [List.append_nil]
      exact h'.suffix
  obtain ⟨dsa, hdsa⟩ := (H.hsem o ho ψ).1
  have hdsaC := DenoteSpine.transport (fun e _ he => H.htr ψ _ e he) hdsa
  obtain ⟨ebs, hebs, hmap⟩ := readback_spine mpC.base2 (hrd.hs ψ hxs) (consList xs ρ)
    (fun x hx => (posNodeOk_dsAnc (H.hok o ho) x hx).1) hdsaC
  have hlen' : o.key.lvls.length = cv'.levelParams.length := by rw [hl', hul]
  have hc := H.htr ψ xs.length _ (denote_const (acval := mk.base2.acval) (φ := ψ)
    (d := xs.length) hf' hlen')
  rw [himg, denote_mkAppN hebs hc, Option.getD_some, interp_mkAppN_foldl, hmap,
    substE_nodeImgX_trueVal mpC.base2 ψ ρ hxs]
  have hI : nodeDsaI mk ctx ψ o = dsa := by rw [nodeDsaI, DenoteSpine.getD_eq hdsa]
  rw [hI, acval_interp_closed mk.base2 _ _ (consList xs ρ) (trueVal mpC ctx ψ ρ xs o.anc),
    show (ConstantInfo.indInfo cv' caps').toConstantVal = cv' from rfl, hl']
  rfl

/-- **A frame hole of the true valuation, at a key frame that satisfies its
owner's parameters**, holds its owner's hole value at the owner's true frame and
carrier (`trueVal_frameApp`; a recorded former applied to its block's parameters
is its hole value at the carrier, `former_app_eq`). -/
theorem trueVal_frameVal (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hxs : ctx.nP ≤ xs.length) {o : PosTree} (ho : o ∈ ns)
    (hkey : Sat V ((lfpSel mpC d.toLfp o.key.cname).params (nodeψ envC ψ o)).reverse
      (keyFrame (nodeDsaI mk ctx ψ o) (ctx.hiAt o.anc.length) (trueVal mpC ctx ψ ρ xs o.anc)))
    {prog : List NestHole} {i : Nat} {hk : NestHole} (hi : prog.reverse[i]? = some hk)
    (hsuf : ∃ Y, prog.drop (prog.length - i) = Y ++ o.anc)
    (hkm : hk ∈ ConLeche.grpNews o.key.lvls o.key.ds (ctx.hiAt o.anc.length) o.grp) :
    trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))
      = (lfpSel mpC d.toLfp o.key.cname).holeVal (nodeψ envC ψ o)
          (keyFrame (nodeDsaI mk ctx ψ o) (ctx.hiAt o.anc.length) (trueVal mpC ctx ψ ρ xs o.anc))
          ((lfpSel mpC d.toLfp o.key.cname).carrier (nodeψ envC ψ o)
            (keyFrame (nodeDsaI mk ctx ψ o) (ctx.hiAt o.anc.length)
              (trueVal mpC ctx ψ ρ xs o.anc)))
          ((lfpSel mpC d.toLfp o.key.cname).names.idxOf hk.key.cname) := by
  rw [trueVal_frameApp H ψ ρ xs hxs ho hi hsuf hkm]
  obtain ⟨hD, -, hnN, hkN, -, _, _, _, _, _, _, hlps, -, -, -, hlenP, -, hg⟩ := dyn_nodeBlock H ho
  simp only [ConLeche.grpNews, List.mem_map] at hkm
  obtain ⟨p, hp, rfl⟩ := hkm
  obtain ⟨mm', hmm', hpm⟩ := (hg.2.2 p hp).1
  simp only
  rw [hpm, idxOf_member hnN hkN hmm']
  have hfe := former_app_eq mpC (H.hsub _ hD) hmm' hkey (trueVal mpC ctx ψ ρ xs o.anc)
  have hdl : ((lfpSel mpC d.toLfp o.key.cname).params (nodeψ envC ψ o)).length
      = ((nodeDsaI mk ctx ψ o).map (interp V (trueVal mpC ctx ψ ρ xs o.anc))).length := by
    rw [List.length_map, hlenP, nodeDsaI, List.length_map]
  rw [hdl] at hfe
  unfold keyFrame at hfe
  rw [frameIdx_consList'] at hfe
  obtain ⟨cv', caps', hf', -⟩ := hlps mm' hmm'
  unfold keyFrame
  rw [← hfe, ← H.hag _ (by rw [hf']; rfl)]

/-- **The true valuation satisfies the stack context** at every listed
node's frames, whether or not they fit: the block's parameters, then each
member's hole value (`blockHoleCtx_sat`), then each frame's group — its
members applied to the key at the parent's true valuation, which inhabit the
group's hole types, its members' runs instantiated at the key (`grpRun_fit`:
the key fits the runs' parameter binders) — by induction along the parents. -/
theorem dyn_trueVal_sat (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length) :
    ∀ (n : Nat) (t : PosTree), t ∈ ns → t.anc.length ≤ n →
      Sat V (stackCtx mk.base2 ψ ctx t.anc (d.holeCtx ψ).reverse) (trueVal mpC ctx ψ ρ xs t.anc) := by
  have hxs' : ctx.nP ≤ xs.length := by rw [H.hnP]; exact hxs
  have base : Sat V (stackCtx mk.base2 ψ ctx [] (d.holeCtx ψ).reverse)
      (trueVal mpC ctx ψ ρ xs []) := by
    obtain ⟨formers, p, isRec, hN, hF⟩ := H.hformers
    have hkN : d.toLfp.names.length = d.k := lfp_namesLen mpC H.hd0
    obtain ⟨hC, -, -, -⟩ := mpC.lfp_ok _ H.hd0
    rw [stackCtx_nil]
    unfold trueVal nodeTrueVal
    rw [consList_append]
    have hlenP : (d.params ψ).length = d.nP := by
      have := hparams.length_eq; rw [List.length_take] at this; omega
    have hρp : Sat V (d.params ψ).reverse (consList (xs.take d.nP) ρ) := by
      have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hparams
      rwa [List.append_nil] at this
    have hρp' : Sat V (d.params ψ).reverse (consList (xs.take ctx.nP) ρ) := by
      rw [H.hnP]; exact hρp
    refine blockHoleCtx_sat mk hN hF (fun t' ht' ψ' ρ' h => hC.parsSat t' ht' ψ' ρ' h) ψ _
      hρp' _ ?_ ?_
    · simp only [nodeHv, List.length_map, List.length_range, NestCtx.hiAt, List.length_nil,
        H.hnames]
      rw [hkN]; omega
    · intro t' ht'
      have htn : t' < ctx.names.length := by rw [H.hnames, hkN]; exact ht'
      obtain ⟨cv, caps, hf, hlps⟩ := H.hlpsM _ (List.getElem_mem htn)
      have hc : denote mpC.base2.acval envC ψ xs.length
          (.const (ctx.names[t']'htn) (ctx.lps.map Level.param))
            = some (mpC.base2.acval (ctx.names[t']'htn) ψ) := by
        have h1 := H.htr ψ xs.length _ (denote_const (acval := mk.base2.acval) (φ := ψ)
          (d := xs.length) hf
          (show (ctx.lps.map Level.param).length = cv.levelParams.length by
            rw [List.length_map, hlps]))
        rw [h1, show (ConstantInfo.indInfo cv caps).toConstantVal = cv from rfl, hlps,
          ConLeche.Level.substFn_param_self, H.hag _ (by rw [hf]; rfl)]
      have hv := memberImg_val mpC ctx ψ ρ xs H.hparF hxs' [] htn hc
      have hlt : t' < ctx.hiAt ([] : List NestHole).length - ctx.nP := by
        simp only [NestCtx.hiAt, List.length_nil, H.hnames]; rw [hkN]; omega
      show ((nodeHv mpC.base2.acval envC ctx ψ [] xs.length).map
        (interp V (consList xs ρ))).getD t' pt = _
      unfold nodeHv
      rw [List.map_map, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hlt,
        Option.map_some, Option.getD_some, Function.comp_apply]
      rw [hv, show d.memberName t' = ctx.names[t']'htn by
        show d.memberNames.getD t' .anonymous = _
        rw [List.getD_eq_getElem?_getD, ← show d.toLfp.names = d.memberNames from rfl,
          ← H.hnames, List.getElem?_eq_getElem htn, Option.getD_some],
        acval_interp_closed mpC.base2 _ ψ ρ (consList (xs.take ctx.nP) ρ),
        H.hag _ (by rw [hf]; rfl), ← H.hnP]
      have hfi := frameIdx_consList' (xs.take ctx.nP) ρ
      rw [List.length_take, Nat.min_eq_left hxs'] at hfi
      rw [hfi]
  intro n
  induction n with
  | zero =>
    intro t ht hn
    rw [List.length_eq_zero_iff.mp (by omega : t.anc.length = 0)]
    exact base
  | succ n ihn =>
    intro t ht hn
    by_cases hanc0 : t.anc = []
    · rw [hanc0]; exact base
    · -- a frame's group over its parent's frames
      obtain ⟨-, -, -, -, -, hanc⟩ := H.hok t ht
      have hao : t.anc = t.occ := by
        rcases hanc with ⟨hao, -⟩ | ⟨han, -⟩
        · exact hao
        · exact absurd han hanc0
      obtain ⟨u, hu, htu⟩ := H.hpar t ht (by rw [← hao]; exact hanc0)
      have hocc := (H.hok u hu).2.2.1 t htu
      obtain ⟨hne, -, -, -, -⟩ := posD_frame_inv (H.hok u hu).1
      have hgl : 0 < u.grp.length := List.length_pos_iff.mpr hne
      have hta : t.anc = (ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length)
          u.grp).reverse ++ u.anc := by rw [hao, hocc]
      have hlt : u.anc.length < t.anc.length := by
        rw [hta]; simp [ConLeche.grpNews]; omega
      have ih := ihn u hu (by omega)
      obtain ⟨hD, -, hnN, hkN, -, mm, hmm, hmmH, cv, caps, hfc, hlps, hlpsOf, hndl, hul, hlenP,
        -, hg⟩ := dyn_nodeBlock H hu
      have hdsa := dyn_dsaI H hu ψ
      rw [hta]
      -- the stack: the group's hole types on top
      rw [stackCtx_frame (posD_frame_inv (H.hok u hu).1).2.2.2.1 u.anc]
      -- the true valuation: the group's hole values on top
      have hψ : nodeψ envC ψ u = Level.substFn ψ cv.levelParams u.key.lvls := by
        unfold nodeψ; rw [hlpsOf]
      -- the group's members applied to the key at the parent's true valuation
      generalize hvs : u.grp.map (fun p => ((nodeDsaI mk ctx ψ u).map
          (interp V (trueVal mpC ctx ψ ρ xs u.anc))).foldl app
            (interp V (trueVal mpC ctx ψ ρ xs u.anc)
              (mk.base2.acval p.1 (Level.substFn ψ cv.levelParams u.key.lvls)))) = vs
      have htv : trueVal mpC ctx ψ ρ xs ((ConLeche.grpNews u.key.lvls u.key.ds
            (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc)
          = consList vs (trueVal mpC ctx ψ ρ xs u.anc) := by
        generalize hG : ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp = G
        have hGl : G.length = u.grp.length := by rw [← hG]; simp [ConLeche.grpNews]
        have hvl : vs.length = G.length := by rw [← hvs]; simp [hGl]
        funext q
        by_cases hq : q < G.length
        · -- a group hole
          rw [consList_getD_of_lt _ _ _ (by rw [hvl]; exact hq), hvl]
          have hj : G.length - 1 - q < G.length := by omega
          have hi : (G.reverse ++ u.anc).reverse[u.anc.length + (G.length - 1 - q)]?
              = some G[G.length - 1 - q] := by
            rw [List.reverse_append, List.reverse_reverse,
              List.getElem?_append_right (by simp), List.length_reverse,
              show u.anc.length + (G.length - 1 - q) - u.anc.length = G.length - 1 - q by omega,
              List.getElem?_eq_getElem hj]
          have hsuf : ∃ Y, (G.reverse ++ u.anc).drop ((G.reverse ++ u.anc).length
              - (u.anc.length + (G.length - 1 - q))) = Y ++ u.anc :=
            ⟨_, by rw [List.drop_append_of_le_length
              (by simp only [List.length_append, List.length_reverse]; omega)]⟩
          have hkm : G[G.length - 1 - q] ∈ ConLeche.grpNews u.key.lvls u.key.ds
              (ctx.hiAt u.anc.length) u.grp := by rw [hG]; exact List.getElem_mem _
          have hpos : q = ctx.hiAt (G.reverse ++ u.anc).length - 1
              - (ctx.hiAt 0 + (u.anc.length + (G.length - 1 - q))) := by
            simp only [NestCtx.hiAt, List.length_append, List.length_reverse]; omega
          have hfv := trueVal_frameApp H ψ ρ xs hxs' hu hi hsuf hkm
          rw [← hpos] at hfv
          rw [hfv, hψ, ← hvs]
          simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
          have hj' : G.length - 1 - q < u.grp.length := by omega
          rw [List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some]
          have : G[G.length - 1 - q] = ⟨⟨u.grp[G.length - 1 - q].1, u.key.lvls, u.key.ds⟩,
              ctx.hiAt u.anc.length, u.grp[G.length - 1 - q].2.piBinders.1.length⟩ := by
            subst hG; simp [ConLeche.grpNews]
          rw [this]
        · -- below the group: the parent's frames
          obtain ⟨r, rfl⟩ : ∃ r, q = r + G.length := ⟨q - G.length, by omega⟩
          rw [← hvl, consList_apply_add, hvl, trueVal_append]
          have hl2 : ((List.map (interp V (consList xs ρ)) (List.map (fun j =>
              (denote mpC.base2.acval envC ψ xs.length
                (nodeImg ctx (G.reverse ++ u.anc) (ctx.hiAt u.anc.length + j))).getD .prf)
              (List.range G.reverse.length)))).length = G.length := by simp
          rw [← hl2, consList_apply_add]
      rw [htv]
      obtain ⟨-, hC, hL⟩ := H.hsem u hu ψ
      rw [← hvs]
      exact sat_of_spineFit ih (grpRun_fit mk hD hnN hkN H.hcov.find hlps hndl hul
        (posNodeOk_dsAnc (H.hok u hu)) hdsa (hlenP _) hg (Rules.RulesInputs.ofSem mk ψ)
        (stackCtx_length_hi (H.hΔ0 ψ) u.anc) hC hL _ ih)

/-- **`hAdm`**: an admissible frame is a live node's (node `0` always is)
and satisfies the node's parameter telescope: at a derived node the true
frame fits the block, hence so does the admissible one (they agree off the
holes and satisfy the stack context, `keyFit_agree`); and it reads the true
frame's index sets below the width (N2, `grp_idx_eq`, every member in the
frame's group). -/
theorem dyn_hAdm (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length) (par : Nat → Nat) :
    ∀ b, b < ns.length + 1 → ∀ G ρ', nodeAdm mk mpC ctx d ns ψ ρ xs par b G ρ' →
      nlLive mpC ctx d ns ψ ρ xs b ∧
      Sat V ((nlDb mpC d ns b).params (nlψ envC ns ψ b)).reverse ρ' ∧
      ∀ c, c < (nlDb mpC d ns b).N → (nlDb mpC d ns b).idx (nlψ envC ns ψ b) ρ' c
        = (nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b) c := by
  intro b hb G ρ' hadm
  by_cases hb0 : b = 0
  · subst hb0
    unfold nodeAdm at hadm
    rw [ite_eq_left rfl] at hadm
    subst hadm
    refine ⟨by unfold nlLive; rw [ite_eq_left rfl]; trivial, ?_, fun _ _ => rfl⟩
    simp only [nlDb, nlψ, nlFr, ite_true]
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hparams
    rw [List.append_nil] at this
    exact this
  · have ht := getD_mem_of_lt (ns := ns) (b := b) (by omega) (by omega)
    unfold nodeAdm at hadm
    rw [ite_eq_right hb0] at hadm
    obtain ⟨hlive, σ, hσ, rfl⟩ := hadm
    refine ⟨hlive, ?_⟩
    unfold nlLive at hlive
    rw [ite_eq_right hb0] at hlive
    rw [dyn_nlFr H hb0 ht ψ ρ xs,
      show nlDb mpC d ns b = lfpSel mpC d.toLfp (ns.getD (b - 1) default).key.cname by
        unfold nlDb; rw [ite_eq_right hb0],
      show nlψ envC ns ψ b = nodeψ envC ψ (ns.getD (b - 1) default) by
        unfold nlψ; rw [ite_eq_right hb0]] at hlive ⊢
    generalize ns.getD (b - 1) default = t at ht hσ hlive ⊢
    obtain ⟨hD, hwid, hnN, hkN, hall, mm, hmm, hmmH, cv, caps, hfc, hlps, hlpsOf, hndl, hul, hlenP,
      -, hg⟩ := dyn_nodeBlock H ht
    have hψ : nodeψ envC ψ t = Level.substFn ψ cv.levelParams t.key.lvls := by
      unfold nodeψ; rw [hlpsOf]
    rw [hψ] at hlive ⊢
    have hws := posNodeOk_dsAnc (H.hok t ht)
    have hdsa := dyn_dsaI H ht ψ
    obtain ⟨-, hC, hL⟩ := H.hsem t ht ψ
    have hsT := dyn_trueVal_sat H ψ ρ xs hparams hxs _ t ht (Nat.le_refl _)
    have hin := Rules.RulesInputs.ofSem mk ψ
    have hΔ := stackCtx_length_hi (m := mk.base2) (φ := ψ) (H.hΔ0 ψ) t.anc
    have hk' : KeyFit (lfpSel mpC d.toLfp t.key.cname) (Level.substFn ψ cv.levelParams t.key.lvls)
        (nodeDsaI mk ctx ψ t) (ctx.hiAt t.anc.length) σ :=
      keyFit_agree mk hD hnN hkN H.hcov.find hlps hws hdsa (hlenP _) hg hin hΔ hC hL
        (fun i hi => (hσ.agree i hi).symm) hsT hσ.sat hlive
    refine ⟨hk'.1, fun c hc => ?_⟩
    rw [hwid] at hc
    exact grp_idx_eq mk hD hnN hkN H.hcov.find hlps hws hdsa (hlenP _) hg hin hΔ hC hL (hall c hc)
      hσ.agree hσ.sat hsT hk' hlive

/-- **An admissible valuation of a live node's frames fits** at the node's
key frame: the true one does, and they agree off the holes (`keyFit_agree`). -/
theorem dyn_keyFitAdm (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {b : Nat} (hb0 : b ≠ 0) (hbl : b ≤ ns.length) (hlive : nlLive mpC ctx d ns ψ ρ xs b)
    {own : Nat → Nat} {G : Nat → Nat → V → V → Prop} {σ : Nat → V}
    (hσ : AdmVal mk mpC ctx d ns ψ ρ xs own G (ns.getD (b - 1) default).anc σ) :
    KeyFit (lfpSel mpC d.toLfp (ns.getD (b - 1) default).key.cname)
      (nodeψ envC ψ (ns.getD (b - 1) default)) (nodeDsaI mk ctx ψ (ns.getD (b - 1) default))
      (ctx.hiAt (ns.getD (b - 1) default).anc.length) σ := by
  have ht := getD_mem_of_lt (ns := ns) (b := b) (by omega) hbl
  unfold nlLive at hlive
  rw [ite_eq_right hb0, dyn_nlFr H hb0 ht ψ ρ xs,
    show nlDb mpC d ns b = lfpSel mpC d.toLfp (ns.getD (b - 1) default).key.cname by
      unfold nlDb; rw [ite_eq_right hb0],
    show nlψ envC ns ψ b = nodeψ envC ψ (ns.getD (b - 1) default) by
      unfold nlψ; rw [ite_eq_right hb0]] at hlive
  generalize ns.getD (b - 1) default = t at ht hσ hlive ⊢
  obtain ⟨hD, -, hnN, hkN, -, _, _, _, cv, _, _, hlps, hlpsOf, -, -, hlenP, -, hg⟩ :=
    dyn_nodeBlock H ht
  have hψ : nodeψ envC ψ t = Level.substFn ψ cv.levelParams t.key.lvls := by
    unfold nodeψ; rw [hlpsOf]
  rw [hψ] at hlive ⊢
  obtain ⟨-, hC, hL⟩ := H.hsem t ht ψ
  exact keyFit_agree mk hD hnN hkN H.hcov.find hlps (posNodeOk_dsAnc (H.hok t ht))
    (dyn_dsaI H ht ψ) (hlenP _) hg (Rules.RulesInputs.ofSem mk ψ)
    (stackCtx_length_hi (m := mk.base2) (φ := ψ) (H.hΔ0 ψ) t.anc) hC hL
    (fun i hi => (hσ.agree i hi).symm) (dyn_trueVal_sat H ψ ρ xs hparams hxs _ t ht (Nat.le_refl _))
    hσ.sat hlive

/-! ## The true valuation's holes, read at full arity -/

/-- **A member hole of the true valuation at full arity**, at a fitting
index spine, is node `0`'s true carrier there: the member applied to the
block's parameters is its hole value at the carrier (`former_app_eq`). -/
theorem dyn_memberLeaf (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    (prog : List NestHole) {t : Nat} (ht : t < ctx.names.length) {is : List V}
    (hfit : SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) is) :
    is.foldl app (trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.nP + t)))
      = app (d.toLfp.carrier ψ (consList (xs.take d.nP) ρ) t) (tupW (d.toLfp.u t ψ) is) := by
  have hkN := lfp_namesLen mpC H.hd0
  have htk : t < d.toLfp.k := by rw [← hkN, ← H.hnames]; exact ht
  have hxs' : ctx.nP ≤ xs.length := by rw [H.hnP]; exact hxs
  obtain ⟨cv, caps, hf, hlps⟩ := H.hlpsM _ (List.getElem_mem ht)
  have hc : denote mpC.base2.acval envC ψ xs.length
      (.const (ctx.names[t]'ht) (ctx.lps.map Level.param))
        = some (mpC.base2.acval (ctx.names[t]'ht) ψ) := by
    have h1 := H.htr ψ xs.length _ (denote_const (acval := mk.base2.acval) (φ := ψ)
      (d := xs.length) hf
      (show (ctx.lps.map Level.param).length = cv.levelParams.length by
        rw [List.length_map, hlps]))
    rw [h1, show (ConstantInfo.indInfo cv caps).toConstantVal = cv from rfl, hlps,
      ConLeche.Level.substFn_param_self, H.hag _ (by rw [hf]; rfl)]
  rw [trueVal_member mpC ctx ψ ρ xs H.hparF hxs' prog ht hc]
  have hmem : d.toLfp.member t = ctx.names[t] := by
    unfold LfpDatum.member
    rw [List.getD_eq_getElem?_getD, ← H.hnames, List.getElem?_eq_getElem ht, Option.getD_some]
  have hsP : Sat V (d.toLfp.params ψ).reverse (consList (xs.take ctx.nP) ρ) := by
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hparams
    rw [List.append_nil] at this
    rw [H.hnP]; exact this
  have hlP : (d.toLfp.params ψ).length = (xs.take ctx.nP).length := by
    have := hparams.length_eq
    rw [List.length_take] at this ⊢; rw [H.hnP]; exact this.symm
  have hfe := former_app_eq mpC H.hd0 htk hsP ρ
  rw [hlP, frameIdx_consList', hmem] at hfe
  rw [hfe, LfpDatum.holeVal_app hfit, H.hnP]

/-- **An owner's frame is its hole's key at the true valuation**: a listed
owner's group and frames a suffix of the stack. -/
theorem dyn_ownerFrame (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    {o : Nat} (ho : o ≠ 0) (hu : ns.getD (o - 1) default ∈ ns) {prog X : List NestHole}
    (hX : prog = X ++ (ConLeche.grpNews (ns.getD (o - 1) default).key.lvls
      (ns.getD (o - 1) default).key.ds (ctx.hiAt (ns.getD (o - 1) default).anc.length)
      (ns.getD (o - 1) default).grp).reverse ++ (ns.getD (o - 1) default).anc)
    {hk : NestHole}
    (hk_mem : hk ∈ ConLeche.grpNews (ns.getD (o - 1) default).key.lvls
      (ns.getD (o - 1) default).key.ds (ctx.hiAt (ns.getD (o - 1) default).anc.length)
      (ns.getD (o - 1) default).grp)
    {dsa : List Term}
    (hdsa : DenoteSpine mk.base2.acval envI ψ (ctx.hiAt prog.length) hk.key.ds dsa) :
    keyFrame dsa (ctx.hiAt prog.length) (trueVal mpC ctx ψ ρ xs prog)
      = nlFr mpC ctx d ns ψ ρ xs o := by
  rw [dyn_nlFr H ho hu ψ ρ xs]
  generalize ns.getD (o - 1) default = u at hu hX hk_mem ⊢
  have hds : hk.key.ds = u.key.ds := by
    simp only [ConLeche.grpNews, List.mem_map] at hk_mem
    obtain ⟨p, -, rfl⟩ := hk_mem
    rfl
  rw [hds] at hdsa
  subst hX
  generalize hG : (ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp) = G at hdsa ⊢
  rw [trueVal_append]
  generalize hvs : List.map (interp V (consList xs ρ)) (List.map (fun j =>
    (denote mpC.base2.acval envC ψ xs.length
      (nodeImg ctx (X ++ G.reverse ++ u.anc) (ctx.hiAt u.anc.length + j))).getD .prf)
      (List.range (X ++ G.reverse).length)) = vs
  have hvl : vs.length = X.length + G.length := by rw [← hvs]; simp
  have hlen : ctx.hiAt (X ++ G.reverse ++ u.anc).length = ctx.hiAt u.anc.length + vs.length := by
    rw [hvl]; simp only [List.length_append, List.length_reverse, ConLeche.NestCtx.hiAt]; omega
  rw [hlen] at hdsa ⊢
  have hlift := DenoteSpine.lift (m := mk.base2) (φ := ψ) (h := ctx.hiAt u.anc.length)
    (D := ctx.hiAt u.anc.length + vs.length) (by omega)
    (fun x hx => (posNodeOk_dsAnc (H.hok u hu) x hx).1) (dyn_dsaI H hu ψ)
  rw [DenoteSpine.unique hdsa hlift, Nat.add_sub_cancel_left, keyFrame_lift]

omit [SetTheory V] in
/-- A stack ending in its owner's group and frames has, below any of the
group's holes, a suffix ending in the owner's frames. -/
theorem stack_suffix {X G A prog : List NestHole} (hX : prog = X ++ G ++ A) {i : Nat}
    (hle : A.length ≤ i) (hi : i ≤ prog.length) :
    ∃ Y, prog.drop (prog.length - i) = Y ++ A :=
  ⟨_, by subst hX; rw [List.drop_append_of_le_length (by simp at hi ⊢; omega)]⟩

/-- **A frame hole of the true valuation at full arity**, at an index spine
fitting its owner `o`'s telescope, is `o`'s true carrier there: its value
is `o`'s hole value at `o`'s true frame and carrier (`trueVal_frameVal`). -/
theorem dyn_ownerLeaf (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hxs : d.nP ≤ xs.length)
    {o : Nat} (ho : o ≠ 0) (hu : ns.getD (o - 1) default ∈ ns) {prog : List NestHole}
    {i : Nat} {hk : NestHole} (hi : prog.reverse[i]? = some hk)
    (hsuf : ∃ Y, prog.drop (prog.length - i) = Y ++ (ns.getD (o - 1) default).anc)
    (hk_mem : hk ∈ ConLeche.grpNews (ns.getD (o - 1) default).key.lvls
      (ns.getD (o - 1) default).key.ds (ctx.hiAt (ns.getD (o - 1) default).anc.length)
      (ns.getD (o - 1) default).grp) {is : List V} (hlive : nlLive mpC ctx d ns ψ ρ xs o)
    (hfit : SpineFit (nlFr mpC ctx d ns ψ ρ xs o)
      ((nlDb mpC d ns o).ids (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is) :
    nlComp mpC d ns o hk.key.cname < (nlDb mpC d ns o).N ∧
    is.foldl app (trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i)))
      = app ((nlDb mpC d ns o).carrier (nlψ envC ns ψ o) (nlFr mpC ctx d ns ψ ρ xs o)
          (nlComp mpC d ns o hk.key.cname))
        (tupW ((nlDb mpC d ns o).u (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is) := by
  have hxs' : ctx.nP ≤ xs.length := by rw [H.hnP]; exact hxs
  have hfrU := dyn_nlFr H ho hu ψ ρ xs
  unfold nlComp at hfit ⊢
  unfold nlLive at hlive
  rw [ite_eq_right ho] at hlive
  rw [show nlDb mpC d ns o = lfpSel mpC d.toLfp (ns.getD (o - 1) default).key.cname by
      unfold nlDb; rw [ite_eq_right ho],
    show nlψ envC ns ψ o = nodeψ envC ψ (ns.getD (o - 1) default) by
      unfold nlψ; rw [ite_eq_right ho]] at hfit hlive ⊢
  rw [hfrU] at hfit hlive ⊢
  generalize ns.getD (o - 1) default = u at hu hk_mem hfit hfrU hsuf hlive ⊢
  have hval := trueVal_frameVal H ψ ρ xs hxs' hu hlive.1 hi hsuf hk_mem
  obtain ⟨hD, hwid, hnN, hkN, -, -, -, -, -, -, -, -, -, -, -, -, -, hg⟩ := dyn_nodeBlock H hu
  simp only [ConLeche.grpNews, List.mem_map] at hk_mem
  obtain ⟨p, hp, rfl⟩ := hk_mem
  obtain ⟨mm', hmm', hpm⟩ := (hg.2.2 p hp).1
  simp only at hval hfit ⊢
  refine ⟨by rw [hpm, idxOf_member hnN hkN hmm', hwid]; exact hmm', ?_⟩
  rw [hval, LfpDatum.holeVal_app hfit]

/-- A listed node's position in the list. -/
theorem exists_pos {ns : List PosTree} {u : PosTree} (hu : u ∈ ns) :
    ∃ o, o ≠ 0 ∧ o ≤ ns.length ∧ ns.getD (o - 1) default = u := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hu
  refine ⟨i + 1, by omega, by omega, ?_⟩
  rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi,
    Option.getD_some]

/-- The owner at any fuel beyond the position. -/
theorem holeOwnerF_fuel {ns : List PosTree} {par : Nat → Nat} :
    ∀ (f f' b i : Nat), b < f → b < f' → holeOwnerF ns par f b i = holeOwnerF ns par f' b i
  | 0, _, b, _, hb, _ => absurd hb (Nat.not_lt_zero _)
  | _ + 1, 0, b, _, _, hb' => absurd hb' (Nat.not_lt_zero _)
  | f + 1, f' + 1, b, i, hb, hb' => by
    simp only [holeOwnerF]
    split
    · rename_i h
      exact holeOwnerF_fuel f f' (par b) i (by omega) (by omega)
    · rfl

/-- **The owner of a stack hole**, along the parent pointers: a listed
node, higher than the stack's node, whose group holds the hole, its group
and frames a suffix of the stack. -/
theorem dyn_holeOwner (H : DynCtx F mk mpC ctx d ns) {par : Nat → Nat} (hPP : ParentPtrs ns par) :
    ∀ (f b : Nat), b ≤ f → 0 < b → b ≤ ns.length → ∀ (i : Nat) (hk : NestHole),
      (ns.getD (b - 1) default).anc.reverse[i]? = some hk →
      0 < holeOwnerF ns par f b i ∧ holeOwnerF ns par f b i ≤ ns.length ∧
      hk ∈ ConLeche.grpNews (ns.getD (holeOwnerF ns par f b i - 1) default).key.lvls
        (ns.getD (holeOwnerF ns par f b i - 1) default).key.ds
        (ctx.hiAt (ns.getD (holeOwnerF ns par f b i - 1) default).anc.length)
        (ns.getD (holeOwnerF ns par f b i - 1) default).grp ∧
      (ns.getD (b - 1) default).height < (ns.getD (holeOwnerF ns par f b i - 1) default).height ∧
      (ns.getD (holeOwnerF ns par f b i - 1) default).anc.length ≤ i ∧
      ∃ X, (ns.getD (b - 1) default).anc = X ++ (ConLeche.grpNews
        (ns.getD (holeOwnerF ns par f b i - 1) default).key.lvls
        (ns.getD (holeOwnerF ns par f b i - 1) default).key.ds
        (ctx.hiAt (ns.getD (holeOwnerF ns par f b i - 1) default).anc.length)
        (ns.getD (holeOwnerF ns par f b i - 1) default).grp).reverse ++
        (ns.getD (holeOwnerF ns par f b i - 1) default).anc
  | 0, b, hb, hb0, _, _, _, _ => by omega
  | f + 1, b, hb, hb0, hbl, i, hk, hi => by
    have ht := getD_mem_of_lt (ns := ns) (b := b) hb0 hbl
    generalize htb : ns.getD (b - 1) default = t at ht hi ⊢
    -- the hole's node occurs at a frame: its parent
    obtain ⟨-, -, -, -, -, hanc⟩ := H.hok t ht
    have hne : t.anc ≠ [] := by
      intro h; rw [h] at hi; simp at hi
    have hao : t.anc = t.occ := by
      rcases hanc with ⟨hao, -⟩ | ⟨han, -⟩
      · exact hao
      · exact absurd han hne
    have hocc : t.occ ≠ [] := by rw [← hao]; exact hne
    obtain ⟨hq0, hqb, hkid⟩ := hPP.1 b hb0 hbl (by rw [htb]; exact hocc)
    rw [htb] at hkid
    have hp := getD_mem_of_lt (ns := ns) (b := par b) hq0 (by omega)
    generalize hpb : ns.getD (par b - 1) default = p at hp hkid
    have hkocc := (H.hok p hp).2.2.1 t hkid
    have hta : t.anc = (ConLeche.grpNews p.key.lvls p.key.ds (ctx.hiAt p.anc.length) p.grp).reverse
        ++ p.anc := by rw [hao, hkocc]
    have hlt := PosTree.height_kid hkid
    rw [hta, List.reverse_append, List.reverse_reverse] at hi
    simp only [holeOwnerF]
    rw [hpb]
    by_cases hin : i < p.anc.length
    · rw [ite_eq_left ⟨hin, hqb⟩]
      rw [List.getElem?_append_left (by simpa using hin)] at hi
      obtain ⟨h1, h2, h3, h4, h5, X, hX⟩ := dyn_holeOwner H hPP f (par b) (by omega) hq0 (by omega) i
        hk (by rw [hpb]; exact hi)
      rw [hpb] at h4 hX
      refine ⟨h1, h2, h3, Nat.lt_trans hlt h4, h5,
        (ConLeche.grpNews p.key.lvls p.key.ds (ctx.hiAt p.anc.length) p.grp).reverse ++ X, ?_⟩
      rw [hta, hX]
      simp only [List.append_assoc]
    · rw [ite_eq_right (fun h => hin h.1), hpb]
      rw [List.getElem?_append_right (by simpa using hin)] at hi
      exact ⟨hq0, by omega, List.mem_of_getElem? hi, hlt, by omega, [],
        by rw [hta, List.nil_append]⟩

/-- **`top`**: the TRUE frame of a live node is admissible once the
shallower live nodes' true elements satisfy `G` — node `0` by definition; a
derived node at the true valuation of its frames, whose member holes at the
block's parameters are node `0`'s true carrier and whose frame holes at
their keys are their (shallower) live owners' true carriers (`leaf`). -/
theorem dyn_top (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {par : Nat → Nat} (hPP : ParentPtrs ns par) :
    ∀ b, b < ns.length + 1 → nlLive mpC ctx d ns ψ ρ xs b → ∀ G : Nat → Nat → V → V → Prop,
      (∀ b' c t y, b' < ns.length + 1 → nlDp ns b' < nlDp ns b → c < (nlDb mpC d ns b').N →
        nlLive mpC ctx d ns ψ ρ xs b' →
        t ∈ˢ (nlDb mpC d ns b').idx (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c →
        y ∈ˢ app ((nlDb mpC d ns b').carrier (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c) t →
        G b' c t y) →
      nodeAdm mk mpC ctx d ns ψ ρ xs par b G (nlFr mpC ctx d ns ψ ρ xs b) := by
  intro b hb hlive G hG
  unfold nodeAdm
  by_cases hb0 : b = 0
  · rw [ite_eq_left hb0]; subst hb0; rfl
  rw [ite_eq_right hb0]
  have ht := getD_mem_of_lt (ns := ns) (b := b) (by omega) (by omega)
  refine ⟨hlive, _, ?_, dyn_nlFr H hb0 ht ψ ρ xs⟩
  have hdpb : nlDp ns b = nlDd ns - (ns.getD (b - 1) default).height := by
    unfold nlDp; rw [ite_eq_right hb0]
  have hdd := height_le_nlDd ht
  have hown := dyn_holeOwner H hPP (b + 1) b (by omega) (by omega) (by omega)
  unfold holeOwner
  generalize ns.getD (b - 1) default = t at ht hdpb hdd hown ⊢
  refine ⟨dyn_trueVal_sat H ψ ρ xs hparams hxs _ t ht (Nat.le_refl _), fun _ _ => rfl,
    fun t' ht' is his y hy => ⟨fun hfit => ?_, fun _ => hy⟩, fun i hk hi => ?_⟩
  · -- a member hole: node `0`'s true carrier
    rw [dyn_memberLeaf H ψ ρ xs hparams hxs t.anc ht' hfit] at hy
    have hkN := lfp_namesLen mpC H.hd0
    have htk : t' < d.toLfp.k := by rw [← hkN, ← H.hnames]; exact ht'
    have h0 : nlDp ns 0 = 0 := by unfold nlDp; rw [ite_eq_left rfl]
    refine hG 0 t' _ y (by omega) (by rw [h0, hdpb]; have := PosTree.height_pos t; omega)
      ?_ (by unfold nlLive; rw [ite_eq_left rfl]; trivial) ?_ ?_
    · show t' < d.toLfp.N
      exact Nat.lt_of_lt_of_le htk (mpC.lfpClause_of_mem H.hd0).kN
    · simp only [nlDb, nlψ, nlFr, ite_eq_left]
      rw [← H.hnP]
      exact tupW_mem hfit
    · simp only [nlDb, nlψ, nlFr, ite_eq_left]
      exact hy
  · -- a frame hole: its owner's true carrier
    obtain ⟨ho0, hol, hmem, hlt, hle, X, hX⟩ := hown i hk hi
    generalize hoe : holeOwnerF ns par (b + 1) b i = o at ho0 hol hmem hlt hle hX ⊢
    have ho : o ≠ 0 := by omega
    have hu' : ns.getD (o - 1) default ∈ ns := getD_mem_of_lt ho0 hol
    have hud := height_le_nlDd hu'
    have hil : i < t.anc.length := by
      have := (List.getElem?_eq_some_iff.mp hi).1; simpa using this
    have hsuf := stack_suffix hX hle (Nat.le_of_lt hil)
    refine ⟨ho0, hol, hmem, hsuf, fun dsa hdsa => dyn_ownerFrame H ψ ρ xs ho hu' hX hmem hdsa,
      fun is _ y hy => ⟨fun ⟨hl, hfit⟩ => ?_, fun _ => hy⟩⟩
    obtain ⟨hmo, heq⟩ := dyn_ownerLeaf H ψ ρ xs hxs ho hu' hi hsuf hmem hl hfit
    rw [heq] at hy
    refine hG _ _ _ y (by omega) ?_ hmo hl (tupW_mem hfit) hy
    rw [hdpb]
    unfold nlDp
    rw [ite_eq_right ho]
    omega

/-- **An admissible valuation is below the true one** along a hole
relation of the node's frames, once `G`'s elements are true: at a member
hole where `G 0` holds, node `0`'s true carrier is the member constant
applied (`dyn_memberLeaf`); at a frame hole where `G o` holds, `o`'s true
carrier is its constant applied at the key (`dyn_ownerLeaf`); elsewhere
the value is below the true one by admissibility. -/
theorem dyn_holeRel (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    (own : Nat → Nat) {G : Nat → Nat → V → V → Prop}
    (hG : ∀ b' c t y, G b' c t y →
      y ∈ˢ app ((lfpSClause (nlDb mpC d ns b') (nlψ envC ns ψ b')
        (pinIdx (nlDb mpC d ns b') (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b')
          (nlLive mpC ctx d ns ψ ρ xs b'))
        (nlFrLen d ns xs b') (nlTail mpC ctx d ns ψ ρ xs b')).carrier
          (nlFrFin mpC ctx d ns ψ ρ xs b') c) t)
    {t : PosTree} (ht : t ∈ ns) :
    HoleRel mk.base2 ψ ctx t.anc (ctx.hiAt t.anc.length)
      (stackCtx mk.base2 ψ ctx t.anc (d.holeCtx ψ).reverse)
      (fun σ₁ σ₂ => AdmVal mk mpC ctx d ns ψ ρ xs own G t.anc σ₁ ∧
        σ₂ = trueVal mpC ctx ψ ρ xs t.anc) where
  dom := by
    rintro σ₁ σ₂ ⟨hA, rfl⟩
    exact ⟨hA.sat, dyn_trueVal_sat H ψ ρ xs hparams hxs _ t ht (Nat.le_refl _)⟩
  agree := by
    rintro σ₁ σ₂ ⟨hA, rfl⟩
    exact hA.agree
  member := by
    intro t' ht'
    rintro σ₁ σ₂ ⟨hA, rfl⟩ is his y hy
    obtain ⟨g1, g2⟩ := hA.member t' ht' is his y hy
    by_cases hc : SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t' ψ) is
    · have hy' := hG _ _ _ _ (g1 hc)
      rw [pinIdx_of (show nlLive mpC ctx d ns ψ ρ xs 0 by unfold nlLive; rw [ite_eq_left rfl]; trivial),
        lfpSClause_carrier (prepend_nlFrFin_nlTail mpC ctx d ns ψ ρ xs 0 ▸ rfl),
        prepend_nlFrFin_nlTail] at hy'
      simp only [nlDb, nlψ, nlFr, ite_eq_left] at hy'
      rw [dyn_memberLeaf H ψ ρ xs hparams hxs t.anc ht' hc]
      exact hy'
    · exact g2 hc
  frame := by
    rintro i hk hki ni har σ₁ σ₂ ⟨hA, rfl⟩ is his y hy
    obtain ⟨ho0, hol, hmem, hsuf, -, hrest2⟩ := hA.frame i hk hki
    generalize own i = o at ho0 hol hmem hsuf hrest2
    obtain ⟨g1, g2⟩ := hrest2 is (by omega) y hy
    by_cases hfit : nlLive mpC ctx d ns ψ ρ xs o ∧ SpineFit (nlFr mpC ctx d ns ψ ρ xs o)
        ((nlDb mpC d ns o).ids (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is
    · rw [(dyn_ownerLeaf H ψ ρ xs hxs (by omega)
        (getD_mem_of_lt (ns := ns) (b := o) ho0 hol) hki hsuf hmem hfit.1 hfit.2).2]
      have hy' := hG _ _ _ _ (g1 hfit)
      rwa [pinIdx_of hfit.1,
        lfpSClause_carrier (prepend_nlFrFin_nlTail mpC ctx d ns ψ ρ xs o ▸ rfl),
        prepend_nlFrFin_nlTail] at hy'
    · exact g2 hfit
  dsScoped := (H.hok t ht).2.2.2.1

/-- **`trans`**: node `0` by its clause's `fitsMono` (its only admissible
frame is its true one); a derived node by the frame's monotonicity
(`FrameMono`, `posD_mono` at the node's own derivation) along the hole
relation from the admissible valuation to the true one (`dyn_holeRel`),
then `trans_of_frameConcl`. -/
theorem dyn_trans (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    (par : Nat → Nat) :
    ∀ b, b < ns.length + 1 → ∀ G : Nat → Nat → V → V → Prop,
      (∀ b' c t y, G b' c t y →
        y ∈ˢ app ((lfpSClause (nlDb mpC d ns b') (nlψ envC ns ψ b')
          (pinIdx (nlDb mpC d ns b') (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b')
            (nlLive mpC ctx d ns ψ ρ xs b'))
          (nlFrLen d ns xs b') (nlTail mpC ctx d ns ψ ρ xs b')).carrier
          (nlFrFin mpC ctx d ns ψ ρ xs b') c) t) →
      ∀ ρ', nodeAdm mk mpC ctx d ns ψ ρ xs par b G ρ' → ∀ Y,
      InTupleSpace ((nlDb mpC d ns b).w (nlψ envC ns ψ b)) (nlDb mpC d ns b).N
        ((nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) Y →
      TupleLe (nlDb mpC d ns b).N
        ((nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) Y
        ((nlDb mpC d ns b).carrier (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) →
      ∀ t c j fs, c < (nlDb mpC d ns b).N →
        (nlDb mpC d ns b).HFits (nlψ envC ns ψ b) ρ' Y t c j fs →
        (nlDb mpC d ns b).HFits (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)
          ((nlDb mpC d ns b).carrier (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) t c j fs := by
  intro b hb G hG ρ' hadm Y hY hle t c j fs hc hf
  have hsat := (dyn_hAdm H ψ ρ xs hparams hxs par b hb G ρ' hadm).2
  unfold nodeAdm at hadm
  by_cases hb0 : b = 0
  · rw [ite_eq_left hb0] at hadm
    subst hb0
    subst hadm
    have hcl : LfpClause mpC.base2.acval (nlDb mpC d ns 0) := by
      simp only [nlDb, ite_eq_left]; exact mpC.lfpClause_of_mem H.hd0
    exact lfp_trans_self hcl hsat.1 hY hle hc hf
  rw [ite_eq_right hb0] at hadm
  obtain ⟨hlive, σ, hσ, rfl⟩ := hadm
  have ht := getD_mem_of_lt (ns := ns) (b := b) (by omega) (by omega)
  have hsat' := hsat
  unfold nlLive at hlive
  rw [ite_eq_right hb0] at hlive
  rw [dyn_nlFr H hb0 ht ψ ρ xs] at hY hle hsat' hlive ⊢
  have e1 : nlDb mpC d ns b = lfpSel mpC d.toLfp (ns.getD (b - 1) default).key.cname := by
    unfold nlDb; rw [ite_eq_right hb0]
  have e2 : nlψ envC ns ψ b = nodeψ envC ψ (ns.getD (b - 1) default) := by
    unfold nlψ; rw [ite_eq_right hb0]
  rw [e1, e2] at hY hle hf hsat' hlive ⊢
  rw [e1] at hc
  generalize ns.getD (b - 1) default = u at ht hσ hY hle hc hf hsat' hlive ⊢
  obtain ⟨hD, hwid, hnN, hkN, hall, mm, hmm, hmmH, cv, caps, hfc, hlps, hlpsOf, hndl, hul, hlenP,
    hnL, hg⟩ := dyn_nodeBlock H ht
  generalize lfpSel mpC d.toLfp u.key.cname = D at *
  have hψ : nodeψ envC ψ u = Level.substFn ψ cv.levelParams u.key.lvls := by
    unfold nodeψ; rw [hlpsOf]
  rw [hψ] at hY hle hf hsat' hlive ⊢
  -- the frame's monotonicity at the node's own derivation
  have hR := dyn_holeRel H ψ ρ xs hparams hxs (holeOwner ns par b) hG ht
  have hmono : FrameMono mk ψ ctx u.anc u.key.lvls u.key.ds u.grp :=
    posD_mono mk (Rules.RulesInputs.ofSem mk ψ) (H.hok u ht).1
  have hdsa := dyn_dsaI H ht ψ
  have hws := posNodeOk_dsAnc (H.hok u ht)
  obtain ⟨-, hC, hL⟩ := H.hsem u ht ψ
  have hΔ := stackCtx_length_hi (m := mk.base2) (φ := ψ) (H.hΔ0 ψ) u.anc
  have hin := Rules.RulesInputs.ofSem mk ψ
  have hsT := dyn_trueVal_sat H ψ ρ xs hparams hxs _ u ht (Nat.le_refl _)
  -- the admissible frame fits where the true one does
  have hkσ : KeyFit D (Level.substFn ψ cv.levelParams u.key.lvls) (nodeDsaI mk ctx ψ u)
      (ctx.hiAt u.anc.length) σ :=
    keyFit_agree mk hD hnN hkN H.hcov.find hlps hws hdsa (hlenP _) hg hin hΔ hC hL
      (fun i hi => (hσ.agree i hi).symm) hsT hσ.sat hlive
  obtain ⟨-, -, -, hconcl⟩ := hmono H.hcov hD hmm hmmH hlps hul hws hdsa (hlenP _) hnL hR hΔ hC hL
  refine trans_of_frameConcl (mk.lfpClause_of_mem hD) hwid hall
    (hconcl σ (trueVal mpC ctx ψ ρ xs u.anc) ⟨hσ, rfl⟩ hkσ hlive) hsat'.1 ?_ hY hle hc hf
  intro c' hc'
  rw [hwid] at hc'
  exact grp_idx_eq mk hD hnN hkN H.hcov.find hlps hws hdsa (hlenP _) hg hin hΔ hC hL (hall c' hc')
    hσ.agree hσ.sat hsT hkσ hlive

/-! ## First-order set-parameterized wrapper for `TgtNodeDyn` -/

/-- **Admissible finite frames over unbounded set hypotheses `G : V`**:
element hypotheses encoded via `nenc b' c t y ∈ˢ G`, evaluated on
`prepend ρ' (nlTail ... b)`. -/
@[expose] def nodeAdmSet (mk : EnvModelM V envI) (mpC : EnvModelM V envC) (ctx : NestCtx)
    (d : BlockData V) (ns : List PosTree) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (par : Nat → Nat) (b : Nat) (G : V) (ρ' : Fin (nlFrLen d ns xs b) → V) : Prop :=
  nodeAdm mk mpC ctx d ns ψ ρ xs par b
    (fun b' c t y => nenc b' c t y ∈ˢ G)
    (prepend ρ' (nlTail mpC ctx d ns ψ ρ xs b))

omit [SetTheory V] in
private theorem prepend_eq_prepend_iff {len : Nat} {as bs : Fin len → V} {t₁ t₂ : Nat → V} :
    prepend as t₁ = prepend bs t₂ ↔
      (∀ i : Fin len, as i = bs i) ∧ (∀ q : Nat, t₁ q = t₂ q) := by
  constructor
  · intro h
    refine ⟨fun i => ?_, fun q => ?_⟩
    · have hi := congrFun h i.val
      simpa only [prepend, dite_eq_left i.isLt] using hi
    · have hq := congrFun h (q + len)
      simpa only [prepend, dite_eq_right (by omega : ¬ q + len < len), Nat.add_sub_cancel] using hq
  · rintro ⟨h1, h2⟩
    funext i
    by_cases hi : i < len
    · simp only [prepend, dite_eq_left hi]; exact h1 ⟨i, hi⟩
    · simp only [prepend, dite_eq_right hi]; exact h2 (i - len)

private theorem defFun_foldl_app_ofFn_do {k : Nat}
    (X : (Fin k → V) → V) (hX : DefFun k X) :
    ∀ {r : Nat} (As : Fin r → (Fin k → V) → V), (∀ i, DefFun k (As i)) →
      DefFun k fun env => (List.ofFn fun i => As i env).foldl app (X env)
  | 0, _, _ => hX.congr fun env => by simp
  | r + 1, As, hAs => by
    have hX' : DefFun k fun env => app (X env) (As 0 env) := DefFun.app_apply hX (hAs 0)
    have hrec := defFun_foldl_app_ofFn_do (fun env => app (X env) (As 0 env)) hX'
      (fun i : Fin r => As i.succ) (fun i => hAs i.succ)
    exact hrec.congr fun env => by rw [List.ofFn_succ, List.foldl_cons]

private theorem defFun_mkTower_ofFn_do {k : Nat} :
    ∀ {r : Nat} (As : Fin r → (Fin k → V) → V), (∀ i, DefFun k (As i)) →
      DefFun k fun env => Tower.mkTower (List.ofFn fun i => As i env)
  | 0, _, _ => DefFun.empty.congr fun _ => by simp [Tower.mkTower]
  | r + 1, As, hAs => by
    have hrest := defFun_mkTower_ofFn_do (fun i : Fin r => As i.succ) (fun i => hAs i.succ)
    exact (DefFun.spair_apply (hAs 0) hrest).congr fun env => by
      simp [List.ofFn_succ, Tower.mkTower]

private theorem defFun_tupW_ofFn_do (u : Nat) {k r : Nat}
    (As : Fin r → (Fin k → V) → V) (hAs : ∀ i, DefFun k (As i)) :
    DefFun k fun env => tupW u (List.ofFn fun i => As i env) := by
  by_cases hu : u = 0
  · subst hu; exact DefFun.pt.congr fun _ => (tupW_zero _).symm
  · exact (defFun_mkTower_ofFn_do As hAs).congr fun _ => (tupW_pos hu _).symm

private theorem defRel_spineFit_prepend_ofFn_do {k : Nat} (tail : Nat → V) :
    ∀ (Fs : List Term) {d r : Nat}
      (Xs : Fin d → (Fin k → V) → V), (∀ i, DefFun k (Xs i)) →
      ∀ (As : Fin r → (Fin k → V) → V), (∀ i, DefFun k (As i)) →
      DefRel k fun env =>
        SpineFit (prepend (fun i => Xs i env) tail) Fs (List.ofFn fun i => As i env)
  | [], _, 0, _, _, _, _ => DefRel.true
  | [], _, _ + 1, _, _, _, _ => DefRel.false.congr fun _ => by simp [SpineFit]
  | _ :: _, _, 0, _, _, _, _ => DefRel.false.congr fun _ => by simp [SpineFit]
  | F :: Fs, d, r + 1, Xs, hXs, As, hAs => by
    let Xs' : Fin (d + 1) → (Fin k → V) → V := fun i env =>
      if h0 : i.val = 0 then As 0 env else Xs ⟨i.val - 1, by omega⟩ env
    have hXs' : ∀ i, DefFun k (Xs' i) := fun ⟨i, hi⟩ => by
      dsimp only [Xs']; split
      · exact hAs 0
      · exact hXs _
    have hrest := defRel_spineFit_prepend_ofFn_do tail Fs Xs' hXs'
      (fun i : Fin r => As i.succ) (fun i => hAs i.succ)
    refine (DefRel.and
      (DefRel.mem_apply (hAs 0) ((interp_defFun_prepend tail d F).comp hXs))
      hrest).congr fun env => ?_
    rw [List.ofFn_succ]
    refine and_congr_right fun _ => ?_
    have hp : prepend (fun i => Xs' i env) tail = cons (As 0 env) (prepend (fun i => Xs i env) tail) := by
      funext j
      cases j with
      | zero => simp [prepend, Xs', cons]
      | succ j =>
        by_cases hj : j < d
        · simp [prepend, Xs', hj, show j + 1 < d + 1 by omega, cons]
        · have hj1 : ¬ (j + 1 < d + 1) := by omega
          simp only [prepend, hj, hj1, ↓reduceDIte, cons]
          congr 1; omega
    rw [hp]

private theorem defRel_spineFit_const_ofFn_do {k : Nat} (σ : Nat → V)
    (Fs : List Term) {r : Nat} (As : Fin r → (Fin k → V) → V) (hAs : ∀ i, DefFun k (As i)) :
    DefRel k fun env => SpineFit σ Fs (List.ofFn fun i => As i env) := by
  refine (defRel_spineFit_prepend_ofFn_do σ Fs
    (Fin.elim0 : Fin 0 → (Fin k → V) → V) (fun i => Fin.elim0 i) As hAs).congr fun env => ?_
  have hp : prepend (Fin.elim0 : Fin 0 → V) σ = σ := prepend_zero σ
  change SpineFit (prepend Fin.elim0 σ) Fs _ ↔ _
  rw [hp]

theorem dyn_nodeAdmSet_def (ψ : Name → Nat) (ρ : Nat → V) (xs : List V) (par : Nat → Nat) :
    ∀ b, DefRel (nlFrLen d ns xs b + 1) fun v =>
      nodeAdmSet mk mpC ctx d ns ψ ρ xs par b (v 0) (ftail v) := by
  intro b
  by_cases hb0 : b = 0
  · subst hb0
    have h0 : DefRel (V := V) (nlFrLen d ns xs 0 + 1) fun v =>
        ∀ i : Fin (nlFrLen d ns xs 0), ftail v i = nlFrFin mpC ctx d ns ψ ρ xs 0 i :=
      DefRel.finForall (V := V) fun i => DefRel.eq_apply
        (DefFun.proj (V := V) ⟨i.val + 1, by omega⟩)
        (DefFun.const (V := V) (nlFrFin mpC ctx d ns ψ ρ xs 0 i))
    refine h0.congr fun v => ?_
    unfold nodeAdmSet nodeAdm
    rw [ite_eq_left rfl, ← prepend_nlFrFin_nlTail mpC ctx d ns ψ ρ xs 0, prepend_eq_prepend_iff]
    exact ⟨fun h => ⟨h, fun _ => rfl⟩, fun ⟨h, _⟩ => h⟩
  · let t := ns.getD (b - 1) default
    let hi := ctx.hiAt t.anc.length
    let tv := trueVal mpC ctx ψ ρ xs t.anc
    let tailT : Nat → V := fun q => tv (q + hi)
    let M := hi + (nlFrLen d ns xs b + 1)
    let σ_fn : (Fin M → V) → Nat → V := fun v => prepend (ftake v) tailT
    let Δ := stackCtx mk.base2 ψ ctx t.anc (d.holeCtx ψ).reverse
    let SatIdx (idx : Nat) (v : Fin M → V) : Prop :=
      ∀ Aa, Δ[idx]? = some Aa → σ_fn v idx ∈ˢ interp V (fun j => σ_fn v (j + idx + 1)) Aa
    have hSatIdx : ∀ idx, DefRel M (SatIdx idx) := fun idx => by
      cases hopt : Δ[idx]? with
      | none => exact DefRel.true.congr fun _ => ⟨(fun _ _ h => by rw [hopt] at h; cases h), fun _ => trivial⟩
      | some Aa =>
        have hLHS : DefFun M fun v => σ_fn v idx := by
          by_cases hlt : idx < hi
          · exact (DefFun.proj (V := V) ⟨idx, by omega⟩).congr fun v => by
              simp only [σ_fn, prepend, dite_eq_left hlt]; rfl
          · exact (DefFun.const (V := V) (tailT (idx - hi))).congr fun v => by
              simp only [σ_fn, prepend, dite_eq_right hlt]
        let rem := if idx + 1 < hi then hi - (idx + 1) else 0
        let off := if hi ≤ idx + 1 then idx + 1 - hi else 0
        let tail_i : Nat → V := fun q => tailT (q + off)
        let Xs_i : Fin rem → (Fin M → V) → V := fun j v =>
          v ⟨j.val + (idx + 1), by
            have hj := j.isLt; dsimp [rem] at hj
            by_cases h1 : idx + 1 < hi
            · simp [h1] at hj; omega
            · simp [h1] at hj⟩
        have hXs_i : ∀ j, DefFun M (Xs_i j) := fun j =>
          DefFun.proj ⟨j.val + (idx + 1), by
            have hj := j.isLt; dsimp [rem] at hj
            by_cases h1 : idx + 1 < hi
            · simp [h1] at hj; omega
            · simp [h1] at hj⟩
        have hRHS_eq : ∀ v, (fun j => σ_fn v (j + idx + 1)) = prepend (fun j => Xs_i j v) tail_i := by
          intro v; funext j
          by_cases hj : j < rem
          · have hlt : j + idx + 1 < hi := by
              dsimp [rem] at hj
              by_cases h1 : idx + 1 < hi
              · simp [h1] at hj; omega
              · simp [h1] at hj
            simp only [σ_fn, prepend, dite_eq_left hlt, dite_eq_left hj, Xs_i]
            exact congrArg (v ·) (Fin.ext (by dsimp; omega))
          · have hge : ¬ j + idx + 1 < hi := by
              dsimp [rem] at hj
              by_cases h1 : idx + 1 < hi
              · simp [h1] at hj; omega
              · simp [h1] at hj; omega
            simp only [σ_fn, prepend, dite_eq_right hge, dite_eq_right hj, tail_i]
            congr 1
            dsimp [rem, off] at hj ⊢
            by_cases h1 : idx + 1 < hi
            · have h2 : ¬ hi ≤ idx + 1 := by omega
              simp only [h1, ↓reduceIte] at hj ⊢; simp only [h2, ↓reduceIte]; omega
            · have h2 : hi ≤ idx + 1 := by omega
              simp only [h1, ↓reduceIte] at hj ⊢; simp only [h2, ↓reduceIte]; omega
        have hRHS : DefFun M fun v => interp V (fun j => σ_fn v (j + idx + 1)) Aa :=
          ((interp_defFun_prepend tail_i rem Aa).comp hXs_i).congr fun v => by rw [hRHS_eq v]; rfl
        refine (DefRel.mem_apply hLHS hRHS).congr fun v => ?_
        exact ⟨fun hm _ he => by rw [hopt] at he; cases he; exact hm, fun h => h Aa hopt⟩
    have hSat : DefRel M fun v => Sat V Δ (σ_fn v) :=
      (DefRel.finForall_lt (n := Δ.length) fun idx _ => hSatIdx idx).congr fun v =>
        ⟨fun h idx Aa hiA => h idx (List.getElem?_eq_some_iff.mp hiA).1 Aa hiA,
         fun h idx _ Aa hiA => h idx Aa hiA⟩
    let AgrIdx (j : Nat) (v : Fin M → V) : Prop :=
      ¬ holeP hi ctx.nP hi j → σ_fn v j = tv j
    have hAgrIdx : ∀ j, j < hi → DefRel M (AgrIdx j) := fun j hj => by
      by_cases hp : holeP hi ctx.nP hi j
      · exact DefRel.true.congr fun _ => ⟨(fun _ hnp => absurd hp hnp), fun _ => trivial⟩
      · exact (DefRel.eq_apply (DefFun.proj ⟨j, Nat.lt_of_lt_of_le hj (Nat.le_add_right _ _)⟩)
          (DefFun.const (tv j))).congr fun v => by
          simp only [AgrIdx, σ_fn, prepend, dite_eq_left hj, ftake]
          exact ⟨fun h _ => h, fun h => h hp⟩
    have hAgree : DefRel M fun v => AgreeOff (holeP hi ctx.nP hi) (σ_fn v) tv :=
      (DefRel.finForall_lt hAgrIdx).congr fun v =>
        ⟨fun h j hnp => by
          by_cases hj : j < hi
          · exact h j hj hnp
          · simp only [σ_fn, prepend, dite_eq_right hj, tailT, tv, Nat.sub_add_cancel (Nat.le_of_not_lt hj)],
         fun h j _ hnp => h j hnp⟩
    let G_fn : (Fin M → V) → V := fun v => fdrop v 0
    have hG_fn : DefFun M G_fn := DefFun.fdrop_proj 0
    have hMember : DefRel M fun v => ∀ t', t' < ctx.names.length →
        ∀ is : List V, is.length = ctx.nIdxs.getD t' 0 →
        ∀ y, y ∈ˢ is.foldl app (σ_fn v (hi - 1 - (ctx.nP + t'))) →
          (SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t' ψ) is →
            nenc 0 t' (tupW (d.toLfp.u t' ψ) is) y ∈ˢ G_fn v) ∧
          (¬ SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t' ψ) is →
            y ∈ˢ is.foldl app (tv (hi - 1 - (ctx.nP + t')))) := by
      refine DefRel.finForall_lt fun t' ht' => ?_
      let nI := ctx.nIdxs.getD t' 0
      let M₁ := nI + M
      let M₂ := M₁ + 1
      let Y_fn : (Fin M₂ → V) → V := fun w => w 0
      have hY_fn : DefFun M₂ Y_fn := DefFun.proj 0
      let is_fn : Fin nI → (Fin M₂ → V) → V := fun i w => w ⟨i.val + 1, by omega⟩
      have his_fn : ∀ i, DefFun M₂ (is_fn i) := fun i => DefFun.proj ⟨i.val + 1, by omega⟩
      let idxM := hi - 1 - (ctx.nP + t')
      let slot_fn : (Fin M₂ → V) → V := fun w => σ_fn (fdrop (ftail w)) idxM
      have hslot_fn : DefFun M₂ slot_fn := by
        by_cases hlt : idxM < hi
        · exact (DefFun.proj (V := V) ⟨1 + nI + idxM, by omega⟩).congr fun w => by
            simp only [slot_fn, σ_fn, prepend, dite_eq_left hlt, fdrop, ftail, ftake]
            congr 1; apply Fin.ext; dsimp; omega
        · exact (DefFun.const (V := V) (tailT (idxM - hi))).congr fun w => by
            simp only [slot_fn, σ_fn, prepend, dite_eq_right hlt]
      have hMemFold := DefRel.mem_apply hY_fn (defFun_foldl_app_ofFn_do slot_fn hslot_fn is_fn his_fn)
      have hFitRel := defRel_spineFit_const_ofFn_do (consList (xs.take ctx.nP) ρ)
        (d.toLfp.ids t' ψ) is_fn his_fn
      have hGMem := DefRel.mem_apply
        (DefFun.nenc_apply 0 t' (defFun_tupW_ofFn_do (d.toLfp.u t' ψ) is_fn his_fn) hY_fn)
        ((hG_fn.fdrop_apply (k := nI)).weaken)
      have hTrueMem := DefRel.mem_apply hY_fn
        (defFun_foldl_app_ofFn_do (fun _ => tv idxM) (DefFun.const (tv idxM)) is_fn his_fn)
      have hBody := hMemFold.imp ((hFitRel.imp hGMem).and (hFitRel.not.imp hTrueMem))
      have hForAll := DefRel.forall_fin (DefRel.forall_ hBody)
      refine hForAll.congr fun v => ?_
      have hSimp : ∀ (isVec : Fin nI → V) (y : V),
          (Y_fn (fcons y (fappend isVec v)) = y) ∧
          ((fun i => is_fn i (fcons y (fappend isVec v))) = isVec) ∧
          (fdrop (ftail (fcons y (fappend isVec v))) = v) := by
        intro isVec y
        have hft : ftail (fcons y (fappend isVec v)) = fappend isVec v := rfl
        have hfd : fdrop (fappend isVec v) = v := by
          funext i; simp only [fdrop, fappend, dite_eq_right (by omega : ¬ nI + i.val < nI)]
          congr 1; apply Fin.ext; dsimp; omega
        have his : (fun i => is_fn i (fcons y (fappend isVec v))) = isVec := by
          funext i
          simp only [is_fn, fcons, fappend, dite_eq_left i.isLt]
        exact ⟨rfl, his, hft ▸ hfd⟩
      constructor
      · intro h is hlen y hy
        have his_eq : is = List.ofFn fun i : Fin nI => is[i.val]'(hlen ▸ i.isLt) := by
          apply List.ext_getElem (by simp [hlen, nI, List.getD_eq_getElem?_getD]); intro j hj1 hj2; simp
        have hs := hSimp (fun i => is[i.val]'(hlen ▸ i.isLt)) y
        have hres := h (fun i => is[i.val]'(hlen ▸ i.isLt)) y
        dsimp only [slot_fn] at hres
        rw [hs.1, hs.2.1, hs.2.2, ← his_eq] at hres
        exact hres hy
      · intro h isVec y hy
        have hs := hSimp isVec y
        have hres := h (List.ofFn isVec) (by simp [nI, List.getD_eq_getElem?_getD]) y
        dsimp only [slot_fn] at hy ⊢
        rw [hs.1, hs.2.1, hs.2.2] at hy ⊢
        exact hres hy
    let FrameIdx (i : Nat) (v : Fin M → V) : Prop :=
      ∀ hk : NestHole, t.anc.reverse[i]? = some hk →
        0 < holeOwner ns par b i ∧ holeOwner ns par b i ≤ ns.length ∧
          hk ∈ ConLeche.grpNews (ns.getD (holeOwner ns par b i - 1) default).key.lvls
            (ns.getD (holeOwner ns par b i - 1) default).key.ds
            (ctx.hiAt (ns.getD (holeOwner ns par b i - 1) default).anc.length)
            (ns.getD (holeOwner ns par b i - 1) default).grp ∧
          (∃ Y, t.anc.drop (t.anc.length - i) =
            Y ++ (ns.getD (holeOwner ns par b i - 1) default).anc) ∧
          (∀ dsa', DenoteSpine mk.base2.acval envI ψ hi hk.key.ds dsa' →
            keyFrame dsa' hi tv = nlFr mpC ctx d ns ψ ρ xs (holeOwner ns par b i)) ∧
          ∀ is : List V, is.length = hk.nIdx →
          ∀ y, y ∈ˢ is.foldl app (σ_fn v (hi - 1 - (ctx.hiAt 0 + i))) →
            (nlLive mpC ctx d ns ψ ρ xs (holeOwner ns par b i) ∧
              SpineFit (nlFr mpC ctx d ns ψ ρ xs (holeOwner ns par b i))
                ((nlDb mpC d ns (holeOwner ns par b i)).ids
                  (nlComp mpC d ns (holeOwner ns par b i) hk.key.cname)
                  (nlψ envC ns ψ (holeOwner ns par b i))) is →
              nenc (holeOwner ns par b i) (nlComp mpC d ns (holeOwner ns par b i) hk.key.cname)
                (tupW ((nlDb mpC d ns (holeOwner ns par b i)).u
                  (nlComp mpC d ns (holeOwner ns par b i) hk.key.cname)
                  (nlψ envC ns ψ (holeOwner ns par b i))) is) y ∈ˢ G_fn v) ∧
            (¬ (nlLive mpC ctx d ns ψ ρ xs (holeOwner ns par b i) ∧
                SpineFit (nlFr mpC ctx d ns ψ ρ xs (holeOwner ns par b i))
                  ((nlDb mpC d ns (holeOwner ns par b i)).ids
                    (nlComp mpC d ns (holeOwner ns par b i) hk.key.cname)
                    (nlψ envC ns ψ (holeOwner ns par b i))) is) →
              y ∈ˢ is.foldl app (tv (hi - 1 - (ctx.hiAt 0 + i))))
    have hFrameIdx : ∀ i, DefRel M (FrameIdx i) := fun i => by
      cases hopt : t.anc.reverse[i]? with
      | none => exact DefRel.true.congr fun _ => ⟨(fun _ _ h => by rw [hopt] at h; cases h), fun _ => trivial⟩
      | some hk =>
        let ownI := holeOwner ns par b i
        let compI := nlComp mpC d ns ownI hk.key.cname
        let cSide : Prop := 0 < ownI ∧ ownI ≤ ns.length ∧
          hk ∈ ConLeche.grpNews (ns.getD (ownI - 1) default).key.lvls
            (ns.getD (ownI - 1) default).key.ds
            (ctx.hiAt (ns.getD (ownI - 1) default).anc.length)
            (ns.getD (ownI - 1) default).grp ∧
          (∃ Y, t.anc.drop (t.anc.length - i) = Y ++ (ns.getD (ownI - 1) default).anc)
        have hDsaRel : DefRel M fun _ => ∀ dsa', DenoteSpine mk.base2.acval envI ψ hi hk.key.ds dsa' →
            keyFrame dsa' hi tv = nlFr mpC ctx d ns ψ ρ xs ownI :=
          DefRel.constProp (V := V) (k := M) _
        let M₁ := hk.nIdx + M
        let M₂ := M₁ + 1
        let Y_fn : (Fin M₂ → V) → V := fun w => w 0
        have hY_fn : DefFun M₂ Y_fn := DefFun.proj 0
        let is_fn : Fin hk.nIdx → (Fin M₂ → V) → V := fun q w => w ⟨q.val + 1, by omega⟩
        have his_fn : ∀ q, DefFun M₂ (is_fn q) := fun q => DefFun.proj ⟨q.val + 1, by omega⟩
        let idxF := hi - 1 - (ctx.hiAt 0 + i)
        let slot_fn : (Fin M₂ → V) → V := fun w => σ_fn (fdrop (ftail w)) idxF
        have hslot_fn : DefFun M₂ slot_fn := by
          by_cases hlt : idxF < hi
          · exact (DefFun.proj (V := V) ⟨1 + hk.nIdx + idxF, by omega⟩).congr fun w => by
              simp only [slot_fn, σ_fn, prepend, dite_eq_left hlt, fdrop, ftail, ftake]
              congr 1; apply Fin.ext; dsimp; omega
          · exact (DefFun.const (V := V) (tailT (idxF - hi))).congr fun w => by
              simp only [slot_fn, σ_fn, prepend, dite_eq_right hlt]
        have hMemFold := DefRel.mem_apply hY_fn (defFun_foldl_app_ofFn_do slot_fn hslot_fn is_fn his_fn)
        have hFitRel := DefRel.and
          (DefRel.constProp (nlLive mpC ctx d ns ψ ρ xs ownI))
          (defRel_spineFit_const_ofFn_do (nlFr mpC ctx d ns ψ ρ xs ownI)
            ((nlDb mpC d ns ownI).ids compI (nlψ envC ns ψ ownI)) is_fn his_fn)
        have hGMem := DefRel.mem_apply
          (DefFun.nenc_apply ownI compI
            (defFun_tupW_ofFn_do ((nlDb mpC d ns ownI).u compI (nlψ envC ns ψ ownI)) is_fn his_fn)
            hY_fn)
          ((hG_fn.fdrop_apply (k := hk.nIdx)).weaken)
        have hTrueMem := DefRel.mem_apply hY_fn
          (defFun_foldl_app_ofFn_do (fun _ => tv idxF) (DefFun.const (tv idxF)) is_fn his_fn)
        have hBody := hMemFold.imp ((hFitRel.imp hGMem).and (hFitRel.not.imp hTrueMem))
        have hForAll := DefRel.forall_fin (DefRel.forall_ hBody)
        have hForIs : DefRel M fun v => ∀ is : List V, is.length = hk.nIdx →
            ∀ y, y ∈ˢ is.foldl app (σ_fn v idxF) →
              (nlLive mpC ctx d ns ψ ρ xs ownI ∧
                SpineFit (nlFr mpC ctx d ns ψ ρ xs ownI)
                  ((nlDb mpC d ns ownI).ids compI (nlψ envC ns ψ ownI)) is →
                nenc ownI compI (tupW ((nlDb mpC d ns ownI).u compI (nlψ envC ns ψ ownI)) is) y ∈ˢ
                  G_fn v) ∧
              (¬ (nlLive mpC ctx d ns ψ ρ xs ownI ∧
                SpineFit (nlFr mpC ctx d ns ψ ρ xs ownI)
                  ((nlDb mpC d ns ownI).ids compI (nlψ envC ns ψ ownI)) is) →
                y ∈ˢ is.foldl app (tv idxF)) := by
          refine hForAll.congr fun v => ?_
          have hSimp : ∀ (isVec : Fin hk.nIdx → V) (y : V),
              (Y_fn (fcons y (fappend isVec v)) = y) ∧
              ((fun q => is_fn q (fcons y (fappend isVec v))) = isVec) ∧
              (fdrop (ftail (fcons y (fappend isVec v))) = v) := by
            intro isVec y
            have hft : ftail (fcons y (fappend isVec v)) = fappend isVec v := rfl
            have hfd : fdrop (fappend isVec v) = v := by
              funext q; simp only [fdrop, fappend, dite_eq_right (by omega : ¬ hk.nIdx + q.val < hk.nIdx)]
              congr 1; apply Fin.ext; dsimp; omega
            have his : (fun q => is_fn q (fcons y (fappend isVec v))) = isVec := by
              funext q
              simp only [is_fn, fcons, fappend, dite_eq_left q.isLt]
            exact ⟨rfl, his, hft ▸ hfd⟩
          constructor
          · intro h is hlen y hy
            have his_eq : is = List.ofFn fun q : Fin hk.nIdx => is[q.val]'(Nat.lt_of_lt_of_eq q.isLt hlen.symm) := by
              apply List.ext_getElem (by simp [hlen]); intro q hq1 hq2; simp
            have hs := hSimp (fun q => is[q.val]'(Nat.lt_of_lt_of_eq q.isLt hlen.symm)) y
            have hres := h (fun q => is[q.val]'(Nat.lt_of_lt_of_eq q.isLt hlen.symm)) y
            dsimp only [slot_fn] at hres
            rw [hs.1, hs.2.1, hs.2.2, ← his_eq] at hres
            exact hres hy
          · intro h isVec y hy
            have hs := hSimp isVec y
            have hres := h (List.ofFn isVec) (by simp) y
            dsimp only [slot_fn] at hy ⊢
            rw [hs.1, hs.2.1, hs.2.2] at hy ⊢
            exact hres hy
        refine (DefRel.and (DefRel.constProp cSide) (DefRel.and hDsaRel hForIs)).congr fun v => ?_
        constructor
        · intro h hk' heq
          rw [hopt] at heq; cases heq
          dsimp only [cSide, ownI, compI, idxF] at h
          exact ⟨h.1.1, h.1.2.1, h.1.2.2.1, h.1.2.2.2, h.2.1, h.2.2⟩
        · intro h
          dsimp only [cSide, ownI, compI, idxF]
          obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h hk hopt
          exact ⟨⟨h1, h2, h3, h4⟩, h5, h6⟩
    have hFrame : DefRel M fun v => ∀ i hk, t.anc.reverse[i]? = some hk →
        0 < holeOwner ns par b i ∧ holeOwner ns par b i ≤ ns.length ∧
          hk ∈ ConLeche.grpNews (ns.getD (holeOwner ns par b i - 1) default).key.lvls
            (ns.getD (holeOwner ns par b i - 1) default).key.ds
            (ctx.hiAt (ns.getD (holeOwner ns par b i - 1) default).anc.length)
            (ns.getD (holeOwner ns par b i - 1) default).grp ∧
          (∃ Y, t.anc.drop (t.anc.length - i) =
            Y ++ (ns.getD (holeOwner ns par b i - 1) default).anc) ∧
          (∀ dsa', DenoteSpine mk.base2.acval envI ψ hi hk.key.ds dsa' →
            keyFrame dsa' hi tv = nlFr mpC ctx d ns ψ ρ xs (holeOwner ns par b i)) ∧
          ∀ is : List V, is.length = hk.nIdx →
          ∀ y, y ∈ˢ is.foldl app (σ_fn v (hi - 1 - (ctx.hiAt 0 + i))) →
            (nlLive mpC ctx d ns ψ ρ xs (holeOwner ns par b i) ∧
              SpineFit (nlFr mpC ctx d ns ψ ρ xs (holeOwner ns par b i))
                ((nlDb mpC d ns (holeOwner ns par b i)).ids
                  (nlComp mpC d ns (holeOwner ns par b i) hk.key.cname)
                  (nlψ envC ns ψ (holeOwner ns par b i))) is →
              nenc (holeOwner ns par b i) (nlComp mpC d ns (holeOwner ns par b i) hk.key.cname)
                (tupW ((nlDb mpC d ns (holeOwner ns par b i)).u
                  (nlComp mpC d ns (holeOwner ns par b i) hk.key.cname)
                  (nlψ envC ns ψ (holeOwner ns par b i))) is) y ∈ˢ G_fn v) ∧
            (¬ (nlLive mpC ctx d ns ψ ρ xs (holeOwner ns par b i) ∧
                SpineFit (nlFr mpC ctx d ns ψ ρ xs (holeOwner ns par b i))
                  ((nlDb mpC d ns (holeOwner ns par b i)).ids
                    (nlComp mpC d ns (holeOwner ns par b i) hk.key.cname)
                    (nlψ envC ns ψ (holeOwner ns par b i))) is) →
              y ∈ˢ is.foldl app (tv (hi - 1 - (ctx.hiAt 0 + i)))) :=
      (DefRel.finForall_lt (n := t.anc.reverse.length) fun i _ => hFrameIdx i).congr fun v =>
        ⟨fun h i hk hiH => h i (List.getElem?_eq_some_iff.mp hiH).1 hk hiH,
         fun h i _ hk hiH => h i hk hiH⟩
    let dsa := nodeDsaI mk ctx ψ t
    have hLen : dsa.length = nlFrLen d ns xs b := by
      simp only [dsa, nodeDsaI, nlFrLen, hb0, ite_false, List.length_map, t, List.getD_eq_getElem?_getD]
    let tailB := nlTail mpC ctx d ns ψ ρ xs b
    let ρ'_fn : Fin (nlFrLen d ns xs b) → (Fin M → V) → V := fun q v =>
      (ftail (fdrop v)) q
    have hρ'_fn : ∀ q, DefFun M (ρ'_fn q) := fun q =>
      (DefFun.proj (V := V) (k := M) ⟨hi + 1 + q.val, by have hq := q.isLt; omega⟩).congr fun v => by
        simp only [ρ'_fn, ftail, fdrop]
        congr 1; apply Fin.ext; dsimp; omega
    have hKeyEq : DefRel M fun v =>
        prepend (ftail (fdrop v)) tailB = keyFrame dsa hi (σ_fn v) := by
      let As_k : Fin (nlFrLen d ns xs b) → (Fin M → V) → V := fun q v =>
        interp V (σ_fn v) (dsa[dsa.length - 1 - q.val]'(by have hq := q.isLt; rw [hLen]; omega))
      have hAs_k : ∀ q, DefFun M (As_k q) := fun q =>
        (interp_defFun_prepend tailT hi _).comp fun l => DefFun.ftake_proj l
      have hEq := DefRel.and
        (DefRel.finForall fun q => DefRel.eq_apply (hρ'_fn q) (hAs_k q))
        (DefRel.constProp (∀ q : Nat, tailB q = tailT q))
      refine hEq.congr fun v => ?_
      have hkf : keyFrame dsa hi (σ_fn v) = prepend (fun q => As_k q v) tailT := by
        unfold keyFrame
        funext idx
        have hl : (dsa.map (interp V (σ_fn v))).length = nlFrLen d ns xs b := by simp [hLen]
        by_cases hidx : idx < nlFrLen d ns xs b
        · rw [consList_getD_of_lt _ _ _ (by omega)]
          simp only [List.getD_eq_getElem?_getD, hl, prepend, dite_eq_left hidx, As_k]
          rw [List.getElem?_eq_getElem (by rw [hl]; omega), Option.getD_some, List.getElem_map]
          congr 2; omega
        · obtain ⟨q, rfl⟩ : ∃ q, idx = q + nlFrLen d ns xs b := ⟨idx - nlFrLen d ns xs b, by omega⟩
          have hca := consList_apply_add (dsa.map (interp V (σ_fn v))) (fun j => σ_fn v (j + hi)) q
          rw [hl] at hca
          rw [hca]
          simp only [prepend, dite_eq_right (by omega : ¬ q + nlFrLen d ns xs b < nlFrLen d ns xs b),
            Nat.add_sub_cancel, σ_fn, dite_eq_right (by omega : ¬ q + hi < hi),
            Nat.add_sub_cancel, tailT]
      rw [hkf, prepend_eq_prepend_iff]
    have hBig := DefRel.and (DefRel.constProp (nlLive mpC ctx d ns ψ ρ xs b))
      (DefRel.exists_fin (DefRel.and (DefRel.and hSat (DefRel.and hAgree (DefRel.and hMember hFrame))) hKeyEq))
    refine hBig.congr fun v' => ?_
    have hσ_app : ∀ (σf : Fin hi → V), σ_fn (fappend σf v') = prepend σf tailT := fun σf => by
      have hft : ftake (fappend σf v') = σf := by
        funext i; simp only [ftake, fappend, dite_eq_left i.isLt]
      dsimp only [σ_fn]; rw [hft]
    have hG_app : ∀ (σf : Fin hi → V), G_fn (fappend σf v') = v' 0 := fun σf => by
      simp only [G_fn, fdrop, fappend]
      have hne : ¬ hi + (0 : Fin (nlFrLen d ns xs b + 1)).val < hi := by omega
      rw [dite_eq_right hne]
      congr 1; apply Fin.ext; dsimp; omega
    have hDropTail : ∀ (σf : Fin hi → V), ftail (fdrop (fappend σf v')) = ftail v' := fun σf => by
      funext q
      simp only [ftail, fdrop, fappend]
      have hne : ¬ hi + q.succ.val < hi := by omega
      rw [dite_eq_right hne]
      congr 1; apply Fin.ext; dsimp; omega
    unfold nodeAdmSet nodeAdm
    rw [ite_eq_right hb0]
    refine and_congr_right fun _ => ?_
    constructor
    · rintro ⟨σf, ⟨h1, h2, h3, h4⟩, h5⟩
      rw [hσ_app] at h1 h2
      rw [hσ_app, hG_app] at h3 h4
      rw [hσ_app, hDropTail] at h5
      exact ⟨prepend σf tailT, ⟨h1, h2, h3, h4⟩, h5⟩
    · rintro ⟨σ, ⟨h1, h2, h3, h4⟩, h5⟩
      have htail : ∀ j, hi ≤ j → σ j = tv j := fun j hj => h2 j (fun h => by exact absurd h.1 (Nat.not_lt.mpr hj))
      have hσ_eq : σ = prepend (fun i : Fin hi => σ i.val) tailT := by
        funext j
        by_cases hj : j < hi
        · simp only [prepend, dite_eq_left hj]
        · simp only [prepend, dite_eq_right hj, tailT, htail j (Nat.le_of_not_lt hj)]
          congr 1; omega
      rw [hσ_eq] at h1 h2 h3 h4 h5
      refine ⟨fun i => σ i.val, ⟨?_, ?_, ?_, ?_⟩, ?_⟩
      · rw [hσ_app]; exact h1
      · rw [hσ_app]; exact h2
      · rw [hσ_app, hG_app]; exact h3
      · rw [hσ_app, hG_app]; exact h4
      · rw [hσ_app, hDropTail]; exact h5

theorem dyn_hAdmSet (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length) (par : Nat → Nat) :
    ∀ b, b < ns.length + 1 → ∀ (G : V) (ρ' : Fin (nlFrLen d ns xs b) → V),
      nodeAdmSet mk mpC ctx d ns ψ ρ xs par b G ρ' →
      nlLive mpC ctx d ns ψ ρ xs b ∧
      Sat V ((nlDb mpC d ns b).params (nlψ envC ns ψ b)).reverse
        (prepend ρ' (nlTail mpC ctx d ns ψ ρ xs b)) ∧
      ∀ c, c < (nlDb mpC d ns b).N →
        (nlDb mpC d ns b).idx (nlψ envC ns ψ b) (prepend ρ' (nlTail mpC ctx d ns ψ ρ xs b)) c =
          (nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b) c :=
  fun b hb G ρ' h =>
    dyn_hAdm H ψ ρ xs hparams hxs par b hb (fun b' c t y => nenc b' c t y ∈ˢ G)
      (prepend ρ' (nlTail mpC ctx d ns ψ ρ xs b)) h

theorem dyn_topSet (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {par : Nat → Nat} (hPP : ParentPtrs ns par) :
    ∀ b, b < ns.length + 1 → nlLive mpC ctx d ns ψ ρ xs b → ∀ G : V,
      (∀ b' c t y, b' < ns.length + 1 → nlDp ns b' < nlDp ns b → c < (nlDb mpC d ns b').N →
        nlLive mpC ctx d ns ψ ρ xs b' →
        t ∈ˢ (nlDb mpC d ns b').idx (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c →
        y ∈ˢ app ((nlDb mpC d ns b').carrier (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c) t →
        nenc b' c t y ∈ˢ G) →
      nodeAdmSet mk mpC ctx d ns ψ ρ xs par b G (nlFrFin mpC ctx d ns ψ ρ xs b) := by
  intro b hb hlv G hG
  unfold nodeAdmSet
  rw [prepend_nlFrFin_nlTail]
  exact dyn_top H ψ ρ xs hparams hxs hPP b hb hlv (fun b' c t y => nenc b' c t y ∈ˢ G) hG

theorem dyn_transSet (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    (par : Nat → Nat) :
    ∀ b, b < ns.length + 1 → ∀ G : V,
      (∀ b' c t y, nenc b' c t y ∈ˢ G →
        y ∈ˢ app ((lfpSClause (nlDb mpC d ns b') (nlψ envC ns ψ b')
          (pinIdx (nlDb mpC d ns b') (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b')
            (nlLive mpC ctx d ns ψ ρ xs b'))
          (nlFrLen d ns xs b') (nlTail mpC ctx d ns ψ ρ xs b')).carrier
          (nlFrFin mpC ctx d ns ψ ρ xs b') c) t) →
      ∀ ρ' : Fin (nlFrLen d ns xs b) → V, nodeAdmSet mk mpC ctx d ns ψ ρ xs par b G ρ' → ∀ Y,
      InTupleSpace ((nlDb mpC d ns b).w (nlψ envC ns ψ b)) (nlDb mpC d ns b).N
        ((nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) Y →
      TupleLe (nlDb mpC d ns b).N
        ((nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) Y
        ((nlDb mpC d ns b).carrier (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) →
      ∀ t c j fs, c < (nlDb mpC d ns b).N →
        (nlDb mpC d ns b).HFits (nlψ envC ns ψ b)
          (prepend ρ' (nlTail mpC ctx d ns ψ ρ xs b)) Y t c j fs →
        (nlDb mpC d ns b).HFits (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)
          ((nlDb mpC d ns b).carrier (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b)) t c j fs :=
  fun b hb G hG ρ' hadm Y hY hle t c j fs hc hf =>
    dyn_trans H ψ ρ xs hparams hxs par b hb (fun b' c t y => nenc b' c t y ∈ˢ G) hG
      (prepend ρ' (nlTail mpC ctx d ns ψ ρ xs b)) hadm Y hY hle t c j fs hc hf

end Frames

/-! ## The dynamic part's context -/

/-- **The dynamic part's context from the stage's** (`nestedClassNodes`'
node context). -/
theorem dynCtx_of {F : Nat}
    {envC envI : Env} {pp : BlockShape} {mpC : EnvModelM V envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → Term}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : RecCtxBase V F envC envI pp mpC dR isRecR A kindsR nfsR posR)
    {mk : EnvModelM V envI} (hmkC : LfpCover mk pp.memberNames)
    (hmk : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks)
    (hag : ∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n)
    (hsubC : ∀ D ∈ mpC.lfpBlocks, D = dR.toLfp ∨ D ∈ mk.lfpBlocks)
    (htr : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : Term},
      denote mk.base2.acval envI ψ dd e = some ea →
        denote mpC.base2.acval envC ψ dd e = some ea)
    (hcoreK : BlockHoleCtxFacts mk.base2 dR pp.lps pp.formers pp isRecR)
    {fvsP : List Expr} {ns : List PosTree}
    (hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?) t)
    (hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns)
    (hpar : ∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids)
    (hsem : ∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ (pp.nestCtx fvsP envI.find?)
      (dR.holeCtx ψ).reverse t)
    (hF : NodeListFacts mpC (pp.nestCtx fvsP envI.find?) ns)
    (hparF : fvsP.length = pp.nP ∧ ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = .fvar i ty)
    (hparS : ∀ x ∈ fvsP, ConLeche.ScB pp.nP x) :
    DynCtx F mk mpC (pp.nestCtx fvsP envI.find?) dR ns := by
  obtain ⟨hPos, henvC, -, -, hN, hS, -, -, hdR, hlfp, hcovC, -⟩ := hctx
  obtain ⟨cvTa0, -, -, -, h0, -⟩ := ConLeche.checkBlockPositivity_m2 hPos
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hkN := lfp_namesLen mpC hlfp
  refine ⟨hcovC, hlfp, contCover_of hmkC (fun _ => rfl), hmk, hag, hsubC, htr,
    ⟨pp.nP, pp.ctorGroups, henvC⟩, hok, hkids, hpar, hsem, hF, rfl, hparF, hparS, rfl,
    fun ψ => ?_,
    fun n hn => ?_, ⟨pp.formers, pp, isRecR, hN, hcoreK.1⟩⟩
  · -- the hole context: the parameters, then one hole per member
    have h0' : pp.formers[0]? = some cvTa0 := by rw [List.head?_eq_getElem?] at h0; exact h0
    obtain ⟨-, hFD0⟩ := hcoreK.1 0 cvTa0 h0'
    rw [List.length_reverse, BlockData.holeCtx, List.length_append, List.length_map,
      List.length_range, BlockData.params, List.length_take, hFD0.len ψ]
    show min _ _ + _ = pp.nP + pp.memberNames.length + 0
    have : (blockDataOf V pp pk uOfD ppsOf).k = pp.memberNames.length := by
      simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
        ConLeche.BlockShape.memberNames]
    rw [this]
    have : (blockDataOf V pp pk uOfD ppsOf).nP = pp.nP := rfl
    rw [this]
    omega
  · -- the members are stored at the block's level parameters
    change n ∈ pp.memberNames at hn
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hn
    have hck : c < (blockDataOf V pp pk uOfD ppsOf).k := by
      change c < pp.members.length
      simpa [ConLeche.BlockShape.memberNames] using hc
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, pp.formers[c]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hck)⟩
    have hname := hN.1 c cvTb hcvb
    obtain ⟨⟨cvS, hf, hDS⟩, -⟩ := hcoreK.1 c cvTb hcvb
    rw [← hname] at hf
    unfold BlockData.memberName at hf
    change envI.find? (pp.memberNames.getD c .anonymous) = _ at hf
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at hf
    exact ⟨_, _, hf, hDS.lps.trans (hS.lpsT c cvTb hck hcvb)⟩

omit [SetTheory V] in
/-- **The canonical parameters**, opened off a closed former type: the
variables `0 ..< n`, closed below `n` (`DynCtx.hparF`, `DynCtx.hparS`). -/
theorem canonPars_of_open {n : Nat} {e : Expr} {fvs : List Expr} {rest : Expr}
    (h : ConLeche.openPisAtFvars n e 0 = some (fvs, rest)) (he : ConLeche.ScB 0 e) :
    (fvs.length = n ∧ ∀ (i : Nat) (x : Expr), fvs[i]? = some x → ∃ ty, x = .fvar i ty) ∧
    ∀ x ∈ fvs, ConLeche.ScB n x := by
  obtain ⟨hl, hfv, -⟩ := ConLeche.ScB.openPis h he
  refine ⟨⟨hl, fun i x hx => ?_⟩, fun x hx => ?_⟩
  · obtain ⟨ty, rfl, -⟩ := hfv i x hx
    exact ⟨ty, by rw [Nat.zero_add]⟩
  · obtain ⟨i, hi⟩ := List.getElem?_of_mem hx
    obtain ⟨ty, rfl, hty⟩ := hfv i x hi
    have hil : i < n := by rw [← hl]; exact (List.getElem?_eq_some_iff.mp hi).1
    exact ConLeche.ScB.fvar (by omega) hty

end ConLeche.Model
