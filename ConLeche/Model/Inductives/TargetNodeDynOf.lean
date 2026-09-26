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

public section

/-!
# The node presentation's dynamic part: `hAdm`, `top`, `trans`

At the admissible frames `nodeAdm` (`TargetNodeAdm.lean`):

* `hAdm` — an admissible frame satisfies the node's parameter telescope
  (K.52, `nodeKeyFit`) and reads the true frame's index sets (N2: the
  valuations agree off the holes, `grp_idx_eq`);
* `top` — the TRUE valuation (the holes' constants) is admissible once the
  shallower nodes' true elements satisfy `G`: a constant applied at full
  arity at its owner's parameters is the owner's true carrier (`leaf`);
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
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal IndCaps CheckM NestCtx NestHole
  BlockParts BlockShape fueledOps PosTree PosNodeOk PosD)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-! ## Readings -/

/-! ## The true valuation -/

section True

variable {envC : Env} (mpC : EnvModelM V μ envC) (ctx : NestCtx) (ψ : Name → Nat) (ρ : Nat → V)
  (xs : List V)

/-- **The true valuation of a stack grown by holes on top**: the new
holes' constants consed on the old stack's. -/
theorem trueVal_append (hs prog : List NestHole) :
    trueVal mpC ctx ψ ρ xs (hs ++ prog)
      = consList ((hs.reverse.map fun h =>
          (denoteMeta mpC.base2.acval envC ψ 0 (.const h.key.cname h.key.lvls)).getD default).map
            (interp V ρ)) (trueVal mpC ctx ψ ρ xs prog) := by
  unfold trueVal nodeTrueVal nodeHv nodeHoleConsts
  rw [← consList_append]
  congr 1
  simp only [List.reverse_append, List.map_append, List.map_map, List.append_assoc]
  rfl

end True

/-! ## The context, bundled -/

/-- **What the dynamic part reads** (`nestedClassNodes`' node context,
bundled): the constructors' model `mpC` covered and recording the block;
the formers' model `mk` covering the walk's context, its blocks among
`mpC`'s (and `mpC`'s the block's or `mk`'s), its readings `mpC`'s; the
list's nodes, owned, closed under kids and parents, read in their stack
contexts; the class tie's node facts; the walk's context the block's. -/
structure DynCtx (F : Nat) {envI envC : Env} (mk : EnvModelM V μ envI) (mpC : EnvModelM V μ envC)
    (ctx : NestCtx) (d : BlockData V) (ns : List PosTree) : Prop where
  hcovC : LfpCover mpC []
  hd0 : d.toLfp ∈ mpC.lfpBlocks
  hcov : ContCover mk ctx
  hsub : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks
  hag : ∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n
  hsubC : ∀ D ∈ mpC.lfpBlocks, D = d.toLfp ∨ D ∈ mk.lfpBlocks
  htr : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : AnnotTerm},
    denoteMeta mk.base2.acval envI ψ dd e = some ea → denoteMeta mpC.base2.acval envC ψ dd e = some ea
  henvC : ∃ (nP : Nat) (ctorsAs : List (List (ConstantVal × Nat))),
    envC = ConLeche.consBlockCtors nP ctorsAs envI
  hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI ctx t
  hown : ∀ t ∈ ns, NodeOwned (fueledOps .verified F) envI ctx t
  hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns
  hpar : ∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids
  hsem : ∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ ctx (d.holeCtx ψ).reverse t
  hF : NodeListFacts mpC ctx ns
  hnP : ctx.nP = d.nP
  hnames : ctx.names = d.toLfp.names
  hΔ0 : ∀ ψ, ((d.holeCtx ψ).reverse).length = ctx.hiAt 0
  hlpsM : ∀ n ∈ ctx.names, ∃ cv caps, envI.find? n = some (.indInfo cv caps) ∧
    cv.levelParams = ctx.lps
  hformers : ∃ (cvTas : List ConstantVal) (p : BlockShape) (isRec : Bool),
    BlockNamesOk (V := V) d cvTas ∧
    ∀ (c : Nat) (cvTb : ConstantVal), cvTas[c]? = some cvTb →
      envI.find? cvTb.name = some (.indInfo cvTb (ConLeche.blockCapsAt p c isRec)) ∧
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
        (ctx.hiAt prog.length + grp.length) us ds
        (ConLeche.grpSub us (ctx.hiAt prog.length) grp) ctors) ts := by
  cases h with
  | frame _ _ _ hnd _ _ hgrp hctors _ hwalk => exact ⟨hnd, hgrp, _, hctors, hwalk⟩

/-- **A listed node's recorded block** (`nlDb` at the node): the block
`lfpSel` selects for the key's container is the formers' model's, as wide
as its members, every member in the frame's group (N2), the group's
head one of them, all at the head's level parameters (distinct), the
key's parameters its parameter count, the group well formed. -/
theorem dyn_nodeBlock {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI}
    {mpC : EnvModelM V μ envC} {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}
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
      GrpWf ctx (lfpSel mpC d.toLfp t.key.cname) (ctx.hiAt t.anc.length) t.key.lvls t.key.ds
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
  obtain ⟨cvI, capsI, hfI, hul⟩ := ConLeche.nestInstType_lvls hnI
  rw [H.hcov.find, hp₀H, ← hmmH, hfc] at hfI
  obtain ⟨rfl, rfl⟩ : cv = cvI ∧ caps = capsI := by simpa using hfI
  -- the key's container's level parameters, at the constructors' environment
  obtain ⟨nPc, ctorsAs, henvC⟩ := H.henvC
  have hlpsC := posNodeOk_lps H.hcov H.hsub henvC hok _ hheadG
  obtain ⟨lps', hl'⟩ := blk_lps_envC H.hcov H.hsub henvC hD
  obtain ⟨cv', caps', hfC', hfI', hcl'⟩ := hl' mm hmm
  rw [hfc] at hfI'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hfI'
  refine ⟨hD, H.hcovC.wid D hDC, hblkD.nodup, hkN, fun c hc => ⟨hc, ?_⟩, mm, hmm, hmmH, cv, caps,
    hfc, hlps, ?_, hndl, hul, fun ψ' => hlenP0 ψ',
    hnL.imp (fun ⟨L', hL', hne'⟩ => ⟨_, L', hL', hne'⟩) id, hnd, fun p hp => ⟨?_, hinst p hp⟩⟩
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
  · exact exists_member_of_mem_names hkN (hgrpN _ (List.mem_map_of_mem hp)) |>.imp
      fun i ⟨hi, hi'⟩ => ⟨hi, hi'.symm⟩

/-! ## The true valuation's holes -/

section Pos

variable {envC : Env} (mpC : EnvModelM V μ envC) (ctx : NestCtx) (ψ : Name → Nat) (ρ : Nat → V)
  (xs : List V)

theorem trueVal_pos (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) {k : Nat}
    (hk : k < ctx.names.length + prog.length) :
    trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.nP + k))
      = interp V ρ (((nodeHv mpC.base2.acval envC ctx ψ prog)[k]?).getD default) := by
  unfold trueVal nodeTrueVal
  have hlv : (nodeHv mpC.base2.acval envC ctx ψ prog).length = ctx.names.length + prog.length := by
    simp [nodeHv, nodeHoleConsts]
  have hlen : (xs.take ctx.nP ++ (nodeHv mpC.base2.acval envC ctx ψ prog).map (interp V ρ)).length
      = ctx.hiAt prog.length := by
    rw [List.length_append, List.length_take, List.length_map, hlv]
    simp only [ConLeche.NestCtx.hiAt]; omega
  rw [consList_apply_lt _ _ _ (by rw [hlen]; simp only [ConLeche.NestCtx.hiAt]; omega), hlen,
    show ctx.hiAt prog.length - 1 - (ctx.hiAt prog.length - 1 - (ctx.nP + k)) = ctx.nP + k by
      simp only [ConLeche.NestCtx.hiAt]; omega,
    List.getElem?_append_right (by rw [List.length_take]; omega), List.length_take,
    show ctx.nP + k - min ctx.nP xs.length = k by omega, List.getElem?_map,
    List.getElem?_eq_getElem (by rw [hlv]; exact hk)]
  simp

/-- **A member hole of the true valuation** holds the member's constant. -/
theorem trueVal_member (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) {t : Nat}
    (ht : t < ctx.names.length) :
    trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.nP + t))
      = interp V ρ ((denoteMeta mpC.base2.acval envC ψ 0
          (.const (ctx.names[t]'ht) (ctx.lps.map Level.param))).getD default) := by
  rw [trueVal_pos mpC ctx ψ ρ xs hxs prog (by omega)]
  congr 1
  unfold nodeHv nodeHoleConsts
  rw [List.map_append, List.getElem?_append_left (by simpa using ht), List.getElem?_map,
    List.getElem?_map, List.getElem?_eq_getElem ht]
  rfl

/-- **A frame hole of the true valuation** holds its group member's constant. -/
theorem trueVal_frame (hxs : ctx.nP ≤ xs.length) (prog : List NestHole) {i : Nat}
    {hk : NestHole} (hi : prog.reverse[i]? = some hk) :
    trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i))
      = interp V ρ ((denoteMeta mpC.base2.acval envC ψ 0
          (.const hk.key.cname hk.key.lvls)).getD default) := by
  have hil : i < prog.length := by
    have := (List.getElem?_eq_some_iff.mp hi).1; simpa using this
  have e : ctx.hiAt 0 + i = ctx.nP + (ctx.names.length + i) := by
    simp only [ConLeche.NestCtx.hiAt]; omega
  rw [e, trueVal_pos mpC ctx ψ ρ xs hxs prog (by omega)]
  congr 1
  unfold nodeHv nodeHoleConsts
  rw [List.map_append, List.getElem?_append_right (by simp),
    show ctx.names.length + i - (List.map (fun a => (denoteMeta mpC.base2.acval envC ψ 0 a).getD
      default) (List.map (fun n => Expr.const n (List.map Level.param ctx.lps)) ctx.names)).length
      = i by simp, List.getElem?_map, List.getElem?_map, hi]
  rfl

end Pos

/-! ## Owners -/

/-- **Every hole of a listed node's stack has a listed OWNER above it**,
whose group and frames are a suffix of the stack. -/
theorem dyn_owner {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI}
    {mpC : EnvModelM V μ envC} {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}
    (H : DynCtx F mk mpC ctx d ns) :
    ∀ (n : Nat) (t : PosTree), t ∈ ns → nlDd ns - t.height ≤ n → ∀ hk ∈ t.anc,
      ∃ u ∈ ns, t.height < u.height ∧
        hk ∈ ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp ∧
        ∃ X, t.anc = X ++ (ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length)
          u.grp).reverse ++ u.anc
  | 0, t, ht, hn, hk, hkm => by
    have := height_le_nlDd ht
    have := PosTree.height_pos t
    omega
  | n + 1, t, ht, hn, hk, hkm => by
    obtain ⟨-, -, -, -, -, hanc⟩ := H.hok t ht
    rcases hanc with ⟨hao, -⟩ | ⟨han, -⟩
    · have hne : t.occ ≠ [] := by
        intro h; rw [hao, h] at hkm; exact nomatch hkm
      obtain ⟨p, hp, htp⟩ := H.hpar t ht hne
      have hocc := (H.hok p hp).2.2.1 t htp
      have hlt := PosTree.height_kid htp
      rw [hao, hocc, List.mem_append, List.mem_reverse] at hkm
      rcases hkm with hkm | hkm
      · exact ⟨p, hp, hlt, hkm, [], by rw [hao, hocc, List.nil_append]⟩
      · have hpd := height_le_nlDd hp
        obtain ⟨u, hu, hlt', hmem, X, hX⟩ := dyn_owner H n p hp (by omega) hk hkm
        refine ⟨u, hu, Nat.lt_trans hlt hlt', hmem,
          (ConLeche.grpNews p.key.lvls p.key.ds (ctx.hiAt p.anc.length) p.grp).reverse ++ X, ?_⟩
        rw [hao, hocc, hX]
        simp only [List.append_assoc]
    · rw [han] at hkm; exact nomatch hkm

/-! ## A listed node's true frame -/

section Frames

variable {F : Nat} {envI envC : Env} {mk : EnvModelM V μ envI} {mpC : EnvModelM V μ envC}
  {ctx : NestCtx} {d : BlockData V} {ns : List PosTree}

/-- A listed node's key is read where its frame is derived: `nodeDsaI`. -/
theorem dyn_dsaI (H : DynCtx F mk mpC ctx d ns) {t : PosTree} (ht : t ∈ ns) (ψ : Name → Nat) :
    DenoteMetaSpine mk.base2.acval envI ψ (ctx.hiAt t.anc.length) t.key.ds (nodeDsaI mk ctx ψ t) := by
  obtain ⟨dsa, hdsa⟩ := (H.hsem t ht ψ).1
  rw [nodeDsaI, DenoteMetaSpine.getD_eq hdsa]
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
  rw [if_neg hb]
  generalize ns.getD (b - 1) default = t at ht ⊢
  obtain ⟨dsa, hdsa⟩ := (H.hsem t ht ψ).1
  have hI : nodeDsaI mk ctx ψ t = dsa := by rw [nodeDsaI, DenoteMetaSpine.getD_eq hdsa]
  rw [hI]
  have hD : ctx.nP + (nodeHoleConsts ctx t.occ).length = ctx.hiAt t.occ.length := by
    rw [nodeHoleConsts_length]; simp only [NestCtx.hiAt]; omega
  unfold nodeFr
  rw [hD]
  obtain ⟨-, -, -, -, -, hanc⟩ := H.hok t ht
  rcases hanc with ⟨hao, -⟩ | ⟨han, hds⟩
  · rw [hao] at hdsa ⊢
    rw [DenoteMetaSpine.getD_eq (DenoteMetaSpine.transport (fun e _ he => H.htr ψ _ e he) hdsa)]
    rfl
  · rw [han] at hdsa ⊢
    have hlift := DenoteMetaSpine.lift (m := mk.base2) (φ := ψ) (h := ctx.hiAt 0)
      (D := ctx.hiAt t.occ.length) (by simp only [NestCtx.hiAt]; omega) (fun x hx => (hds x hx).2)
      hdsa
    rw [DenoteMetaSpine.getD_eq (DenoteMetaSpine.transport (fun e _ he => H.htr ψ _ e he) hlift)]
    have htv : nodeTrueVal ctx.nP (nodeHv mpC.base2.acval envC ctx ψ t.occ) xs ρ
        = trueVal mpC ctx ψ ρ xs (t.occ ++ []) := by rw [List.append_nil]; rfl
    rw [htv, trueVal_append]
    generalize hvs : (List.map (interp V ρ) (List.map (fun h =>
      (denoteMeta mpC.base2.acval envC ψ 0 (.const h.key.cname h.key.lvls)).getD default)
        t.occ.reverse)) = vs
    have hvl : vs.length = t.occ.length := by rw [← hvs]; simp
    have e1 : ctx.hiAt t.occ.length - ctx.hiAt 0 = vs.length := by
      rw [hvl]; simp only [NestCtx.hiAt]; omega
    have e2 : ctx.hiAt t.occ.length = ctx.hiAt 0 + vs.length := by
      rw [hvl]; simp only [NestCtx.hiAt]; omega
    rw [e1, e2, keyFrame_lift]
    rfl

/-- **`hAdm`**: an admissible frame satisfies the node's parameter
telescope (node `0`: the prefix's parameters fit; a derived node: K.52,
`nodeKeyFit`) and reads the true frame's index sets below the width (N2:
the valuations agree off the holes, `grp_idx_eq`, every member in the
frame's group). -/
theorem dyn_hAdm (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (par : Nat → Nat) :
    ∀ b, b < ns.length + 1 → ∀ G ρ', nodeAdm mk mpC ctx d ns ψ ρ xs par b G ρ' →
      Sat V ((nlDb mpC d ns b).params (nlψ envC ns ψ b)).reverse ρ' ∧
      ∀ c, c < (nlDb mpC d ns b).N → (nlDb mpC d ns b).idx (nlψ envC ns ψ b) ρ' c
        = (nlDb mpC d ns b).idx (nlψ envC ns ψ b) (nlFr mpC ctx d ns ψ ρ xs b) c := by
  intro b hb G ρ' hadm
  by_cases hb0 : b = 0
  · subst hb0
    unfold nodeAdm at hadm
    rw [if_pos rfl] at hadm
    subst hadm
    refine ⟨?_, fun _ _ => rfl⟩
    simp only [nlDb, nlψ, nlFr, if_true]
    have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hparams
    rw [List.append_nil] at this
    exact this
  · have ht := getD_mem_of_lt (ns := ns) (b := b) (by omega) (by omega)
    unfold nodeAdm at hadm
    rw [if_neg hb0] at hadm
    obtain ⟨σ, hσ, rfl⟩ := hadm
    rw [dyn_nlFr H hb0 ht ψ ρ xs,
      show nlDb mpC d ns b = lfpSel mpC d.toLfp (ns.getD (b - 1) default).key.cname by
        unfold nlDb; rw [if_neg hb0],
      show nlψ envC ns ψ b = nodeψ envC ψ (ns.getD (b - 1) default) by
        unfold nlψ; rw [if_neg hb0]]
    generalize ns.getD (b - 1) default = t at ht hσ ⊢
    obtain ⟨hD, hwid, hnN, hkN, hall, mm, hmm, hmmH, cv, caps, hfc, hlps, hlpsOf, hndl, hul, hlenP,
      -, hg⟩ := dyn_nodeBlock H ht
    have hψ : nodeψ envC ψ t = Level.substFn ψ cv.levelParams t.key.lvls := by
      unfold nodeψ; rw [hlpsOf]
    rw [hψ]
    have hws := posNodeOk_dsAnc (H.hok t ht)
    have hdsa := dyn_dsaI H ht ψ
    refine ⟨nodeKeyFit mk (H.hΔ0 ψ) (H.hok t ht) (H.hsem t ht ψ) hD hmm hmmH hfc (hlenP _).symm
      hdsa σ hσ.sat, fun c hc => ?_⟩
    rw [hwid] at hc
    exact grp_idx_eq mk hD hnN hkN H.hcov.find hlps hndl hul hws hdsa (hlenP _) hg (hall c hc)
      hσ.agree

/-- A constant's reading, at the constructors' model, is the formers'
model's leaf (stored at `envI`, at its level count). -/
theorem dyn_constRead (H : DynCtx F mk mpC ctx d ns) {ψ : Name → Nat} {n : Name}
    {us : List Level} {cv : ConstantVal} {caps : IndCaps}
    (hf : envI.find? n = some (.indInfo cv caps)) (hlen : us.length = cv.levelParams.length) :
    (denoteMeta mpC.base2.acval envC ψ 0 (.const n us)).getD default
      = mk.base2.acval n (Level.substFn ψ cv.levelParams us) := by
  rw [H.htr ψ 0 _ (denoteMeta_const hf hlen)]
  rfl

/-- **The true valuation satisfies the stack context**: the prefix's
parameters fit (`hparams`), each member's constant inhabits its former's
type (`blockHoleCtx_sat`), each frame hole's constant its container's
former type at the key's levels (`EnvModelM.constType`). -/
theorem dyn_trueVal_sat (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) :
    ∀ (prog : List NestHole), (∀ h ∈ prog, ∃ cv caps,
        envI.find? h.key.cname = some (.indInfo cv caps) ∧ h.key.lvls.length = cv.levelParams.length) →
      Sat V (stackCtx mk.base2 ψ ctx prog (d.holeCtx ψ).reverse) (trueVal mpC ctx ψ ρ xs prog)
  | [], _ => by
    obtain ⟨cvTas, p, isRec, hN, hF⟩ := H.hformers
    have hkN := lfp_namesLen mpC H.hd0
    rw [stackCtx_nil]
    unfold trueVal nodeTrueVal
    rw [consList_append]
    refine blockHoleCtx_sat mk hN hF ψ _ ?_ ?_ _ ?_
    · simp only [nodeHv, nodeHoleConsts, List.reverse_nil, List.map_nil, List.append_nil,
        List.length_map, H.hnames]
      exact hkN
    · intro t ht σ
      have htn : t < ctx.names.length := by rw [H.hnames]; exact hkN ▸ ht
      obtain ⟨cv, caps, hf, hlps⟩ := H.hlpsM _ (List.getElem_mem htn)
      have hlen : (ctx.lps.map Level.param).length = cv.levelParams.length := by
        rw [List.length_map, hlps]
      simp only [nodeHv, nodeHoleConsts, List.reverse_nil, List.map_nil, List.append_nil,
        List.map_map]
      rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem htn,
        Option.map_some, Option.getD_some]
      simp only [Function.comp_apply]
      rw [dyn_constRead H hf hlen, hlps, ConLeche.Level.substFn_param_self,
        acval_interp_closed mk.base2 _ ψ σ ρ]
      congr 2
      show d.memberNames.getD t .anonymous = ctx.names[t]
      rw [List.getD_eq_getElem?_getD, ← show d.toLfp.names = d.memberNames from rfl, ← H.hnames,
        List.getElem?_eq_getElem htn, Option.getD_some]
    · have := sat_of_spineFit (Δ₀ := []) (Sat_nil V ρ) hparams
      rw [List.append_nil] at this
      rw [H.hnP]; exact this
  | h :: prog, hprog => by
    obtain ⟨cv, caps, hf, hlen⟩ := hprog h List.mem_cons_self
    have ih := dyn_trueVal_sat H ψ ρ xs hparams prog fun h' hh' => hprog h' (List.mem_cons_of_mem _ hh')
    obtain ⟨ta, hta, -, hmem⟩ := EnvModelM.constType mk (φ := ψ) 0 h.key.cname (.indInfo cv caps)
      h.key.lvls hf rfl hlen
    have hty : (denoteMeta mk.base2.acval envI ψ 0 (nestHoleTy ctx h)).getD .prf = ta := by
      have hta' : denoteMeta mk.base2.acval envI ψ 0
          (cv.type.instantiateLevelParams cv.levelParams h.key.lvls) = some ta := hta
      unfold nestHoleTy
      rw [H.hcov.find, hf]
      simp only
      rw [hta']; rfl
    have hst : stackCtx mk.base2 ψ ctx (h :: prog) (d.holeCtx ψ).reverse
        = ta :: stackCtx mk.base2 ψ ctx prog (d.holeCtx ψ).reverse := by
      unfold stackCtx; rw [List.map_cons, List.cons_append, hty]
    rw [hst, show h :: prog = [h] ++ prog from rfl, trueVal_append]
    simp only [List.reverse_singleton, List.map_cons, List.map_nil, consList_cons, consList_nil]
    refine Sat_cons V ih ?_
    rw [dyn_constRead H hf hlen, acval_interp_closed mk.base2 _ _ ρ]
    exact hmem _

/-! ## The true valuation's holes, read at full arity -/

/-- A listed node's group members are stored inductives at the key's
level count. -/
theorem dyn_holeFound (H : DynCtx F mk mpC ctx d ns) {u : PosTree} (hu : u ∈ ns) {hk : NestHole}
    (hk_mem : hk ∈ ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp) :
    ∃ cv caps, envI.find? hk.key.cname = some (.indInfo cv caps) ∧
      hk.key.lvls.length = cv.levelParams.length := by
  simp only [ConLeche.grpNews, List.mem_map] at hk_mem
  obtain ⟨p, hp, rfl⟩ := hk_mem
  obtain ⟨-, -, -, hinst, -⟩ := posD_frame_inv (H.hok u hu).1
  obtain ⟨nI, hnI⟩ := hinst p hp
  obtain ⟨cv, caps, hf, hl⟩ := ConLeche.nestInstType_lvls hnI
  rw [H.hcov.find] at hf
  exact ⟨cv, caps, hf, hl⟩

/-- Every hole of a listed node's stack is a stored inductive at its level
count. -/
theorem dyn_stackFound (H : DynCtx F mk mpC ctx d ns) {t : PosTree} (ht : t ∈ ns) :
    ∀ hk ∈ t.anc, ∃ cv caps, envI.find? hk.key.cname = some (.indInfo cv caps) ∧
      hk.key.lvls.length = cv.levelParams.length := by
  intro hk hkm
  obtain ⟨u, hu, -, hmem, -⟩ := dyn_owner H _ t ht (Nat.le_refl _) hk hkm
  exact dyn_holeFound H hu hmem

/-- **A member hole of the true valuation at full arity**, at the block's
parameters and a fitting index spine, is node `0`'s true carrier there
(the clause's `leaf`). -/
theorem dyn_memberLeaf (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V)
    (xs : List V) (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    (prog : List NestHole) {t : Nat} (ht : t < ctx.names.length) {is : List V}
    (hfit : SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t ψ) is) :
    (xs.take ctx.nP ++ is).foldl app
        (trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.nP + t)))
      = app (d.toLfp.carrier ψ (consList (xs.take d.nP) ρ) t) (tupW (d.toLfp.u t ψ) is) := by
  have hkN := lfp_namesLen mpC H.hd0
  have htk : t < d.toLfp.k := by rw [← hkN, ← H.hnames]; exact ht
  obtain ⟨cv, caps, hf, hlps⟩ := H.hlpsM _ (List.getElem_mem ht)
  have hlen : (ctx.lps.map Level.param).length = cv.levelParams.length := by
    rw [List.length_map, hlps]
  rw [trueVal_member mpC ctx ψ ρ xs (by rw [H.hnP]; exact hxs) prog ht, dyn_constRead H hf hlen, hlps,
    ConLeche.Level.substFn_param_self, ← H.hag _ (by rw [hf]; rfl)]
  have hmem : d.toLfp.member t = ctx.names[t] := by
    unfold LfpDatum.member
    rw [List.getD_eq_getElem?_getD, ← H.hnames, List.getElem?_eq_getElem ht, Option.getD_some]
  rw [← hmem, H.hnP]
  rw [H.hnP] at hfit
  exact (mpC.lfpClause_of_mem H.hd0).leaf t htk ψ ρ _ is hparams hfit

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
    {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mk.base2.acval envI ψ (ctx.hiAt prog.length) hk.key.ds dsa) :
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
  have hGl : G.length = u.grp.length := by rw [← hG]; simp [ConLeche.grpNews]
  rw [trueVal_append]
  generalize hvs : List.map (interp V ρ) (List.map (fun h =>
    (denoteMeta mpC.base2.acval envC ψ 0 (.const h.key.cname h.key.lvls)).getD default)
      (X ++ G.reverse).reverse) = vs
  have hvl : vs.length = X.length + G.length := by rw [← hvs]; simp; omega
  have hlen : ctx.hiAt ((X ++ G.reverse) ++ u.anc).length = ctx.hiAt u.anc.length + vs.length := by
    rw [hvl]; simp only [List.length_append, List.length_reverse, ConLeche.NestCtx.hiAt]; omega
  rw [hlen] at hdsa ⊢
  have hlift := DenoteMetaSpine.lift (m := mk.base2) (φ := ψ) (h := ctx.hiAt u.anc.length)
    (D := ctx.hiAt u.anc.length + vs.length) (by omega)
    (fun x hx => (posNodeOk_dsAnc (H.hok u hu) x hx).1) (dyn_dsaI H hu ψ)
  rw [DenoteMetaSpine.unique hdsa hlift, Nat.add_sub_cancel_left, keyFrame_lift]

/-- **A frame hole of the true valuation at full arity**, at its key's
parameters and an index spine fitting its owner `o`'s telescope, is `o`'s
true carrier there (the clause's `leaf` at `o`'s true frame, which
satisfies the telescope by K.52). -/
theorem dyn_ownerLeaf (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {o : Nat} (ho : o ≠ 0) (hu : ns.getD (o - 1) default ∈ ns) {prog : List NestHole}
    {i : Nat} {hk : NestHole} (hi : prog.reverse[i]? = some hk)
    (hk_mem : hk ∈ ConLeche.grpNews (ns.getD (o - 1) default).key.lvls
      (ns.getD (o - 1) default).key.ds (ctx.hiAt (ns.getD (o - 1) default).anc.length)
      (ns.getD (o - 1) default).grp)
    {dsa : List AnnotTerm}
    (hdsa : DenoteMetaSpine mk.base2.acval envI ψ (ctx.hiAt prog.length) hk.key.ds dsa)
    (hfr : keyFrame dsa (ctx.hiAt prog.length) (trueVal mpC ctx ψ ρ xs prog)
      = nlFr mpC ctx d ns ψ ρ xs o) {is : List V}
    (hfit : SpineFit (nlFr mpC ctx d ns ψ ρ xs o)
      ((nlDb mpC d ns o).ids (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is) :
    nlComp mpC d ns o hk.key.cname < (nlDb mpC d ns o).N ∧
    (dsa.map (interp V (trueVal mpC ctx ψ ρ xs prog)) ++ is).foldl app
        (trueVal mpC ctx ψ ρ xs prog (ctx.hiAt prog.length - 1 - (ctx.hiAt 0 + i)))
      = app ((nlDb mpC d ns o).carrier (nlψ envC ns ψ o) (nlFr mpC ctx d ns ψ ρ xs o)
          (nlComp mpC d ns o hk.key.cname))
        (tupW ((nlDb mpC d ns o).u (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is) := by
  have hfrU := dyn_nlFr H ho hu ψ ρ xs
  unfold nlComp at hfit ⊢
  rw [show nlDb mpC d ns o = lfpSel mpC d.toLfp (ns.getD (o - 1) default).key.cname by
      unfold nlDb; rw [if_neg ho],
    show nlψ envC ns ψ o = nodeψ envC ψ (ns.getD (o - 1) default) by
      unfold nlψ; rw [if_neg ho]] at hfit ⊢
  rw [← hfr] at hfit ⊢
  rw [hfrU] at hfr
  generalize ns.getD (o - 1) default = u at hu hk_mem hfr hfrU hfit ⊢
  obtain ⟨hD, hwid, hnN, hkN, -, mm, hmm, hmmH, cv, caps, hfc, hlps, hlpsOf, -, hul, hlenP, -, hg⟩ :=
    dyn_nodeBlock H hu
  generalize lfpSel mpC d.toLfp u.key.cname = D at *
  have hψ : nodeψ envC ψ u = Level.substFn ψ cv.levelParams u.key.lvls := by
    unfold nodeψ; rw [hlpsOf]
  rw [hψ] at hfit ⊢
  -- the hole's member of `D`
  simp only [ConLeche.grpNews, List.mem_map] at hk_mem
  obtain ⟨p, hp, rfl⟩ := hk_mem
  obtain ⟨mm', hmm', hpm⟩ := (hg.2 p hp).1
  simp only at hfit ⊢ hdsa hi
  rw [hpm, idxOf_member hnN hkN hmm'] at hfit ⊢
  refine ⟨hwid ▸ hmm', ?_⟩
  obtain ⟨cv', caps', hf', hl'⟩ := hlps mm' hmm'
  have hlen : u.key.lvls.length = cv'.levelParams.length := by rw [hl', hul]
  rw [trueVal_frame mpC ctx ψ ρ xs (by rw [H.hnP]; exact hxs) prog hi]
  simp only
  rw [hpm, dyn_constRead H hf' hlen, hl', ← H.hag _ (by rw [hf']; rfl)]
  -- the leaf at the owner's true frame
  have hkf : keyFrame dsa (ctx.hiAt prog.length) (trueVal mpC ctx ψ ρ xs prog)
      = consList (dsa.map (interp V (trueVal mpC ctx ψ ρ xs prog)))
          (fun j => trueVal mpC ctx ψ ρ xs prog (j + ctx.hiAt prog.length)) := rfl
  rw [hkf] at hfit ⊢
  have hsat := nodeKeyFit mk (H.hΔ0 ψ) (H.hok u hu) (H.hsem u hu ψ) hD hmm hmmH hfc
    (hlenP _).symm (dyn_dsaI H hu ψ) _ (dyn_trueVal_sat H ψ ρ xs hparams u.anc (dyn_stackFound H hu))
  rw [← hfr, hkf] at hsat
  have hSP := spineFit_of_sat_consList (by
    rw [List.length_map, ← DenoteMetaSpine.length_eq hdsa, hlenP]) hsat
  rw [acval_interp_closed mpC.base2 _ _ ρ
    (fun j => trueVal mpC ctx ψ ρ xs prog (j + ctx.hiAt prog.length))]
  exact (mpC.lfpClause_of_mem (H.hsub D hD)).leaf mm' hmm' _ _ _ is hSP hfit

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
    · rw [if_pos ⟨hin, hqb⟩]
      rw [List.getElem?_append_left (by simpa using hin)] at hi
      obtain ⟨h1, h2, h3, h4, X, hX⟩ := dyn_holeOwner H hPP f (par b) (by omega) hq0 (by omega) i hk
        (by rw [hpb]; exact hi)
      rw [hpb] at h4 hX
      refine ⟨h1, h2, h3, Nat.lt_trans hlt h4,
        (ConLeche.grpNews p.key.lvls p.key.ds (ctx.hiAt p.anc.length) p.grp).reverse ++ X, ?_⟩
      rw [hta, hX]
      simp only [List.append_assoc]
    · rw [if_neg (fun h => hin h.1), hpb]
      rw [List.getElem?_append_right (by simpa using hin)] at hi
      exact ⟨hq0, by omega, List.mem_of_getElem? hi, hlt, [], by rw [hta, List.nil_append]⟩

/-- **`top`**: the TRUE frame is admissible once the shallower nodes' true
elements satisfy `G` — node `0` by definition; a derived node at the true
valuation of its frames, whose member holes at the block's parameters are
node `0`'s true carrier and whose frame holes at their keys are their
(shallower) owners' true carriers (`leaf`). -/
theorem dyn_top (H : DynCtx F mk mpC ctx d ns) (ψ : Name → Nat) (ρ : Nat → V) (xs : List V)
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) (hxs : d.nP ≤ xs.length)
    {par : Nat → Nat} (hPP : ParentPtrs ns par) :
    ∀ b, b < ns.length + 1 → ∀ G : Nat → Nat → V → V → Prop,
      (∀ b' c t y, b' < ns.length + 1 → nlDp ns b' < nlDp ns b → c < (nlDb mpC d ns b').N →
        t ∈ˢ (nlDb mpC d ns b').idx (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c →
        y ∈ˢ app ((nlDb mpC d ns b').carrier (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c) t →
        G b' c t y) →
      nodeAdm mk mpC ctx d ns ψ ρ xs par b G (nlFr mpC ctx d ns ψ ρ xs b) := by
  intro b hb G hG
  unfold nodeAdm
  by_cases hb0 : b = 0
  · rw [if_pos hb0]; subst hb0; rfl
  rw [if_neg hb0]
  have ht := getD_mem_of_lt (ns := ns) (b := b) (by omega) (by omega)
  refine ⟨_, ?_, dyn_nlFr H hb0 ht ψ ρ xs⟩
  have hdpb : nlDp ns b = nlDd ns - (ns.getD (b - 1) default).height := by
    unfold nlDp; rw [if_neg hb0]
  have hdd := height_le_nlDd ht
  have hown := dyn_holeOwner H hPP (b + 1) b (by omega) (by omega) (by omega)
  unfold holeOwner
  generalize ns.getD (b - 1) default = t at ht hdpb hdd hown ⊢
  refine ⟨dyn_trueVal_sat H ψ ρ xs hparams t.anc (dyn_stackFound H ht), fun _ _ => rfl,
    fun t' ht' as has y hy => ⟨fun hP hfit => ?_, fun _ => hy⟩, fun i hk hi => ?_⟩
  · -- a member hole at the block's parameters: node `0`'s true carrier
    have has' : as = xs.take ctx.nP ++ as.drop ctx.nP := by rw [← hP, List.take_append_drop]
    rw [has', dyn_memberLeaf H ψ ρ xs hparams hxs t.anc ht' hfit] at hy
    have hkN := lfp_namesLen mpC H.hd0
    have htk : t' < d.toLfp.k := by rw [← hkN, ← H.hnames]; exact ht'
    have h0 : nlDp ns 0 = 0 := by unfold nlDp; rw [if_pos rfl]
    refine hG 0 t' _ y (by omega) (by rw [h0, hdpb]; have := PosTree.height_pos t; omega)
      ?_ ?_ ?_
    · show t' < d.toLfp.N
      exact Nat.lt_of_lt_of_le htk (mpC.lfpClause_of_mem H.hd0).kN
    · simp only [nlDb, nlψ, nlFr, if_pos]
      rw [← H.hnP]
      exact tupW_mem hfit
    · simp only [nlDb, nlψ, nlFr, if_pos]
      exact hy
  · -- a frame hole: its owner's true carrier
    obtain ⟨ho0, hol, hmem, hlt, X, hX⟩ := hown i hk hi
    generalize hoe : holeOwnerF ns par (b + 1) b i = o at ho0 hol hmem hlt hX ⊢
    have ho : o ≠ 0 := by omega
    have hu' : ns.getD (o - 1) default ∈ ns := getD_mem_of_lt ho0 hol
    have hou : ns.getD (o - 1) default = ns.getD (o - 1) default := rfl
    have hud := height_le_nlDd hu'
    refine ⟨ho0, hol, hmem, fun dsa hdsa => ?_⟩
    have hfr := dyn_ownerFrame H ψ ρ xs ho hu' hX hmem hdsa
    refine ⟨hfr, fun is _ y hy => ⟨fun hfit => ?_, fun _ => hy⟩⟩
    obtain ⟨hmo, heq⟩ := dyn_ownerLeaf H ψ ρ xs hparams hxs ho hu' hi hmem hdsa hfr hfit
    rw [heq] at hy
    refine hG _ _ _ y (by omega) ?_ hmo (tupW_mem hfit) hy
    rw [hdpb]
    unfold nlDp
    rw [if_neg ho]
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
      y ∈ˢ app ((nlDb mpC d ns b').carrier (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c) t)
    {t : PosTree} (ht : t ∈ ns) :
    HoleRel mk.base2 ψ ctx t.anc (ctx.hiAt t.anc.length)
      (stackCtx mk.base2 ψ ctx t.anc (d.holeCtx ψ).reverse)
      (fun σ₁ σ₂ => AdmVal mk mpC ctx d ns ψ ρ xs own G t.anc σ₁ ∧
        σ₂ = trueVal mpC ctx ψ ρ xs t.anc) where
  dom := by
    rintro σ₁ σ₂ ⟨hA, rfl⟩
    exact ⟨hA.sat, dyn_trueVal_sat H ψ ρ xs hparams t.anc (dyn_stackFound H ht)⟩
  agree := by
    rintro σ₁ σ₂ ⟨hA, rfl⟩
    exact hA.agree
  member := by
    rintro t' ht' σ₁ σ₂ ⟨hA, rfl⟩ as has y hy
    obtain ⟨g1, g2⟩ := hA.member t' ht' as has y hy
    by_cases hc : as.take ctx.nP = xs.take ctx.nP ∧
        SpineFit (consList (xs.take ctx.nP) ρ) (d.toLfp.ids t' ψ) (as.drop ctx.nP)
    · have hy' := hG _ _ _ _ (g1 hc.1 hc.2)
      simp only [nlDb, nlψ, nlFr, if_pos] at hy'
      have has' : as = xs.take ctx.nP ++ as.drop ctx.nP := by rw [← hc.1, List.take_append_drop]
      rw [has', dyn_memberLeaf H ψ ρ xs hparams hxs t.anc ht' hc.2]
      exact hy'
    · exact g2 hc
  frame := by
    rintro i hk hki dsa hsp ni har σ₁ σ₂ ⟨hA, rfl⟩ is his y hy
    obtain ⟨ho0, hol, hmem, hrest⟩ := hA.frame i hk hki
    generalize own i = o at ho0 hol hmem hrest
    obtain ⟨hfr, hrest2⟩ := hrest dsa hsp
    obtain ⟨g1, g2⟩ := hrest2 is (by omega) y hy
    by_cases hfit : SpineFit (nlFr mpC ctx d ns ψ ρ xs o)
        ((nlDb mpC d ns o).ids (nlComp mpC d ns o hk.key.cname) (nlψ envC ns ψ o)) is
    · rw [(dyn_ownerLeaf H ψ ρ xs hparams hxs (by omega)
        (getD_mem_of_lt (ns := ns) (b := o) ho0 hol) hki hmem hsp hfr hfit).2]
      exact hG _ _ _ _ (g1 hfit)
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
          ((nlDb mpC d ns b').idx (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b'))).carrier
          (nlFr mpC ctx d ns ψ ρ xs b') c) t) →
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
  have hG' : ∀ b' c t y, G b' c t y →
      y ∈ˢ app ((nlDb mpC d ns b').carrier (nlψ envC ns ψ b') (nlFr mpC ctx d ns ψ ρ xs b') c) t :=
    fun b' c t y h => by have := hG b' c t y h; rwa [lfpSClause_carrier rfl] at this
  have hsat := dyn_hAdm H ψ ρ xs hparams par b hb G ρ' hadm
  unfold nodeAdm at hadm
  by_cases hb0 : b = 0
  · rw [if_pos hb0] at hadm
    subst hb0
    subst hadm
    have hcl : LfpClause mpC.base2.acval (nlDb mpC d ns 0) := by
      simp only [nlDb, if_pos]; exact mpC.lfpClause_of_mem H.hd0
    exact lfp_trans_self hcl hsat.1 hY hle hc hf
  rw [if_neg hb0] at hadm
  obtain ⟨σ, hσ, rfl⟩ := hadm
  have ht := getD_mem_of_lt (ns := ns) (b := b) (by omega) (by omega)
  have hsat' := hsat
  rw [dyn_nlFr H hb0 ht ψ ρ xs] at hY hle hsat' ⊢
  have e1 : nlDb mpC d ns b = lfpSel mpC d.toLfp (ns.getD (b - 1) default).key.cname := by
    unfold nlDb; rw [if_neg hb0]
  have e2 : nlψ envC ns ψ b = nodeψ envC ψ (ns.getD (b - 1) default) := by
    unfold nlψ; rw [if_neg hb0]
  rw [e1, e2] at hY hle hf hsat' ⊢
  rw [e1] at hc
  generalize ns.getD (b - 1) default = u at ht hσ hY hle hc hf hsat' ⊢
  obtain ⟨hD, hwid, hnN, hkN, hall, mm, hmm, hmmH, cv, caps, hfc, hlps, hlpsOf, hndl, hul, hlenP,
    hnL, hg⟩ := dyn_nodeBlock H ht
  generalize lfpSel mpC d.toLfp u.key.cname = D at *
  have hψ : nodeψ envC ψ u = Level.substFn ψ cv.levelParams u.key.lvls := by
    unfold nodeψ; rw [hlpsOf]
  rw [hψ] at hY hle hf hsat' ⊢
  -- the frame's monotonicity at the node's own derivation
  have hR := dyn_holeRel H ψ ρ xs hparams hxs (holeOwner ns par b) hG' ht
  have hmono : FrameMono mk ψ ctx u.anc u.key.lvls u.key.ds u.grp :=
    posD_mono mk (Rules.RulesInputs.ofSem mk ψ) (H.hok u ht).1
  have hdsa := dyn_dsaI H ht ψ
  obtain ⟨-, -, -, hconcl⟩ := hmono H.hcov hD hmm hmmH hlps hul (posNodeOk_dsAnc (H.hok u ht))
    hdsa (hlenP _) hnL hR (stackCtx_length_hi (H.hΔ0 ψ) _) (H.hsem u ht ψ).2.1 (H.hsem u ht ψ).2.2
    (fun σ₁ σ₂ h => ⟨nodeKeyFit mk (H.hΔ0 ψ) (H.hok u ht) (H.hsem u ht ψ) hD hmm hmmH hfc
        (hlenP _).symm hdsa σ₁ (hR.dom σ₁ σ₂ h).1,
      nodeKeyFit mk (H.hΔ0 ψ) (H.hok u ht) (H.hsem u ht ψ) hD hmm hmmH hfc
        (hlenP _).symm hdsa σ₂ (hR.dom σ₁ σ₂ h).2⟩)
  refine trans_of_frameConcl (mk.lfpClause_of_mem hD) hwid hall
    (hconcl σ (trueVal mpC ctx ψ ρ xs u.anc) ⟨hσ, rfl⟩) hsat'.1 ?_ hY hle hc hf
  intro c' hc'
  rw [hwid] at hc'
  exact grp_idx_eq mk hD hnN hkN H.hcov.find hlps hndl hul (posNodeOk_dsAnc (H.hok u ht)) hdsa
    (hlenP _) hg (hall c' hc') hσ.agree

end Frames

/-! ## The dynamic part's context -/

/-- **The dynamic part's context from the stage's** (`nestedClassNodes`'
node context). -/
theorem dynCtx_of {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {nodesR : ConLeche.NestNodes}
    (hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      nodesR)
    {mk : EnvModelM V μ envI} (hmkC : LfpCover mk pp.toBlockShape.memberNames)
    (hmk : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks)
    (hag : ∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n)
    (hsubC : ∀ D ∈ mpC.lfpBlocks, D = dR.toLfp ∨ D ∈ mk.lfpBlocks)
    (htr : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mk.base2.acval envI ψ dd e = some ea →
        denoteMeta mpC.base2.acval envC ψ dd e = some ea)
    (hcoreK : BlockHoleCtxFacts mk.base2 dR pp.lps cvTasR pp.toBlockShape isRecR)
    {fvsP : List Expr} {ns : List PosTree}
    (hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t)
    (hown : ∀ t ∈ ns, NodeOwned (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t)
    (hkids : ∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns)
    (hpar : ∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids)
    (hsem : ∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ (pp.nestCtx fvsP envI.find? envI.consts)
      (dR.holeCtx ψ).reverse t)
    (hF : NodeListFacts mpC (pp.nestCtx fvsP envI.find? envI.consts) ns) :
    DynCtx F mk mpC (pp.nestCtx fvsP envI.find? envI.consts) dR ns := by
  obtain ⟨-, hPos, henvC, -, -, hN, hS, -, -, hdR, hlfp, hcovC, -, -⟩ := hctx
  obtain ⟨cvTa0, -, -, -, h0, -⟩ := ConLeche.checkBlockPositivity_inv_gen hPos
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hkN := lfp_namesLen mpC hlfp
  refine ⟨hcovC, hlfp, contCover_of hmkC (fun _ => rfl) rfl, hmk, hag, hsubC, htr,
    ⟨pp.nP, ctorsAsR, henvC⟩, hok, hown, hkids, hpar, hsem, hF, rfl, rfl, fun ψ => ?_,
    fun n hn => ?_, ⟨cvTasR, pp.toBlockShape, isRecR, hN, hcoreK.1⟩⟩
  · -- the hole context: the parameters, then one hole per member
    have h0' : cvTasR[0]? = some cvTa0 := by rw [List.head?_eq_getElem?] at h0; exact h0
    obtain ⟨-, hFD0⟩ := hcoreK.1 0 cvTa0 h0'
    rw [List.length_reverse, BlockData.holeCtx, List.length_append, List.length_map,
      List.length_range, BlockData.params, List.length_map, List.length_take, hFD0.len ψ]
    show min _ _ + _ = pp.nP + pp.memberNames.length + 0
    have : (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).k = pp.memberNames.length := by
      simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
        ConLeche.BlockShape.memberNames]
    rw [this]
    have : (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).nP = pp.nP := rfl
    rw [this]
    omega
  · -- the members are stored at the block's level parameters
    change n ∈ pp.toBlockShape.memberNames at hn
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hn
    have hck : c < (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).k := by
      change c < pp.toBlockShape.members.length
      simpa [ConLeche.BlockShape.memberNames] using hc
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTasR[c]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hck)⟩
    have hname := hN.1 c cvTb hcvb
    obtain ⟨hf, -⟩ := hcoreK.1 c cvTb hcvb
    rw [← hname] at hf
    unfold BlockData.memberName at hf
    change envI.find? (pp.toBlockShape.memberNames.getD c .anonymous) = _ at hf
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at hf
    exact ⟨_, _, hf, hS.lpsT c cvTb hck hcvb⟩

end ConLeche.Model
