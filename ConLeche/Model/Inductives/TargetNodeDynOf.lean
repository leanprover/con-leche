module

public import ConLeche.Model.Inductives.TargetNodeAdm
public import ConLeche.Model.Inductives.TargetGuardParams
import ConLeche.Model.Inductives.ContSem
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Model.Annot.BitInst
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.PosDerivNodes
import ConLeche.Model.Inductives.TargetClass
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Model.Inductives.BlockHoleGrade
import ConLeche.Model.Inductives.BlockRecTyShapeRun
import ConLeche.Verify.Level
import ConLeche.Model.Inductives.StructRecKit2
import ConLeche.Model.Inductives.ContLeaf

public section

/-!
# The node presentation's dynamic part: `hAdm`, `top`, `trans` (lane NESTIND, session 23)

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

/-- A read spine is its terms' readings. -/
theorem DenoteMetaSpine.getD_eq {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} {d : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ d as vs →
      as.map (fun x => (denoteMeta acval env φ d x).getD default) = vs
  | _, _, .nil => rfl
  | _, _, .cons ha hs => by
    rw [List.map_cons, ha, Option.getD_some, DenoteMetaSpine.getD_eq hs]

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

/-- **What the dynamic part reads** (`NestedNodeDynOwed`'s hypotheses,
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
as its members, every member in the frame's group (N2-eager), the group's
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
  -- the group's names are the block's (N2-eager)
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
    (hparams : SpineFit ρ (d.params ψ) (xs.take d.nP)) :
    ∀ b, b < ns.length + 1 → ∀ G ρ', nodeAdm mk mpC ctx d ns ψ ρ xs b G ρ' →
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

end Frames

end ConLeche.Model
