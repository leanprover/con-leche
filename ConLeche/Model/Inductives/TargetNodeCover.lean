module

public import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Semantics.Inductives.DeclBlockEta
import ConLeche.Model.Inductives.TargetNodeAdm
import ConLeche.Model.Inductives.TargetCallEntry
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Verify.Inductives.HoleImg

public section

/-!
# The node list at a nested stage, and its coverage

The coverage theorem (`outsideClass_reachedNode`,
`PosDerivTie.lean`) gives every OUTSIDE recursor class a reached node of
SOME member constructor's (or seed's) derivation forest — a node
(`PosNodeOk`) whose key read back the class matches (`NodeMajor`).  There is no single
shared forest (each class comes with its own constructor derivation), so
the node list is indexed by the classes: node `c` is the chosen node of
outside class `c` (`nestedRecCtx_nodes`).  Every listed node is a
`PosNodeOk` node of the walk's context, and the list covers every outside
class — `NodeListCover` at every prefix spine, unguarded.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level NestCtx PosTree TargetMajor ConstantVal
  ConstantInfo BlockShape fueledOps PosNodeOk)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## The node facts a `PosNodeOk` node carries -/

/-- **A node's group lies in one recorded block** with its key's container:
the frame's head is a covered container (not a member, not `Quot`,
stored), its block's names are `nestBlockOf` of the head, and the rest of
the group lies there. -/
theorem posNodeOk_blk {env : Env} {mk : EnvModelM V μ env} {ctx : NestCtx}
    {ops : ConLeche.CheckerOps ConLeche.CheckM} (hcov : ContCover mk ctx) {t : PosTree}
    (hok : PosNodeOk ops env ctx t) :
    ∀ n ∈ t.grp.map (·.1), ∃ D ∈ mk.lfpBlocks, t.key.cname ∈ D.names ∧ n ∈ D.names := by
  obtain ⟨hfr, hcn, -⟩ := hok
  obtain ⟨hne, ⟨hhdN, hhdQ⟩, -, hinst, hblk⟩ := posD_frame_inv hfr
  obtain ⟨p₀, ps, hgrp⟩ := List.exists_cons_of_ne_nil hne
  rw [hgrp] at hinst hblk hhdN hhdQ
  simp only [List.headD_cons, List.tail_cons] at hinst hblk hhdN hhdQ
  obtain ⟨nI, hrun⟩ := hinst p₀ List.mem_cons_self
  obtain ⟨cvC, caps, hfC, -⟩ := ConLeche.nestInstType_inv hrun
  have hfC' : env.find? p₀.1 = some (.indInfo cvC caps) := by rw [← hcov.find]; exact hfC
  obtain ⟨D, hD, mm, hmm, hmem⟩ := hcov.cover p₀.1 cvC caps hfC' hhdN hhdQ
  have hblkD := hcov.block D hD
  have hkN := lfp_namesLen mk hD
  have hall : ConLeche.nestBlockOf ctx p₀.1 = D.names := by
    unfold ConLeche.nestBlockOf
    rw [hfC]
    exact hblkD.all mm hmm cvC caps (by rw [hmem]; exact hfC')
  have hin : ∀ n ∈ t.grp.map (·.1), n ∈ D.names := by
    intro n hn
    rw [hgrp] at hn
    rcases List.mem_cons.mp hn with rfl | hn
    · show p₀.1 ∈ D.names
      rw [← hmem]
      unfold LfpDatum.member
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega), Option.getD_some]
      exact List.getElem_mem _
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
      have := hblk p hp
      rw [hall, List.contains_iff_mem] at this
      exact this
  exact fun n hn => ⟨D, hD, hin _ hcn, hin n hn⟩

/-- **A node's key parameters are scoped at its stack's depth.** -/
theorem posNodeOk_ws {env : Env} {ctx : NestCtx} {ops : ConLeche.CheckerOps ConLeche.CheckM}
    {t : PosTree} (hok : PosNodeOk ops env ctx t) :
    ∀ x ∈ t.key.ds, Expr.WScoped (ctx.hiAt t.occ.length) x :=
  fun x hx => (hok.2.2.2.2.1 x hx).1

omit [SetTheory V] in
/-- A name of a recorded block is one of its members. -/
theorem exists_member_of_mem_names {D : LfpDatum V} (hkN : D.names.length = D.k) {n : Name}
    (h : n ∈ D.names) : ∃ i, i < D.k ∧ D.member i = n := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem h
  refine ⟨i, hkN ▸ hi, ?_⟩
  unfold LfpDatum.member
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]

/-- **A recorded block of the formers' model, read at the constructors'
environment**: every member is stored there as at `envI` (the
constructors' conses add constructors only), all at one level-parameter
list (`contBlock_facts`). -/
theorem blk_lps_envC {envI envC : Env} {mk : EnvModelM V μ envI} {mpC : EnvModelM V μ envC}
    {ctx : NestCtx} (hcov : ContCover mk ctx) (hsub : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks)
    {nP : Nat} {ctorsAs : List (List (ConstantVal × Nat))}
    (henvC : envC = ConLeche.consBlockCtors nP ctorsAs envI) {D : LfpDatum V}
    (hD : D ∈ mk.lfpBlocks) :
    ∃ lps : List Name, ∀ i, i < D.k → ∃ cv caps,
      envC.find? (D.member i) = some (.indInfo cv caps) ∧
      envI.find? (D.member i) = some (.indInfo cv caps) ∧ cv.levelParams = lps := by
  subst henvC
  by_cases hk : D.k = 0
  · exact ⟨[], fun i hi => absurd hi (by omega)⟩
  obtain ⟨cv0, caps0, hf0⟩ := (mpC.lfp_ok D (hsub D hD)).2.1.1 0 (by omega)
  have hf0I := ConLeche.Semantics.consBlockCtors_find?_indInfo hf0
  obtain ⟨nPc, L, hq⟩ := nestContainer_of_find (ctx := ctx) (by rw [hcov.find]; exact hf0I)
  obtain ⟨lps, hlps, -⟩ := contBlock_facts mk hcov hD (by omega : 0 < D.k) hf0I hq
  refine ⟨lps, fun i hi => ?_⟩
  obtain ⟨cv, caps, hf⟩ := (mpC.lfp_ok D (hsub D hD)).2.1.1 i hi
  have hfI := ConLeche.Semantics.consBlockCtors_find?_indInfo hf
  obtain ⟨cv', caps', hf', hl'⟩ := hlps i hi
  rw [hfI] at hf'
  obtain ⟨rfl, rfl⟩ : cv = cv' ∧ caps = caps' := by simpa using hf'
  exact ⟨cv, caps, hf, hfI, hl'⟩

/-- **A node's group shares the container's level parameters** at the
constructors' environment (`NodeListFacts.lps`). -/
theorem posNodeOk_lps {envI envC : Env} {mk : EnvModelM V μ envI} {mpC : EnvModelM V μ envC}
    {ctx : NestCtx} {ops : ConLeche.CheckerOps ConLeche.CheckM} (hcov : ContCover mk ctx)
    (hsub : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks) {nP : Nat}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (henvC : envC = ConLeche.consBlockCtors nP ctorsAs envI) {t : PosTree}
    (hok : PosNodeOk ops envI ctx t) :
    ∀ n ∈ t.grp.map (·.1), lpsOf envC t.key.cname = lpsOf envC n := by
  intro n hn
  obtain ⟨D, hD, h1, h2⟩ := posNodeOk_blk hcov hok n hn
  obtain ⟨lps, hl⟩ := blk_lps_envC hcov hsub henvC hD
  have hkN := lfp_namesLen mk hD
  obtain ⟨i, hi, hi1⟩ := exists_member_of_mem_names hkN h1
  obtain ⟨i', hi', hi2⟩ := exists_member_of_mem_names hkN h2
  obtain ⟨cv, caps, hf, -, hlp⟩ := hl i hi
  obtain ⟨cv', caps', hf', -, hlp'⟩ := hl i' hi'
  rw [hi1] at hf
  rw [hi2] at hf'
  unfold lpsOf
  rw [hf, hf']
  exact hlp.trans hlp'.symm

/-- **The block's own holes are read**: a member hole's read-back is the
member at the block's levels applied to the canonical parameters. -/
theorem nodeHolesRead_nil {envC : Env} {mpC : EnvModelM V μ envC} {ctx : NestCtx}
    (hparF : ctx.params.length = ctx.nP ∧ ∀ (i : Nat) (x : Expr), ctx.params[i]? = some x →
      ∃ ty, x = .fvar i ty)
    (hparS : ∀ x ∈ ctx.params, ConLeche.ScB ctx.nP x)
    (hmem : ∀ n ∈ ctx.names, ∃ ci, envC.find? n = some ci ∧
      ctx.lps.length = ci.toConstantVal.levelParams.length) :
    NodeHolesRead mpC.base2.acval envC ctx [] := by
  refine ⟨hparS, trivial, fun ψ dd _ i hi => ?_⟩
  unfold nodeImg
  split
  · exact ⟨_, denoteMeta_fvar _ _ _ _⟩
  · rename_i hlt
    have ht : i - ctx.nP < ctx.names.length := by
      simp only [ConLeche.NestCtx.hiAt, List.length_nil] at hi; omega
    simp only [ConLeche.nestHoleImg]
    rw [ite_eq_left ⟨by omega, by simpa using hi⟩, Option.getD_some]
    have hn : ctx.names.getD (i - ctx.nP) .anonymous ∈ ctx.names := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
      exact List.getElem_mem _
    obtain ⟨ci, hf, hl⟩ := hmem _ hn
    have hc := denoteMeta_const (acval := mpC.base2.acval) (φ := ψ) (d := dd) hf
      (show (ctx.lps.map Level.param).length = ci.toConstantVal.levelParams.length by
        rw [List.length_map]; exact hl)
    have hsp := denoteMetaSpine_fvars (acval := mpC.base2.acval) (env := envC) (φ := ψ)
      dd ctx.params 0 (fun i x hx => by simpa using hparF.2 i x hx)
    exact ⟨_, denoteMeta_mkAppN hsp hc⟩

omit [SetTheory V] in
theorem progScB_append {ctx : NestCtx} {A : List NestHole} (hA : ConLeche.ProgScB ctx A) :
    ∀ (G : List NestHole), (∀ h ∈ G, ∀ x ∈ h.key.ds, ConLeche.ScB (ctx.hiAt A.length) x) →
      ConLeche.ProgScB ctx (G ++ A)
  | [], _ => hA
  | h :: G, hG => by
    refine ⟨fun x hx => ?_, progScB_append hA G fun h' hh' => hG h' (List.mem_cons_of_mem _ hh')⟩
    exact ConLeche.ScB.mono
      (by simp only [ConLeche.NestCtx.hiAt, List.append_eq, List.length_append]; omega)
      (hG h List.mem_cons_self x hx)

omit [SetTheory V] in
/-- **A read spine read shallower**: a spine scoped at `p` that reads at a
depth `D ≥ p` reads at `p` (`denoteMeta_lift`, argument by argument). -/
theorem denoteMetaSpine_lower {acval : Name → (Name → Nat) → AnnotTerm} {env : Env}
    {φ : Name → Nat} (hacl : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
      (acval n ψ).liftN 1 k = acval n ψ) {D p : Nat} :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval env φ D as vs →
      (∀ x ∈ as, Expr.WScoped p x) → p ≤ D → ∃ ws, DenoteMetaSpine acval env φ p as ws
  | _, _, .nil, _, _ => ⟨[], .nil⟩
  | a :: _, _, .cons ha hs, hw, hpD => by
    obtain ⟨ws, hws⟩ := denoteMetaSpine_lower hacl hs
      (fun x hx => hw x (List.mem_cons_of_mem _ hx)) hpD
    rw [denoteMeta_lift hacl (hw a List.mem_cons_self) _ hpD] at ha
    obtain ⟨w, hw', -⟩ := Option.map_eq_some_iff.mp ha
    exact ⟨w :: ws, .cons hw' hws⟩

/-- **A node's group on top of its read frames is read**: a new hole's
read-back is its container applied to the key read back, which reads where
the key does (`readback_spine`, at the node's own stack, of which the
frames' `anc` is a suffix). -/
theorem nodeHolesRead_grp' {envI envC : Env} {mpC : EnvModelM V μ envC} {ctx : NestCtx}
    {ops : ConLeche.CheckerOps ConLeche.CheckM} {u : PosTree} (hok : PosNodeOk ops envI ctx u)
    (hrdA : NodeHolesRead mpC.base2.acval envC ctx u.anc)
    (hsp : ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
      (ctx.hiAt u.anc.length) u.key.ds dsa)
    (hfind : ∀ p ∈ u.grp, ∃ ci, envC.find? p.1 = some ci ∧
      u.key.lvls.length = ci.toConstantVal.levelParams.length) :
    NodeHolesRead mpC.base2.acval envC ctx
      ((ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp).reverse ++ u.anc) := by
  have hds := posNodeOk_dsAnc hok
  generalize hG : ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp = G
  have hGd : ∀ h ∈ G, h.key.ds = u.key.ds ∧ h.key.lvls = u.key.lvls ∧
      ∃ p ∈ u.grp, h.key.cname = p.1 := by
    intro h hh
    rw [← hG] at hh
    simp only [ConLeche.grpNews, List.mem_map] at hh
    obtain ⟨p, hp, rfl⟩ := hh
    exact ⟨rfl, rfl, p, hp, rfl⟩
  refine ⟨hrdA.1, progScB_append hrdA.2.1 _ fun h hh x hx => ?_, fun ψ dd hd i hi => ?_⟩
  · rw [(hGd h (List.mem_reverse.mp hh)).1] at hx
    exact hds x hx
  by_cases hia : i < ctx.hiAt u.anc.length
  · rw [nodeImg_suffix ctx G.reverse u.anc hia]
    exact hrdA.2.2 ψ dd hd i hia
  -- a new hole: its container applied to the key read back
  obtain ⟨j, rfl⟩ : ∃ j, i = ctx.hiAt (u.anc.length + j) :=
    ⟨i - ctx.hiAt u.anc.length, by simp only [ConLeche.NestCtx.hiAt] at hia ⊢; omega⟩
  have hj : j < G.length := by
    simp only [ConLeche.NestCtx.hiAt, List.length_append, List.length_reverse] at hi; omega
  have hrev : (G.reverse ++ u.anc).reverse[u.anc.length + j]? = some G[j] := by
    rw [List.reverse_append, List.reverse_reverse, List.getElem?_append_right (by simp),
      List.length_reverse, show u.anc.length + j - u.anc.length = j by omega,
      List.getElem?_eq_getElem hj]
  have hfi := ConLeche.nestHoleImg_frame (ctx := ctx) hrev
  obtain ⟨hdsE, hlvE, p, hp, hcn⟩ := hGd G[j] (List.getElem_mem hj)
  have himg : nodeImg ctx (G.reverse ++ u.anc) (ctx.hiAt (u.anc.length + j))
      = Expr.mkAppN (.const p.1 u.key.lvls) (u.key.ds.map (nodeRb ctx u.anc)) := by
    unfold nodeImg
    rw [ite_eq_right (by simp only [ConLeche.NestCtx.hiAt]; omega), hfi, Option.getD_some, hdsE, hlvE,
      hcn]
    congr 1
    have hdrop : (G.reverse ++ u.anc).drop ((G.reverse ++ u.anc).length - (u.anc.length + j))
        = (G.reverse).drop (G.length - j) ++ u.anc := by
      rw [List.drop_append_of_le_length (by simp)]
      congr 2; simp; omega
    rw [hdrop]
    refine List.map_congr_left fun x hx => ?_
    unfold nodeRb
    exact replaceFVars_congr_below (fun v hv => ConLeche.nestHoleImg_suffix _ u.anc hv) x
      (hds x hx).1.fvarsBelow
  rw [himg]
  obtain ⟨dsa, hdsa⟩ := hsp ψ
  obtain ⟨ebs, hebs, -⟩ := readback_spine mpC.base2 (hrdA.hs ψ hd) (fun _ => pt)
    (fun x hx => (hds x hx).1) hdsa
  obtain ⟨ci, hf, hl⟩ := hfind p hp
  exact ⟨_, denoteMeta_mkAppN hebs (denoteMeta_const hf hl)⟩

/-- **A node's stack holes are read** (`NodeListFacts.read`): by induction
along the parents, each node's stack is its parent's group on top of the
parent's frames (`nodeHolesRead_grp'`), the block's own holes at the bottom
(`nodeHolesRead_nil`). -/
theorem nodeHolesRead_of {envI envC : Env} {mpC : EnvModelM V μ envC} {ctx : NestCtx}
    {ops : ConLeche.CheckerOps ConLeche.CheckM} {ns : List PosTree}
    (hok : ∀ t ∈ ns, PosNodeOk ops envI ctx t)
    (hpar : ∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids)
    (hnil : NodeHolesRead mpC.base2.acval envC ctx [])
    (hsp : ∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
      (ctx.hiAt t.occ.length) t.key.ds dsa)
    (hfind : ∀ t ∈ ns, ∀ p ∈ t.grp, ∃ ci, envC.find? p.1 = some ci ∧
      t.key.lvls.length = ci.toConstantVal.levelParams.length) :
    ∀ t ∈ ns, NodeHolesRead mpC.base2.acval envC ctx t.occ := by
  have key : ∀ (n : Nat) (t : PosTree), t ∈ ns → t.occ.length ≤ n →
      NodeHolesRead mpC.base2.acval envC ctx t.occ := by
    intro n
    induction n with
    | zero =>
      intro t _ hn
      rw [List.length_eq_zero_iff.mp (by omega : t.occ.length = 0)]
      exact hnil
    | succ n ih =>
      intro t ht hn
      by_cases h0 : t.occ = []
      · rw [h0]; exact hnil
      obtain ⟨u, hu, htu⟩ := hpar t ht h0
      have hocc := (hok u hu).2.2.1 t htu
      obtain ⟨hne, -, -, -, -⟩ := posD_frame_inv (hok u hu).1
      have hgl : 0 < u.grp.length := List.length_pos_iff.mpr hne
      have hanc : NodeHolesRead mpC.base2.acval envC ctx u.anc := by
        obtain ⟨-, -, -, -, -, hanc⟩ := hok u hu
        rcases hanc with ⟨hao, -⟩ | ⟨han, -⟩
        · rw [hao]
          refine ih u hu ?_
          rw [hocc] at hn
          simp only [List.length_append, List.length_reverse, ConLeche.grpNews,
            List.length_map] at hn
          rw [← hao]; omega
        · rw [han]; exact hnil
      have hds := posNodeOk_dsAnc (hok u hu)
      rw [hocc]
      refine nodeHolesRead_grp' (hok u hu) hanc (fun ψ => ?_) (hfind u hu)
      obtain ⟨dsa, hdsa⟩ := hsp u hu ψ
      exact denoteMetaSpine_lower mpC.base2.acval_closed hdsa (fun x hx => (hds x hx).1)
        (by
          rcases (hok u hu).2.2.2.2.2 with ⟨hao, -⟩ | ⟨han, -⟩
          · rw [hao]; exact Nat.le_refl _
          · rw [han]; simp [ConLeche.NestCtx.hiAt])
  exact fun t ht => key _ t ht (Nat.le_refl _)

/-- **A frame's group is stored at the frame's levels**: a group member is
a member of the container's block, installed in `envC`, whose level count
`nestInstType` checked against the key's (official's `infer_constant`). -/
theorem grp_find_of {envI envC : Env} {mk : EnvModelM V μ envI}
    {mpC : EnvModelM V μ envC} {ctx : NestCtx} {ops : ConLeche.CheckerOps ConLeche.CheckM}
    (hcov : ContCover mk ctx) (hsub : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks) {nP : Nat}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (henvC : envC = ConLeche.consBlockCtors nP ctorsAs envI)
    {u : PosTree} (hu : PosNodeOk ops envI ctx u) :
    ∀ p ∈ u.grp, ∃ ci, envC.find? p.1 = some ci ∧
      u.key.lvls.length = ci.toConstantVal.levelParams.length := by
  intro p hp
  obtain ⟨-, -, -, hinst, -⟩ := posD_frame_inv hu.1
  obtain ⟨nI, hrun⟩ := hinst p hp
  obtain ⟨cvC, capsC, hfC, hlv⟩ := ConLeche.nestInstType_lvls hrun
  obtain ⟨D, hD, -, h2⟩ := posNodeOk_blk hcov hu p.1 (List.mem_map_of_mem hp)
  obtain ⟨lps, hl⟩ := blk_lps_envC hcov hsub henvC hD
  obtain ⟨i, hi, hpi⟩ := exists_member_of_mem_names (lfp_namesLen mk hD) h2
  obtain ⟨cv, caps, hf, hfI, -⟩ := hl i hi
  rw [hpi] at hf hfI
  rw [hcov.find, hfI] at hfC
  obtain ⟨rfl, rfl⟩ : cv = cvC ∧ caps = capsC := by simpa using hfC
  exact ⟨_, hf, hlv⟩

/-! ## The node facts of a listed `PosNodeOk` node -/

/-- **The class tie's node facts** (`NodeListFacts`) at any list of owned
`PosNodeOk` nodes of the walk's context whose keys are read at the
constructors' model (`hsp`): the group's block (`posNodeOk_blk`), its level
parameters (`posNodeOk_lps`), the stack's hole constants
(`nodeHolesRead_of`) and the key's scoping (`posNodeOk_ws`). -/
theorem nodeListFacts_of {F : Nat}
    {envC envI : Env} {pp : ConLeche.BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : RecCtxBase V μ F envC envI pp cvTasR ctorsAsR mpC dR isRecR A kindsR nfsR posR)
    {fvsP : List Expr} {ns : List PosTree}
    (hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find?) t)
    (hpar : ∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids)
    (hparF : fvsP.length = pp.nP ∧ ∀ (i : Nat) (x : Expr), fvsP[i]? = some x →
      ∃ ty, x = .fvar i ty)
    (hparS : ∀ x ∈ fvsP, ConLeche.ScB pp.nP x)
    (hsp : ∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
        ((pp.nestCtx fvsP envI.find?).hiAt t.occ.length) t.key.ds dsa) :
    NodeListFacts mpC (pp.nestCtx fvsP envI.find?) ns := by
  obtain ⟨-, henvC, -, -, hN, hS, hcore, -, hdR, -, -, ⟨mk, hmkC, hmk, -, -, -, -⟩, -⟩ := hctx
  have hcc : ContCover mk (pp.nestCtx fvsP envI.find?) :=
    contCover_of hmkC (fun _ => rfl)
  -- the members are stored at the block's level parameters
  have hmem : ∀ n ∈ (pp.nestCtx fvsP envI.find?).names, ∃ ci, envC.find? n = some ci ∧
      (pp.nestCtx fvsP envI.find?).lps.length
        = ci.toConstantVal.levelParams.length := by
    intro n hn
    change n ∈ pp.toBlockShape.memberNames at hn
    obtain ⟨c, hc, rfl⟩ := List.getElem_of_mem hn
    obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
    have hck : c < (blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).k := by
      change c < pp.toBlockShape.members.length
      simpa [ConLeche.BlockShape.memberNames] using hc
    obtain ⟨cvTb, hcvb⟩ : ∃ cvTb, cvTasR[c]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hck)⟩
    have hname := hN.1 c cvTb hcvb
    have hlpsT := hS.lpsT c cvTb hck hcvb
    obtain ⟨hf, -⟩ := hcore.1 c cvTb hcvb
    rw [← hname] at hf
    unfold BlockData.memberName at hf
    change envC.find? (pp.toBlockShape.memberNames.getD c .anonymous) = _ at hf
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc, Option.getD_some] at hf
    exact ⟨_, hf, by show pp.lps.length = cvTb.levelParams.length; rw [hlpsT]⟩
  refine ⟨fun t ht n hn => ?_, fun t ht => posNodeOk_lps hcc hmk henvC (hok t ht),
    nodeHolesRead_of hok hpar (nodeHolesRead_nil hparF hparS hmem) hsp
      (fun t ht => grp_find_of hcc hmk henvC (hok t ht)),
    fun t ht => posNodeOk_ws (hok t ht), hsp⟩
  obtain ⟨D, hD, h1, h2⟩ := posNodeOk_blk hcc (hok t ht) n hn
  exact ⟨D, hmk D hD, h1, h2⟩

end ConLeche.Model
