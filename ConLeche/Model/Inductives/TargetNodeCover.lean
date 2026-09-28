module

public import ConLeche.Model.Inductives.TargetNodeList
public import ConLeche.Model.Inductives.BlockPosRunCont
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Verify.Inductives.NestContInv
import ConLeche.Semantics.Inductives.DeclBlockEta
public import ConLeche.Model.Inductives.NestedRecCtx

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

/-- **A node's stack holes are owned**: every hole of its frame stack is a
new hole of some node's frame (`PosTree.Reached.occ_owners`). -/
@[expose] def NodeOwned (ops : ConLeche.CheckerOps ConLeche.CheckM) (env : Env) (ctx : NestCtx)
    (t : PosTree) : Prop :=
  ∀ hk ∈ t.occ, ∃ u, PosNodeOk ops env ctx u ∧
    hk ∈ ConLeche.grpNews u.key.lvls u.key.ds (ctx.hiAt u.anc.length) u.grp

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
    ∀ x ∈ t.key.ds, Expr.WScoped (ctx.nP + (nodeHoleConsts ctx t.occ).length) x := by
  intro x hx
  have h := (hok.2.2.2.2.1 x hx).1
  rw [nodeHoleConsts_length]
  simp only [ConLeche.NestCtx.hiAt] at h
  rwa [Nat.add_assoc] at h

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

/-- **A node's stack holes are stored at their level count**
(`NodeListFacts.read`): a member hole at the block's level parameters
(`hmem`), a frame hole — a group member of its owner's frame — at its
owner's levels, which `nestInstType` checked against the container's
level count (official's `infer_constant`). -/
theorem nodeHolesRead_of {envI envC : Env} {mk : EnvModelM V μ envI}
    {mpC : EnvModelM V μ envC} {ctx : NestCtx} {ops : ConLeche.CheckerOps ConLeche.CheckM}
    (hcov : ContCover mk ctx) (hsub : ∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks) {nP : Nat}
    {ctorsAs : List (List (ConstantVal × Nat))}
    (henvC : envC = ConLeche.consBlockCtors nP ctorsAs envI)
    (hmem : ∀ n ∈ ctx.names, ∃ ci, envC.find? n = some ci ∧
      ctx.lps.length = ci.toConstantVal.levelParams.length)
    {t : PosTree} (hown : NodeOwned ops envI ctx t) : NodeHolesRead envC ctx t.occ := by
  intro a ha
  simp only [nodeHoleConsts, List.mem_append, List.mem_map, List.mem_reverse] at ha
  rcases ha with ⟨n, hn, rfl⟩ | ⟨hk, hkm, rfl⟩
  · obtain ⟨ci, hf, hl⟩ := hmem n hn
    exact ⟨n, _, ci, rfl, hf, by simpa using hl⟩
  · obtain ⟨u, hu, hkn⟩ := hown hk hkm
    simp only [ConLeche.grpNews, List.mem_map] at hkn
    obtain ⟨p, hp, rfl⟩ := hkn
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
    exact ⟨p.1, _, _, rfl, hf, hlv⟩

/-! ## The node facts of a listed `PosNodeOk` node -/

/-- **The class tie's node facts** (`NodeListFacts`) at any list of owned
`PosNodeOk` nodes of the walk's context whose keys are read at the
constructors' model (`hsp`): the group's block (`posNodeOk_blk`), its level
parameters (`posNodeOk_lps`), the stack's hole constants
(`nodeHolesRead_of`) and the key's scoping (`posNodeOk_ws`). -/
theorem nodeListFacts_of {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : ConLeche.BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {keysR : List ConLeche.NestKey}
    (hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      keysR) {fvsP : List Expr} {ns : List PosTree}
    (hok : ∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t)
    (hown : ∀ t ∈ ns, NodeOwned (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t)
    (hsp : ∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
        ((pp.nestCtx fvsP envI.find? envI.consts).nP
          + (nodeHoleConsts (pp.nestCtx fvsP envI.find? envI.consts) t.occ).length) t.key.ds dsa) :
    NodeListFacts mpC (pp.nestCtx fvsP envI.find? envI.consts) ns := by
  obtain ⟨-, -, henvC, -, -, hN, hS, hcore, -, hdR, -, -, ⟨mk, hmkC, hmk, -, -, -, -⟩, -⟩ := hctx
  have hcc : ContCover mk (pp.nestCtx fvsP envI.find? envI.consts) :=
    contCover_of hmkC (fun _ => rfl) rfl
  -- the members are stored at the block's level parameters
  have hmem : ∀ n ∈ (pp.nestCtx fvsP envI.find? envI.consts).names, ∃ ci, envC.find? n = some ci ∧
      (pp.nestCtx fvsP envI.find? envI.consts).lps.length
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
    fun t ht => nodeHolesRead_of hcc hmk henvC hmem (hown t ht),
    fun t ht => posNodeOk_ws (hok t ht), hsp⟩
  obtain ⟨D, hD, h1, h2⟩ := posNodeOk_blk hcc (hok t ht) n hn
  exact ⟨D, hmk D hD, h1, h2⟩

end ConLeche.Model
