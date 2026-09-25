module

public import ConLeche.Model.Inductives.TargetNodeList
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Model.Inductives.PosDerivMono
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Verify.Inductives.NestContInv

public section

/-!
# The node list at a nested stage, and its coverage (lane NESTIND, session 20)

POSDERIV-5's coverage theorem (`outsideClass_reachedNode`,
`PosDerivTie.lean`) gives every OUTSIDE recursor class a reached node of
SOME member constructor's derivation forest — a node (`PosNodeOk`) whose
key read back is the class's major (`NodeMajor`).  There is no single
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

/-- **The node list at a nested stage**: at the walk's context (the head
former's opened parameters `fvsP`), a list of positivity nodes covering
every outside recursor class. -/
theorem nestedRecCtx_nodes (hμ : μ.verifiedChecks = true) {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : ConLeche.BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {nodesR : List ConLeche.NestKey}
    (hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      nodesR) :
    ∃ (fvsP : List Expr) (ns : List PosTree),
      (∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t) ∧
      ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        ∃ t ∈ ns, NodeMajor (pp.nestCtx fvsP envI.find? envI.consts) (tgtMajor out c) t := by
  classical
  obtain ⟨hRec, hPos, -, -, -, hN, -, hcore, hctorsAs, -, -, -, hfm, -⟩ := hctx
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  obtain ⟨mk, -, -, -, -⟩ := hfm
  -- the formers' and the constructors' types are closed
  have hT0 : ∀ cvTa0, cvTasR.head? = some cvTa0 → cvTa0.type.hasFvar = false := by
    intro cvTa0 h0
    have h0' : cvTasR[0]? = some cvTa0 := by
      rw [List.head?_eq_getElem?] at h0; exact h0
    obtain ⟨hf, -⟩ := hcore.1 0 cvTa0 h0'
    exact (mpC.base2.wf _ (List.mem_of_find?_eq_some hf)).1
  have hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false := by
    intro c cs hcs j cA hcA
    have hc : c < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hcs).1
    rw [hctorsAs c hc] at hcs
    obtain rfl := Option.some.inj hcs
    have hck : c < dR.k := hN.2.2 ▸ hN.2.1 c j cA hcA
    obtain ⟨hf, -⟩ := hcore.2.2.2 c hck j cA hcA
    exact (mpC.base2.wf _ (List.mem_of_find?_eq_some hf)).1
  obtain ⟨cvTa0, fvsP, rest, holes, -, -, -, hall⟩ :=
    outsideClass_reachedNode mk.base2.wf hRec hPos hT0 hcl
  have hex : ∀ c, c < out.length → (tgtMajor out c).member = none →
      ∃ t, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t ∧
        NodeMajor (pp.nestCtx fvsP envI.find? envI.consts) (tgtMajor out c) t := by
    intro c hc hM
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, t, -, hok, hNM⟩ := hall c hc hM
    exact ⟨t, hok, hNM⟩
  let ns : List PosTree := (List.range out.length).filterMap fun c =>
    if h : c < out.length ∧ (tgtMajor out c).member = none then
      some (Classical.choose (hex c h.1 h.2)) else none
  refine ⟨fvsP, ns, fun t ht => ?_, fun c hc hM => ?_⟩
  · obtain ⟨c, -, hc⟩ := List.mem_filterMap.mp ht
    split at hc
    · rename_i h
      obtain rfl := Option.some.inj hc
      exact (Classical.choose_spec (hex c h.1 h.2)).1
    · exact nomatch hc
  · have hc' : c < out.length := by simpa [tgtRs] using hc
    refine ⟨Classical.choose (hex c hc' hM), List.mem_filterMap.mpr ⟨c, List.mem_range.mpr hc', ?_⟩,
      (Classical.choose_spec (hex c hc' hM)).2⟩
    rw [dif_pos ⟨hc', hM⟩]

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

/-! ## `NestedNodeListOwed` with the coverage discharged -/

/-- **OWED — the node facts and the dynamic part at ANY list of
`PosNodeOk` nodes** of the walk's context: the group's level parameters
(`NodeListFacts.lps`), the stack's hole constants read (`read`), the key
parameters read (`sp`), and `TgtNodeDyn`.  (The coverage —
`outsideClass_reachedNode` — the group's block and the key's scoping are
proved: `nestedNodeListOwed_of_rest`.) -/
@[expose] def NestedNodeRestOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : ConLeche.BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr))
    (nodesR : List ConLeche.NestKey),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR →
    ∀ (fvsP : List Expr) (ns : List PosTree),
      (∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t) →
      (∀ t ∈ ns, ∀ n ∈ t.grp.map (·.1), lpsOf envC t.key.cname = lpsOf envC n) ∧
      (∀ t ∈ ns, NodeHolesRead envC (pp.nestCtx fvsP envI.find? envI.consts) t.occ) ∧
      (∀ t ∈ ns, ∀ ψ : Name → Nat, ∃ dsa, DenoteMetaSpine mpC.base2.acval envC ψ
        ((pp.nestCtx fvsP envI.find? envI.consts).nP
          + (nodeHoleConsts (pp.nestCtx fvsP envI.find? envI.consts) t.occ).length) t.key.ds dsa) ∧
      ∀ (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal),
        (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
          TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) →
        (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
          Dc c = lfpSel mpC dR.toLfp (tgtMajor out c).ind) →
        ∀ (ψ : Name → Nat) (ρ : Nat → V) (xs : List V),
          (∃ c, c < (tgtRs out).length ∧ tgtClsG dR mpC.base2.acval envC pp.toBlockShape out ψ ρ xs c) →
          Nonempty (TgtNodeDyn μ F mpC (pp.nestCtx fvsP envI.find? envI.consts) dR pp.toBlockShape
            (cvTasR.map (·.type)) out Dc mc cvc ns ψ ρ xs)

/-- **`NestedNodeListOwed` from the rest**: the node list is POSDERIV-5's
(`nestedRecCtx_nodes`), its coverage and the facts `blk`/`ws` proved. -/
theorem nestedNodeListOwed_of_rest (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} (h : NestedNodeRestOwed V μ F block) :
    NestedNodeListOwed V μ F block := by
  intro envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hctx
  obtain ⟨fvsP, ns, hok, hcov⟩ := nestedRecCtx_nodes hμ hctx
  obtain ⟨hlps, hread, hsp, hdyn⟩ :=
    h envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hctx fvsP ns hok
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, ⟨mk, hmkC, hmk, -, -⟩, -⟩ := hctx
  have hcc : ContCover mk (pp.nestCtx fvsP envI.find? envI.consts) :=
    contCover_of hmkC (fun _ => rfl) rfl
  refine ⟨pp.nestCtx fvsP envI.find? envI.consts, ns, rfl, ⟨fun t ht n hn => ?_, hlps, hread,
    fun t ht => posNodeOk_ws (hok t ht), hsp⟩, fun ψ ρ xs c hc hM _ => hcov c hc hM, hdyn⟩
  obtain ⟨D, hD, h1, h2⟩ := posNodeOk_blk hcc (hok t ht) n hn
  exact ⟨D, hmk D hD, h1, h2⟩

/-- **The uniform block step at nested blocks, the coverage discharged.** -/
theorem declBlock_nested_of_rest (hμ : μ.verifiedChecks = true) {F : Nat}
    {env env₂ : ConLeche.Env} {block : List ConLeche.ConstantInfo} {nPd : Nat}
    {p₀ : ConLeche.BlockParts} (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂ true)
    (h : NestedNodeRestOwed V μ F block) :
    LfpCover mp [] → ∃ mp' : EnvModelM V μ env₂, LfpCover mp' [] :=
  declBlock_nested_of_list hμ mp hE hdp hrun (nestedNodeListOwed_of_rest hμ h)

end ConLeche.Model
