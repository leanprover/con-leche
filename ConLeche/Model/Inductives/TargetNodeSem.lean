module

public import ConLeche.Model.Inductives.TargetNodeCover
public import ConLeche.Model.Inductives.PosDerivNodes
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Inductives.ContFrame
import ConLeche.Verify.Inductives.NestScope
import ConLeche.Model.Rules.Inputs
import ConLeche.Model.Inductives.PosDerivTie
import ConLeche.Model.Inductives.LfpCover
import ConLeche.Verify.Inductives.PosAnn

public section

/-!
# Every listed node's key is READ, at the constructors' model

The node-semantics induction (`posD_nodeSem`, `PosDerivNodes.lean`) runs at
the formers' model `mk` (the derivation's environment `envI`) from a member
constructor's own reading — its crest, framed, read and graded in the
block's hole context (`blockCtorCrest`: the datum's reading fact at the
canonical crest the walk's term is up to erasure, `blockWalkCtx`'s U2
grading).  Every node of the constructor's forest then has its key's
parameters read at the depth of the frames it is derived under
(`memberCtor_nodesSem`); lifted to the depth of its occurrence and moved to
the constructors' model `mpC`/`envC` (`FormersModelAt`'s transport — the
constructors' conses keep every lookup), that is `NodeListFacts.sp`.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal CheckM NestCtx NestHole BlockParts
  BlockShape instPisWith nestAbstract nestHoles openPisAtFvars fueledOps PosTree PosNodeOk)

universe w

variable {V : Type w} [SetTheory V] {μ : ConLeche.CheckMode}

/-! ## A member constructor's crest, read in the hole context -/

/-- **A member constructor's crest in its hole context** (`blockCtorHoleCtx`
without the normal form): framed, in the context, read and graded. -/
theorem blockCtorCrest {env : Env} {m : EnvModel V env} {ψ : Name → Nat}
    (hin : Rules.RulesInputs V m ψ) {F : Nat}
    {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts m d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes)
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type) = some crest)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty)
    {tyN : Expr} {ksD : List ConLeche.PosKind} {ts : List PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts)
      cA.2 crest ksD tyN ts) :
    ∃ ca, (p.nestCtx fvsP env.find? env.consts).hiAt 0 = d.nP + d.k ∧
      Rules.Frame (d.nP + d.k) crest ∧
      CtxOkP m ψ (d.nP + d.k) (d.holeCtx ψ).reverse crest ∧
      denoteMeta m.acval env ψ (d.nP + d.k) crest = some ca ∧
      Rules.Graded V (d.holeCtx ψ).reverse ca := by
  have hcN : (p.nestCtx fvsP env.find? env.consts).names = d.memberNames := hnames
  have hcP : (p.nestCtx fvsP env.find? env.consts).nP = d.nP := hnP
  have hcL : (p.nestCtx fvsP env.find? env.consts).lps = lps := hlps
  have hcPar : (p.nestCtx fvsP env.find? env.consts).params = fvsP := rfl
  have hlenF : fvsP.length = d.nP := by
    rw [← hnP]; exact ConLeche.Verify.openPisAtFvars_length _ hop0
  have hidxF := ConLeche.openPisAtFvars_index _ _ _ hop0
  obtain ⟨-, A, hA, hR⟩ := (hcore.2 c j cA hcj).2
  obtain ⟨ab, -, hAr, -, -, -, -, -, -⟩ := hR ψ
  obtain ⟨A', hA', herased⟩ := canonCrest_of_walk (ctx := p.nestCtx fvsP env.find? env.consts)
    (k := d.k)
    (fun i x hx => by rw [hcPar] at hx; simpa using hidxF i x hx)
    (by rw [hcPar, hlenF, hcP])
    (fun t x hx => by
      have ht : t < (p.nestCtx fvsP env.find? env.consts).names.length := by
        rw [← nestHoles_length hholes]; exact (List.getElem?_eq_some_iff.mp hx).1
      obtain ⟨cv, caps, -, hget⟩ := nestHoles_getElem? hholes ht
      rw [hget] at hx
      exact ⟨_, (Option.some.inj hx).symm⟩)
    (by rw [nestHoles_length hholes, hcN, hk]) hcrest
  rw [hcN, hcL, hcP, hA] at hA'
  obtain rfl := Option.some.inj hA'
  have hca := hAr
  rw [← denoteMeta_erasedEq herased] at hca
  obtain ⟨-, -, -, hhi, -, -, -, -, -, hfr, hCP, hgr, -⟩ :=
    blockWalkCtx hin hN hcore.1 hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hCf hCb
      hcrest hinf hd hca
  exact ⟨_, hhi, hfr, hCP, hca, hgr⟩

/-- **Every node of a member constructor's derivation is read in its stack
context**, at the formers' model: `posD_nodeSem` from the constructor's
crest (`blockCtorCrest`). -/
theorem memberCtor_nodesSem {μ : ConLeche.CheckMode} {env : Env} (mk : EnvModelM V μ env)
    {F : Nat} {d : BlockData V} {lps : List Name} {cvTas : List ConstantVal} {p₁ : BlockShape}
    {isRec : Bool}
    (hN : BlockNamesOk (V := V) d cvTas) (hcore : BlockHoleCtxFacts mk.base2 d lps cvTas p₁ isRec)
    {p : BlockParts} (hnames : p.memberNames = d.memberNames) (hlps : p.lps = lps)
    (hnP : p.nP = d.nP) (hnIdxs : p.nIdxs = d.nIdxs) (hk : d.k = d.memberNames.length)
    {cvTa0 : ConstantVal} {fvsP : List Expr} {rest : Expr} {holes : List Expr}
    (hcv0 : cvTas.head? = some cvTa0)
    (hop0 : openPisAtFvars p.nP cvTa0.type 0 = some (fvsP, rest))
    (hholes : nestHoles (p.nestCtx fvsP env.find? env.consts) = some holes)
    (hcov : ContCover mk (p.nestCtx fvsP env.find? env.consts))
    {c j : Nat} {cA : ConstantVal × Nat} (hcj : (d.ctorsM c)[j]? = some cA)
    (hCf : cA.1.type.hasFvar = false) (hCb : cA.1.type.looseBVarsBounded 0 = true)
    {crest : Expr}
    (hcrest : instPisWith fvsP
      (nestAbstract (p.nestCtx fvsP env.find? env.consts) holes cA.1.type) = some crest)
    {ty : Expr} (hinf : ConLeche.inferTypeCore .verified env F
      ((p.nestCtx fvsP env.find? env.consts).hiAt 0) crest = .ok ty)
    {tyN : Expr} {ksD : List ConLeche.PosKind} {ts : List PosTree}
    (hd : ConLeche.MemberCtorD (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts)
      cA.2 crest ksD tyN ts) (ψ : Name → Nat) :
    NodesSem mk.base2 ψ (p.nestCtx fvsP env.find? env.consts) (d.holeCtx ψ).reverse ts := by
  obtain ⟨ca, hhi, hfr, hCP, hca, hgr⟩ := blockCtorCrest (Rules.RulesInputs.ofSem mk ψ) hN hcore
    hnames hlps hnP hnIdxs hk hcv0 hop0 hholes hcj hCf hCb hcrest hinf hd
  obtain ⟨nds, cur, hD, -⟩ := hd
  have hΔ0 : ((d.holeCtx ψ).reverse).length = (p.nestCtx fvsP env.find? env.consts).hiAt 0 := by
    rw [hhi]; exact hCP.1
  have h := posD_nodeSem mk (Rules.RulesInputs.ofSem mk ψ) hcov hΔ0 hD
  rw [← hhi] at hfr hCP hca
  exact h (by simp) (by rw [Nat.add_zero]; exact hfr) (by rw [Nat.add_zero]; exact hCP)
    (by rw [Nat.add_zero]; exact hca) hgr (by simp [stackCtx_nil])


/-! ## Forests: kids and parents -/

theorem PosTree.nodes_kid : ∀ (n : Nat) (r : PosTree), r.height ≤ n → ∀ {t k : PosTree},
    t ∈ r.nodes → k ∈ t.kids → k ∈ r.nodes
  | 0, r, hh, _, _, _, _ => by
    cases r with
    | node occ anc key grp kids => simp [PosTree.height] at hh
  | n + 1, r, hh, t, k, ht, hk => by
    rcases PosTree.mem_nodes.mp ht with rfl | ht
    · exact PosTree.mem_nodes.mpr (Or.inr (PosTree.mem_forest_of_mem hk))
    · obtain ⟨r', hr', htr'⟩ := PosTree.mem_forest_iff.mp ht
      have := PosTree.height_kid hr'
      have h' := PosTree.nodes_kid n r' (by omega) htr' hk
      exact PosTree.mem_nodes.mpr (Or.inr (PosTree.mem_forest_iff.mpr ⟨r', hr', h'⟩))

/-- A kid of a forest's node is a node of the forest. -/
theorem PosTree.mem_forest_kid {ts : List PosTree} {t k : PosTree} (ht : t ∈ PosTree.forest ts)
    (hk : k ∈ t.kids) : k ∈ PosTree.forest ts := by
  obtain ⟨r, hr, htr⟩ := PosTree.mem_forest_iff.mp ht
  exact PosTree.mem_forest_iff.mpr ⟨r, hr, PosTree.nodes_kid r.height r (Nat.le_refl _) htr hk⟩

/-- A reached node is a node of the forest. -/
theorem PosTree.mem_forest_of_reached {ts : List PosTree} {t : PosTree}
    (h : PosTree.Reached ts t) : t ∈ PosTree.forest ts := by
  induction h with
  | root hr => exact PosTree.mem_forest_of_mem hr
  | kid _ hk ih => exact PosTree.mem_forest_kid ih hk

theorem PosTree.nodes_parent : ∀ (n : Nat) (r : PosTree), r.height ≤ n → ∀ {t : PosTree},
    t ∈ r.nodes → t = r ∨ ∃ p ∈ r.nodes, t ∈ p.kids
  | 0, r, hh, _, _ => by
    cases r with
    | node occ anc key grp kids => simp [PosTree.height] at hh
  | n + 1, r, hh, t, ht => by
    rcases PosTree.mem_nodes.mp ht with rfl | ht
    · exact Or.inl rfl
    · obtain ⟨r', hr', htr'⟩ := PosTree.mem_forest_iff.mp ht
      have := PosTree.height_kid hr'
      refine Or.inr ?_
      rcases PosTree.nodes_parent n r' (by omega) htr' with rfl | ⟨p, hp, htp⟩
      · exact ⟨r, PosTree.mem_nodes.mpr (Or.inl rfl), hr'⟩
      · exact ⟨p, PosTree.mem_nodes.mpr (Or.inr (PosTree.mem_forest_iff.mpr ⟨r', hr', hp⟩)), htp⟩

/-- A node of a forest is a root or a kid of a node of the forest. -/
theorem PosTree.forest_parent {ts : List PosTree} {t : PosTree} (ht : t ∈ PosTree.forest ts) :
    t ∈ ts ∨ ∃ p ∈ PosTree.forest ts, t ∈ p.kids := by
  obtain ⟨r, hr, htr⟩ := PosTree.mem_forest_iff.mp ht
  rcases PosTree.nodes_parent r.height r (Nat.le_refl _) htr with rfl | ⟨p, hp, htp⟩
  · exact Or.inl hr
  · exact Or.inr ⟨p, PosTree.mem_forest_iff.mpr ⟨r, hr, hp⟩, htp⟩


/-! ## The node list: the forests of the chosen constructors' derivations -/

/-- **Every member constructor's walk, its forest listed**: at the walk's
context (the first former's parameter openers
`fvsP`), every member constructor has a derivation (`MemberCtorD`) at its
recorded normal form, typed at the hole context, whose forest is among the
listed nodes `ns` — the calls' landing at node `0` reads a container
field's node there. -/
@[expose] def MemberForests (F : Nat) (envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat))) (nfsR : List (List Expr)) (fvsP : List Expr)
    (ns : List PosTree) : Prop :=
  ∃ cvTa0 rest holes, cvTasR.head? = some cvTa0 ∧
    ConLeche.openPisAtFvars pp.nP cvTa0.type 0 = some (fvsP, rest) ∧
    ConLeche.nestHoles (pp.nestCtx fvsP envI.find? envI.consts) = some holes ∧
    ∀ (m : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[m]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → ∃ crest ks ts,
        instPisWith fvsP (nestAbstract (pp.nestCtx fvsP envI.find? envI.consts) holes cA.1.type)
          = some crest ∧
        ConLeche.MemberCtorD (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts)
          cA.2 crest ks ((nfsR.getD m []).getD j default) ts ∧
        (∃ ty, ConLeche.inferTypeCore .verified envI F
          ((pp.nestCtx fvsP envI.find? envI.consts).hiAt 0) crest = .ok ty) ∧
        ∀ u ∈ PosTree.forest ts, u ∈ ns

/-- **Parent pointers of a node list**: every
entry occurring at a frame has an earlier parent entry having it as a kid,
and every kid of an entry has an entry whose parent pointer is it — each
OCCURRENCE of a node knows its parent occurrence (`PosTree.annF`). -/
@[expose] def ParentPtrs (ns : List PosTree) (par : Nat → Nat) : Prop :=
  (∀ b, 0 < b → b ≤ ns.length → (ns.getD (b - 1) default).occ ≠ [] →
    0 < par b ∧ par b < b ∧ ns.getD (b - 1) default ∈ (ns.getD (par b - 1) default).kids) ∧
  (∀ b, 0 < b → b ≤ ns.length → ∀ k ∈ (ns.getD (b - 1) default).kids,
    ∃ b', 0 < b' ∧ b' ≤ ns.length ∧ ns.getD (b' - 1) default = k ∧ par b' = b)

/-- **The node list at a nested stage, closed under kids and parents**:
every node of the member-constructor derivations that the coverage
theorem (`outsideClass_reachedNode`) chose for some outside class, and of one derivation of
every member constructor (`MemberForests`).  Every listed node is a node,
owned, read in its stack context at the formers' model `mk`, its kids
listed, and its parent listed when it is not a root (a root occurs at no
frame); the list covers every outside class. -/
theorem nestedRecCtx_nodes (hμ : μ.verifiedChecks = true) {F : Nat} {block : List ConstantInfo}
    {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {mpC : EnvModelM V μ envC}
    {dR : BlockData V} {isRecR : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {nodesR : ConLeche.NestNodes}
    (hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      nodesR)
    (mk : EnvModelM V μ envI) (hmkC : LfpCover mk pp.toBlockShape.memberNames)
    (hcoreK : BlockHoleCtxFacts mk.base2 dR pp.lps cvTasR pp.toBlockShape isRecR)
    (hleg : ConLeche.targetLegacyAux pp.toBlockShape (out.map (·.2.1)) nodesR = some nodesR) :
    ∃ (fvsP : List Expr) (ns : List PosTree),
      (∀ t ∈ ns, PosNodeOk (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t) ∧
      (∀ t ∈ ns, NodeOwned (fueledOps .verified F) envI (pp.nestCtx fvsP envI.find? envI.consts) t) ∧
      (∀ t ∈ ns, ∀ k ∈ t.kids, k ∈ ns) ∧
      (∀ t ∈ ns, t.occ ≠ [] → ∃ p ∈ ns, t ∈ p.kids) ∧
      (∀ t ∈ ns, ∀ ψ, NodeSemAt mk.base2 ψ (pp.nestCtx fvsP envI.find? envI.consts)
        (dR.holeCtx ψ).reverse t) ∧
      (∀ t ∈ ns, ConLeche.FrameRec (fueledOps .verified F) envI
        (pp.nestCtx fvsP envI.find? envI.consts) nodesR.ctors t.anc t.key.lvls t.key.ds t.grp) ∧
      MemberForests F envI pp cvTasR ctorsAsR nfsR fvsP ns ∧
      (∃ par, ParentPtrs ns par) ∧
      ∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        ∃ t ∈ ns, NodeMajor (pp.nestCtx fvsP envI.find? envI.consts) (tgtMajor out c) t := by
  classical
  obtain ⟨hRec, hPos, -, -, -, hN, -, hcore, hctorsAs, hdR, -, -, -, -⟩ := hctx
  obtain rfl := ConLeche.CheckMode.eq_verified hμ
  -- the formers' and the constructors' types are closed
  have hT0 : ∀ cvTa0, cvTasR.head? = some cvTa0 → cvTa0.type.hasFvar = false := by
    intro cvTa0 h0
    have h0' : cvTasR[0]? = some cvTa0 := by
      rw [List.head?_eq_getElem?] at h0; exact h0
    obtain ⟨hf, -⟩ := hcore.1 0 cvTa0 h0'
    exact (mpC.base2.wf _ (List.mem_of_find?_eq_some hf)).1
  have hcl2 : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
      (dR.ctorsM c)[j]? = some cA ∧
      cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true := by
    intro c cs hcs j cA hcA
    have hc : c < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hcs).1
    rw [hctorsAs c hc] at hcs
    obtain rfl := Option.some.inj hcs
    have hck : c < dR.k := hN.2.2 ▸ hN.2.1 c j cA hcA
    obtain ⟨hf, -⟩ := hcore.2.2.2 c hck j cA hcA
    have hw := mpC.base2.wf _ (List.mem_of_find?_eq_some hf)
    exact ⟨hcA, hw.1, hw.2.2.2.1⟩
  have hcl : ∀ (c : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[c]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA → cA.1.type.hasFvar = false :=
    fun c cs hcs j cA hcA => (hcl2 c cs hcs j cA hcA).2.1
  obtain ⟨cvTa0, fvsP, rest, holes, h1, h2, h3, hall⟩ :=
    outsideClass_reachedNode mk.base2.wf hRec hPos hT0 hcl hleg
  obtain ⟨cvTa0', fvsP', rest', holes', h1', h2', h3', hder⟩ :=
    checkBlockPositivity_derivM mk.base2.wf hPos hT0 hcl
  rw [h1] at h1'
  obtain rfl := Option.some.inj h1'
  rw [h2] at h2'
  obtain ⟨rfl, rfl⟩ : fvsP = fvsP' ∧ rest = rest' := by simpa using h2'
  rw [h3] at h3'
  obtain rfl := Option.some.inj h3'
  generalize hctxE : pp.nestCtx fvsP envI.find? envI.consts = ctx at *
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hcov : ContCover mk ctx := by
    rw [← hctxE]; exact contCover_of hmkC (fun _ => rfl) rfl
  -- every chosen constructor's forest is read
  have hsem : ∀ (m : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat)
      (crest : Expr) (ks : List ConLeche.PosKind) (tyN : Expr) (ts : List PosTree),
      ctorsAsR[m]? = some cs → cs[j]? = some cA →
      instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest →
      ConLeche.MemberCtorD (fueledOps .verified F) envI ctx cA.2 crest ks tyN ts →
      ∀ ψ, NodesSem mk.base2 ψ ctx
        ((blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).holeCtx ψ).reverse ts := by
    intro m cs j cA crest ks tyN ts hcs hj hcr hd ψ
    obtain ⟨hcj, hCf, hCb⟩ := hcl2 m cs hcs j cA hj
    obtain ⟨crest', -, -, hcr', -, -, ⟨ty, hty⟩, -⟩ := hder m cs hcs j cA hj
    rw [hcr] at hcr'
    obtain rfl := Option.some.inj hcr'
    subst hctxE
    exact memberCtor_nodesSem mk hN hcoreK rfl rfl rfl rfl
      (by simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
        ConLeche.BlockShape.memberNames]) h1 h2 h3 hcov hcj hCf hCb hcr hty hd ψ
  -- the chosen forests: one per outside class
  have hex : ∀ c, ∃ ts : List PosTree,
      (¬ (c < out.length ∧ (tgtMajor out c).member = none) → ts = []) ∧
      (c < out.length → (tgtMajor out c).member = none →
        (∃ (m : Nat) (cs : List (ConstantVal × Nat)) (j : Nat) (cA : ConstantVal × Nat)
          (crest : Expr) (ks : List ConLeche.PosKind),
          ctorsAsR[m]? = some cs ∧ cs[j]? = some cA ∧
          instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest ∧
          ConLeche.MemberCtorD (fueledOps .verified F) envI ctx cA.2 crest ks
            ((nfsR.getD m []).getD j default) ts) ∧
        ConLeche.TreeRec (fueledOps .verified F) envI ctx nodesR.ctors ts ∧
        ∃ t, PosTree.Reached ts t ∧ NodeMajor ctx (tgtMajor out c) t) := by
    intro c
    by_cases h : c < out.length ∧ (tgtMajor out c).member = none
    · obtain ⟨m, cs, j, cA, crest, ks, ts, hcs, hj, hcr, hd, htr, t, hR, -, hNM⟩ :=
        hall c h.1 h.2
      exact ⟨ts, fun h' => absurd h h', fun _ _ =>
        ⟨⟨m, cs, j, cA, crest, ks, hcs, hj, hcr, hd⟩, htr, t, hR, hNM⟩⟩
    · exact ⟨[], fun _ => rfl, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  obtain ⟨tsOf, htsOf⟩ := Classical.axiomOfChoice hex
  -- one derivation per member constructor
  have hexM : ∀ q : Nat × Nat, ∃ ts : List PosTree,
      ∀ (cs : List (ConstantVal × Nat)) (cA : ConstantVal × Nat), ctorsAsR[q.1]? = some cs →
        cs[q.2]? = some cA → ∃ crest ks,
          instPisWith fvsP (nestAbstract ctx holes cA.1.type) = some crest ∧
          ConLeche.MemberCtorD (fueledOps .verified F) envI ctx cA.2 crest ks
            ((nfsR.getD q.1 []).getD q.2 default) ts ∧
          (∃ ty, ConLeche.inferTypeCore .verified envI F (ctx.hiAt 0) crest = .ok ty) ∧
          ConLeche.TreeRec (fueledOps .verified F) envI ctx nodesR.ctors ts := by
    intro q
    by_cases h : ∃ cs cA, ctorsAsR[q.1]? = some cs ∧ cs[q.2]? = some cA
    · obtain ⟨cs, cA, hcs, hj⟩ := h
      obtain ⟨crest, ks, ts, hcr, hd, -, hty, -, -, -, htr⟩ := hder q.1 cs hcs q.2 cA hj
      refine ⟨ts, fun cs' cA' hcs' hj' => ?_⟩
      rw [hcs] at hcs'
      obtain rfl := Option.some.inj hcs'
      rw [hj] at hj'
      obtain rfl := Option.some.inj hj'
      exact ⟨crest, ks.map (·.erase), hcr, hd, hty, htr⟩
    · exact ⟨[], fun cs cA hcs hj => absurd ⟨cs, cA, hcs, hj⟩ h⟩
  obtain ⟨tsM, htsM⟩ := Classical.axiomOfChoice hexM
  let rtC : List PosTree := (List.range out.length).flatMap fun c => tsOf c
  let rtM : List PosTree := (List.range ctorsAsR.length).flatMap fun m =>
    (List.range (ctorsAsR.getD m []).length).flatMap fun j => tsM (m, j)
  let L := PosTree.annF 0 0 (rtC ++ rtM)
  let ns : List PosTree := L.map (·.1)
  have hns : ns = PosTree.forest (rtC ++ rtM) := (PosTree.annF_spec _).1
  have hinR : ∀ ts : List PosTree, (∀ r ∈ ts, r ∈ rtC ++ rtM) → ∀ t ∈ PosTree.forest ts, t ∈ ns := by
    intro ts hts t ht
    rw [hns]
    obtain ⟨k, hk, htk⟩ := PosTree.mem_forest_iff.mp ht
    exact PosTree.mem_forest_iff.mpr ⟨k, hts k hk, htk⟩
  have hinC : ∀ c, c < out.length → ∀ t ∈ PosTree.forest (tsOf c), t ∈ ns :=
    fun c hc => hinR _ fun r hr =>
      List.mem_append_left _ (List.mem_flatMap.mpr ⟨c, List.mem_range.mpr hc, hr⟩)
  have hinM : ∀ (m : Nat) (cs : List (ConstantVal × Nat)), ctorsAsR[m]? = some cs →
      ∀ (j : Nat) (cA : ConstantVal × Nat), cs[j]? = some cA →
      ∀ t ∈ PosTree.forest (tsM (m, j)), t ∈ ns := by
    intro m cs hcs j cA hj
    have hm : m < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hcs).1
    have hgd : ctorsAsR.getD m [] = cs := by rw [List.getD_eq_getElem?_getD, hcs]; rfl
    have hjl : j < cs.length := (List.getElem?_eq_some_iff.mp hj).1
    refine hinR _ fun r hr => List.mem_append_right _ (List.mem_flatMap.mpr ⟨m,
      List.mem_range.mpr hm, List.mem_flatMap.mpr ⟨j, List.mem_range.mpr (by rw [hgd]; exact hjl),
        hr⟩⟩)
  -- per listed node: its derivation
  have hsrc : ∀ t ∈ ns, ∃ ts : List PosTree, t ∈ PosTree.forest ts ∧
      (∀ r ∈ ts, PosNodeOk (fueledOps .verified F) envI ctx r) ∧
      (∀ r ∈ ts, r.occ = []) ∧
      (∀ u ∈ PosTree.forest ts, PosNodeOk (fueledOps .verified F) envI ctx u) ∧
      (∀ ψ, NodesSem mk.base2 ψ ctx
        ((blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf).holeCtx ψ).reverse ts) ∧
      ConLeche.TreeRec (fueledOps .verified F) envI ctx nodesR.ctors ts ∧
      ∀ u ∈ PosTree.forest ts, u ∈ ns := by
    intro t ht
    rw [hns] at ht
    obtain ⟨r0, hr0, htr0⟩ := PosTree.mem_forest_iff.mp ht
    have htr0' : t ∈ PosTree.forest [r0] := PosTree.mem_forest_iff.mpr ⟨r0, List.mem_singleton_self _, htr0⟩
    rcases List.mem_append.mp hr0 with hr0 | hr0
    · obtain ⟨c, hc, hrc⟩ := List.mem_flatMap.mp hr0
      have htc : t ∈ PosTree.forest (tsOf c) := PosTree.mem_forest_iff.mpr ⟨r0, hrc, htr0⟩
      have hc' := List.mem_range.mp hc
      by_cases hM : (tgtMajor out c).member = none
      · obtain ⟨⟨m, cs, j, cA, crest, ks, hcs, hj, hcr, hd⟩, htr, -⟩ := (htsOf c).2 hc' hM
        obtain ⟨hocc0, hfor⟩ := ConLeche.memberCtorD_nodes hd
        exact ⟨tsOf c, htc, fun r hr => hfor r (PosTree.mem_forest_of_mem hr), hocc0, hfor,
          hsem m cs j cA crest ks _ _ hcs hj hcr hd, htr, hinC c hc'⟩
      · rw [(htsOf c).1 fun h => hM h.2] at htc
        exact nomatch htc
    · obtain ⟨m, hm, htm⟩ := List.mem_flatMap.mp hr0
      obtain ⟨j, hj, hrj⟩ := List.mem_flatMap.mp htm
      have htj : t ∈ PosTree.forest (tsM (m, j)) := PosTree.mem_forest_iff.mpr ⟨r0, hrj, htr0⟩
      have hm' := List.mem_range.mp hm
      have hj' := List.mem_range.mp hj
      obtain ⟨cs, hcs⟩ : ∃ cs, ctorsAsR[m]? = some cs := ⟨_, List.getElem?_eq_getElem hm'⟩
      have hgd : ctorsAsR.getD m [] = cs := by rw [List.getD_eq_getElem?_getD, hcs]; rfl
      rw [hgd] at hj'
      obtain ⟨cA, hcA⟩ : ∃ cA, cs[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj'⟩
      obtain ⟨crest, ks, hcr, hd, -, htr⟩ := htsM (m, j) cs cA hcs hcA
      obtain ⟨hocc0, hfor⟩ := ConLeche.memberCtorD_nodes hd
      exact ⟨tsM (m, j), htj, fun r hr => hfor r (PosTree.mem_forest_of_mem hr), hocc0, hfor,
        hsem m cs j cA crest ks _ _ hcs hcA hcr hd, htr, hinM m cs hcs j cA hcA⟩
  -- every root occurs at no frame
  have hroot0 : ∀ r ∈ rtC ++ rtM, r.occ = [] := by
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨c, hc, hrc⟩ := List.mem_flatMap.mp hr
      have hc' := List.mem_range.mp hc
      by_cases hM : (tgtMajor out c).member = none
      · obtain ⟨⟨m, cs, j, cA, crest, ks, hcs, hj, hcr, hd⟩, -, -⟩ := (htsOf c).2 hc' hM
        exact (ConLeche.memberCtorD_nodes hd).1 r hrc
      · rw [(htsOf c).1 fun h => hM h.2] at hrc
        exact nomatch hrc
    · obtain ⟨m, hm, htm⟩ := List.mem_flatMap.mp hr
      obtain ⟨j, hj, hrj⟩ := List.mem_flatMap.mp htm
      have hm' := List.mem_range.mp hm
      have hj' := List.mem_range.mp hj
      obtain ⟨cs, hcs⟩ : ∃ cs, ctorsAsR[m]? = some cs := ⟨_, List.getElem?_eq_getElem hm'⟩
      have hgd : ctorsAsR.getD m [] = cs := by rw [List.getD_eq_getElem?_getD, hcs]; rfl
      rw [hgd] at hj'
      obtain ⟨cA, hcA⟩ : ∃ cA, cs[j]? = some cA := ⟨_, List.getElem?_eq_getElem hj'⟩
      obtain ⟨crest, ks, hcr, hd, -, -⟩ := htsM (m, j) cs cA hcs hcA
      exact (ConLeche.memberCtorD_nodes hd).1 r hrj
  -- the parent pointers
  have hPP : ParentPtrs ns (fun b => (L.getD (b - 1) default).2) := by
    obtain ⟨-, hP, hK⟩ := PosTree.annF_spec (rtC ++ rtM)
    have hlen : ns.length = L.length := List.length_map _
    have hget : ∀ b, 0 < b → b ≤ ns.length → L[b - 1]? = some (ns.getD (b - 1) default,
        (L.getD (b - 1) default).2) := by
      intro b hb0 hbl
      have hl : b - 1 < L.length := by omega
      rw [List.getElem?_eq_getElem hl, List.getD_eq_getElem?_getD (l := L), List.getElem?_eq_getElem hl,
        Option.getD_some, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hl,
        Option.map_some, Option.getD_some]
    refine ⟨fun b hb0 hbl hocc => ?_, fun b hb0 hbl k hk => ?_⟩
    · rcases hP (b - 1) _ _ (hget b hb0 hbl) with ⟨h1, h2⟩ | ⟨h1, h2, e, he, h4⟩
      · exact absurd (hroot0 _ h2) hocc
      · dsimp only
        refine ⟨by omega, by omega, ?_⟩
        have hel := (List.getElem?_eq_some_iff.mp he).1
        have hge := hget ((L.getD (b - 1) default).2) (by omega) (by omega)
        rw [Nat.sub_zero] at he
        rw [he] at hge
        rw [← (Prod.mk.inj (Option.some.inj hge)).1]
        exact h4
    · obtain ⟨q', hq'⟩ := hK (b - 1) _ _ (hget b hb0 hbl) k hk
      have hq'l : q' < L.length := (List.getElem?_eq_some_iff.mp hq').1
      refine ⟨q' + 1, by omega, by omega, ?_, ?_⟩
      · rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, List.getElem?_map, hq']; rfl
      · show (L.getD (q' + 1 - 1) default).2 = b
        rw [Nat.add_sub_cancel, List.getD_eq_getElem?_getD, hq', Option.getD_some]
        simp only; omega
  refine ⟨fvsP, ns, fun t ht => ?_, fun t ht => ?_, fun t ht k hk => ?_, fun t ht hne => ?_,
    fun t ht ψ => ?_, fun t ht => ?_, ?_, ⟨_, hPP⟩, fun c hc hM => ?_⟩
  · obtain ⟨ts, htc, -, -, hfor, -⟩ := hsrc t ht
    rw [hctxE]; exact hfor t htc
  · obtain ⟨ts, htc, hroots, hocc0, -, -⟩ := hsrc t ht
    intro hk hkm
    obtain ⟨u, -, hu, -, hmemu⟩ :=
      (PosTree.Reached.of_forest htc).occ_owners hroots hocc0 hk hkm
    rw [hctxE]
    exact ⟨u, hu, hmemu⟩
  · obtain ⟨ts, htc, -, -, -, -, -, hin⟩ := hsrc t ht
    exact hin k (PosTree.mem_forest_kid htc hk)
  · obtain ⟨ts, htc, -, hocc0, -, -, -, hin⟩ := hsrc t ht
    rcases PosTree.forest_parent htc with hr | ⟨p, hp, htp⟩
    · exact absurd (hocc0 t hr) hne
    · exact ⟨p, hin p hp, htp⟩
  · obtain ⟨ts, htc, -, -, -, hS, -⟩ := hsrc t ht
    rw [hctxE]; exact hS ψ t htc
  · obtain ⟨ts, htc, -, -, -, -, htr, -⟩ := hsrc t ht
    rw [hctxE]; exact htr t htc
  · refine ⟨cvTa0, rest, holes, h1, h2, by rw [hctxE]; exact h3, fun m cs hcs j cA hj => ?_⟩
    obtain ⟨crest, ks, hcr, hd, hty, -⟩ := htsM (m, j) cs cA hcs hj
    refine ⟨crest, ks, tsM (m, j), by rw [hctxE]; exact hcr, by rw [hctxE]; exact hd,
      by rw [hctxE]; exact hty, hinM m cs hcs j cA hj⟩
  · have hc' : c < out.length := by simpa [tgtRs] using hc
    obtain ⟨-, -, t, hR, hNM⟩ := (htsOf c).2 hc' hM
    refine ⟨t, hinC c hc' t (PosTree.mem_forest_of_reached hR), ?_⟩
    rw [hctxE]; exact hNM

/-! ## Readings across the constructors' conses -/

/-- A spine read at one model is read at another that reads every term alike. -/
theorem DenoteMetaSpine.transport {acval₁ acval₂ : Name → (Name → Nat) → AnnotTerm}
    {env₁ env₂ : Env} {φ : Name → Nat} {d : Nat}
    (h : ∀ (e : Expr) {ea : AnnotTerm}, denoteMeta acval₁ env₁ φ d e = some ea →
      denoteMeta acval₂ env₂ φ d e = some ea) :
    ∀ {as : List Expr} {vs : List AnnotTerm}, DenoteMetaSpine acval₁ env₁ φ d as vs →
      DenoteMetaSpine acval₂ env₂ φ d as vs
  | _, _, .nil => .nil
  | _, _, .cons ha hs => .cons (h _ ha) (DenoteMetaSpine.transport h hs)

/-- **A node's key read at its occurrence**: its parameters read where its
frame is derived (`NodeSemAt`), lifted to its occurrence's depth. -/
theorem nodeSem_spOcc {env : Env} {m : EnvModel V env} {φ : Name → Nat} {ctx : NestCtx}
    {Δ0 : List AnnotTerm} {ops : ConLeche.CheckerOps CheckM} {t : PosTree}
    (hok : PosNodeOk ops env ctx t) (hsem : NodeSemAt m φ ctx Δ0 t) :
    ∃ dsa, DenoteMetaSpine m.acval env φ (ctx.nP + (nodeHoleConsts ctx t.occ).length) t.key.ds dsa := by
  obtain ⟨⟨dsa, hdsa⟩, -, -⟩ := hsem
  have hD : ctx.nP + (nodeHoleConsts ctx t.occ).length = ctx.hiAt t.occ.length := by
    rw [nodeHoleConsts_length]; simp only [NestCtx.hiAt]; omega
  rw [hD]
  obtain ⟨-, -, -, -, hws, hanc⟩ := hok
  rcases hanc with ⟨hao, -⟩ | ⟨han, hds⟩
  · rw [← hao]; exact ⟨dsa, hdsa⟩
  · rw [han] at hdsa
    exact ⟨_, DenoteMetaSpine.lift (m := m) (by simp only [NestCtx.hiAt]; omega)
      (fun x hx => (hds x hx).2) hdsa⟩

end ConLeche.Model
