module

public import ConLeche.Model.Inductives.TargetNodeCover
public import ConLeche.Model.Inductives.PosDerivNodes
import ConLeche.Model.Annot.BitRename
import ConLeche.Model.Inductives.ContFrame
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
    {tyN : Expr} {ksD : List ConLeche.NestFieldKind} {ts : List PosTree}
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
  obtain ⟨-, A, hA, hR⟩ := (hcore.2.1 c j cA hcj).2
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
    {tyN : Expr} {ksD : List ConLeche.NestFieldKind} {ts : List PosTree}
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


/-- **Every node of a seed's derivation is read in its stack context**, at
the formers' model: `posD_nodeSem` from the seed's parameters, in the hole
context by their leaves (`blockHoleCtx_canon`). -/
theorem seed_nodesSem {μ : ConLeche.CheckMode} {env : Env} (mk : EnvModelM V μ env)
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
    {key : ConLeche.NestKey} {ts : List PosTree}
    (hd : ConLeche.PosD (fueledOps .verified F) env (p.nestCtx fvsP env.find? env.consts)
      (.seed key) ts) (ψ : Name → Nat) :
    NodesSem mk.base2 ψ (p.nestCtx fvsP env.find? env.consts) (d.holeCtx ψ).reverse ts := by
  have hcanon := blockHoleCtx_canon (ψ := ψ) hN hcore.1 hnames hlps hnP hnIdxs hk hcv0 hop0 hholes
  have hhi : (p.nestCtx fvsP env.find? env.consts).hiAt 0 = d.nP + d.k := by
    simp only [ConLeche.NestCtx.hiAt, ConLeche.BlockParts.nestCtx, hnames, hnP, hk, Nat.add_zero]
  have hΔ0 : ((d.holeCtx ψ).reverse).length = (p.nestCtx fvsP env.find? env.consts).hiAt 0 := by
    rw [hhi]; exact (hcanon (.sort .zero) (by simp [Expr.fvarLeaves])).1.1
  have hleaf := ConLeche.posD_seed_leaves hd
  refine posD_nodeSem mk (Rules.RulesInputs.ofSem mk ψ) hcov hΔ0 hd fun x hx => ?_
  rw [hhi]
  exact hcanon x (hleaf x hx holes hholes)

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
field's node there — and whose entry (the root frame's, at the block's
own levels and parameters) is recorded in the table `tbl`. -/
@[expose] def MemberForests (F : Nat) (envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat))) (nfsR : List (List Expr)) (fvsP : List Expr)
    (tbl : List ConLeche.NestCtorNf) (ns : List PosTree) : Prop :=
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
        (∀ u ∈ PosTree.forest ts, u ∈ ns) ∧
        (⟨cA.1.name, (pp.nestCtx fvsP envI.find? envI.consts).lps.map .param,
          (pp.nestCtx fvsP envI.find? envI.consts).params,
          ((nfsR.getD m []).getD j default).replaceFVars
            (ConLeche.nestHoleConst (pp.nestCtx fvsP envI.find? envI.consts) [])⟩ :
          ConLeche.NestCtorNf) ∈ tbl

/-- **Parent pointers of a node list**: every
entry occurring at a frame has an earlier parent entry having it as a kid,
and every kid of an entry has an entry whose parent pointer is it — each
OCCURRENCE of a node knows its parent occurrence (`PosTree.annF`). -/
@[expose] def ParentPtrs (ns : List PosTree) (par : Nat → Nat) : Prop :=
  (∀ b, 0 < b → b ≤ ns.length → (ns.getD (b - 1) default).occ ≠ [] →
    0 < par b ∧ par b < b ∧ ns.getD (b - 1) default ∈ (ns.getD (par b - 1) default).kids) ∧
  (∀ b, 0 < b → b ≤ ns.length → ∀ k ∈ (ns.getD (b - 1) default).kids,
    ∃ b', 0 < b' ∧ b' ≤ ns.length ∧ ns.getD (b' - 1) default = k ∧ par b' = b)

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
