import Setlec.Kernel.IExpr

/-!
# The arena invariant and its preservation (self-contained)

The verification of the `EStore` interning arena as a *data structure*,
kept free of any checker or model imports so that the implementation
layer may consume it (the `Std.HashMap` pattern: a kernel-layer type may
bundle its own invariant when that invariant's verification is
self-contained).  `Setlec/Kernel/WFStore.lean` builds the
correct-by-construction bundle `WFStore` on top of this module;
`Setlec/Verify/IExpr.lean` (the traversal-operation commutation proofs)
imports it and adds everything that talks about the checker.

Contents:
* `denote` / `denoteL` / `denoteN` — structural readback of an interned
  index as a `Setlec.Expr` / `Level` / `Name` (the spec the invariant is
  stated against);
* `EStore.WF` — the store invariant (children strictly below their
  parent, cons-tables exactly the graphs of the node tables, eager
  derived-field arrays congruent and satisfying their recurrences);
* preservation: `empty_wf`, `intern_wf` / `internL_wf` / `internN_wf`
  and the whole-tree round-trips `internExpr_spec` /
  `internLevel_spec` / `internName_spec` (WF ∧ Ext ∧ denotation);
* canonicity: `denote_inj` / `denote_eq_iff` — index equality is
  expression equality;
* the eager derived-field exactness facts (`WF.bvarBoundD_exact`,
  `WF.fvarRangeD_exact`, `WF.lhasParamD_exact`, `WF.ehasParamD_exact`,
  `WF.readbackN_eq_denoteN`);
* `internExprFast_eq` — the boundary fast path equals `internExpr`.
-/

namespace Setlec

/-! ## The level layer (task #62)

Interned levels mirror the expression arena: `denoteL` is the
structural denotation of a level index, `LNode.children` the child
indices, and the well-formedness/canonicity lemmas repeat the
expression ones one level down. -/

/-- The child indices of a level node. -/
def LNode.children : LNode → List LIdx
  | .zero | .param _ => []
  | .succ u => [u]
  | .max u v | .imax u v => [u, v]

/-- The level references of an expression node (sort level, constant
level arguments, binder codomain annotation). -/
def ENode.levels : ENode → List LIdx
  | .sort u => [u]
  | .const _ us => us
  | .lam _ _ _ m | .forallE _ _ _ m => m.cod.toList
  | _ => []

namespace EStore

/-- Denotation of a single level node given denotations for the child
indices. -/
def denoteLNode (den : LIdx → Option Level) : LNode → Option Level
  | .zero => some .zero
  | .param n => some (.param n)
  | .succ u => (den u).map Level.succ
  | .max u v => (den u).bind fun lu => (den v).map fun lv => .max lu lv
  | .imax u v => (den u).bind fun lu => (den v).map fun lv => .imax lu lv

/-- Structural denotation of a level index (well-founded on the index,
like `denote`). -/
def denoteL (st : EStore) (u : LIdx) : Option Level :=
  match st.lnodes[u]? with
  | none => none
  | some n =>
    denoteLNode (fun v => if _h : v < u then st.denoteL v else none) n
termination_by u

/-- Denotation of a level index list under a level denotation. -/
def denoteLList (denL : LIdx → Option Level) : List LIdx → Option (List Level)
  | [] => some []
  | u :: us =>
    (denL u).bind fun l => (denoteLList denL us).map fun ls => l :: ls

/-- Denotation of interned binder metadata under a level denotation. -/
def denoteBM (denL : LIdx → Option Level) : IBinderMeta → Option BinderMeta
  | ⟨bi, none⟩ => some ⟨bi, none⟩
  | ⟨bi, some u⟩ => (denL u).map fun l => ⟨bi, some l⟩

/-- `denoteLList` only looks at the listed indices. -/
theorem denoteLList_congr {l₁ l₂ : LIdx → Option Level} :
    ∀ {us : List LIdx}, (∀ u ∈ us, l₁ u = l₂ u) →
      denoteLList l₁ us = denoteLList l₂ us := by
  intro us
  induction us with
  | nil => intro _; rfl
  | cons u us ih =>
    intro h
    simp only [denoteLList, h u (by simp),
      ih (fun v hv => h v (by simp [hv]))]

/-- `denoteBM` only looks at the codomain annotation. -/
theorem denoteBM_congr {l₁ l₂ : LIdx → Option Level} {m : IBinderMeta}
    (h : ∀ u ∈ m.cod.toList, l₁ u = l₂ u) :
    denoteBM l₁ m = denoteBM l₂ m := by
  obtain ⟨bi, (_ | u)⟩ := m
  · rfl
  · simp only [denoteBM, h u (by simp)]

/-- `denoteLNode` only looks at the children. -/
theorem denoteLNode_congr {d₁ d₂ : LIdx → Option Level} {n : LNode}
    (h : ∀ c ∈ n.children, d₁ c = d₂ c) :
    denoteLNode d₁ n = denoteLNode d₂ n := by
  cases n <;> simp_all [denoteLNode, LNode.children]

/-- One-step unfolding of `denoteL` when the children sit below the
index. -/
theorem denoteL_node {st : EStore} {u : LIdx} {n : LNode}
    (hn : st.lnodes[u]? = some n) (hc : ∀ c ∈ n.children, c < u) :
    st.denoteL u = denoteLNode st.denoteL n := by
  rw [denoteL.eq_def, hn]
  exact denoteLNode_congr fun c h => dif_pos (hc c h)

theorem dite_denoteL_some {st : EStore} {c u : LIdx} {x : Level}
    (h : (if _h : c < u then st.denoteL c else none) = some x) :
    c < u ∧ st.denoteL c = some x := by
  by_cases hc : c < u <;> simp_all

/-- A successful level denotation exposes its node. -/
theorem denoteL_some_inv {st : EStore} {u : LIdx} {a : Level}
    (h : st.denoteL u = some a) :
    ∃ n, st.lnodes[u]? = some n ∧ (∀ c ∈ n.children, c < u) ∧
      denoteLNode st.denoteL n = some a := by
  rw [denoteL.eq_def] at h
  split at h
  · exact absurd h (by simp)
  · rename_i n hn
    refine ⟨n, hn, ?_⟩
    cases n with
    | zero => exact ⟨by simp [LNode.children], h⟩
    | param p => exact ⟨by simp [LNode.children], h⟩
    | succ l =>
      rw [denoteLNode, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨hlt, hx⟩ := dite_denoteL_some hx
      refine ⟨by simp [LNode.children, hlt], ?_⟩
      rw [denoteLNode, hx]; rfl
    | max l r =>
      rw [denoteLNode, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨hltx, hx⟩ := dite_denoteL_some hx
      obtain ⟨hlty, hy⟩ := dite_denoteL_some hy
      refine ⟨by simp [LNode.children, hltx, hlty], ?_⟩
      rw [denoteLNode, hx, hy]; rfl
    | imax l r =>
      rw [denoteLNode, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨y, hy, rfl⟩ := h
      obtain ⟨hltx, hx⟩ := dite_denoteL_some hx
      obtain ⟨hlty, hy⟩ := dite_denoteL_some hy
      refine ⟨by simp [LNode.children, hltx, hlty], ?_⟩
      rw [denoteLNode, hx, hy]; rfl

/-- A denoted level node's children denote. -/
theorem denoteLNode_children_some {den : LIdx → Option Level} {n : LNode}
    {a : Level} (h : denoteLNode den n = some a) :
    ∀ c ∈ n.children, ∃ b, den c = some b := by
  cases n <;>
    simp_all [denoteLNode, LNode.children, Option.map_eq_some_iff,
      Option.bind_eq_some_iff] <;>
    obtain ⟨x, hx, h⟩ := h <;>
    (try obtain ⟨y, hy, h⟩ := h) <;>
    simp_all

/-- Successful level denotation implies the index is in range. -/
theorem denoteL_lt_size {st : EStore} {u : LIdx} {a : Level}
    (h : st.denoteL u = some a) : u < st.lnodes.size := by
  obtain ⟨n, hn, -, -⟩ := denoteL_some_inv h
  exact (Array.getElem?_eq_some_iff.mp hn).1

end EStore

/-! ## The name layer (task #88)

Interned names mirror the level arena one layer down again: `denoteN`
is the structural denotation of a name index, `NNode.children` the
prefix indices; names have no binders and no levels, so the layer is a
plain structural walk. -/

/-- The child (prefix) indices of a name node. -/
def NNode.children : NNode → List NIdx
  | .anonymous => []
  | .str p _ | .num p _ => [p]

namespace EStore

/-- Denotation of a single name node given denotations for the prefix
indices. -/
def denoteNNode (den : NIdx → Option Name) : NNode → Option Name
  | .anonymous => some .anonymous
  | .str p s => (den p).map (Name.str · s)
  | .num p n => (den p).map (Name.num · n)

/-- Structural denotation of a name index (well-founded on the index,
like `denoteL`). -/
def denoteN (st : EStore) (i : NIdx) : Option Name :=
  match st.nnodes[i]? with
  | none => none
  | some n =>
    denoteNNode (fun p => if _h : p < i then st.denoteN p else none) n
termination_by i

/-- `denoteNNode` only looks at the children. -/
theorem denoteNNode_congr {d₁ d₂ : NIdx → Option Name} {n : NNode}
    (h : ∀ c ∈ n.children, d₁ c = d₂ c) :
    denoteNNode d₁ n = denoteNNode d₂ n := by
  cases n <;> simp_all [denoteNNode, NNode.children]

/-- One-step unfolding of `denoteN` when the children sit below the
index. -/
theorem denoteN_node {st : EStore} {i : NIdx} {n : NNode}
    (hn : st.nnodes[i]? = some n) (hc : ∀ c ∈ n.children, c < i) :
    st.denoteN i = denoteNNode st.denoteN n := by
  rw [denoteN.eq_def, hn]
  exact denoteNNode_congr fun c h => dif_pos (hc c h)

theorem dite_denoteN_some {st : EStore} {c i : NIdx} {x : Name}
    (h : (if _h : c < i then st.denoteN c else none) = some x) :
    c < i ∧ st.denoteN c = some x := by
  by_cases hc : c < i <;> simp_all

/-- A successful name denotation exposes its node. -/
theorem denoteN_some_inv {st : EStore} {i : NIdx} {a : Name}
    (h : st.denoteN i = some a) :
    ∃ n, st.nnodes[i]? = some n ∧ (∀ c ∈ n.children, c < i) ∧
      denoteNNode st.denoteN n = some a := by
  rw [denoteN.eq_def] at h
  split at h
  · exact absurd h (by simp)
  · rename_i n hn
    refine ⟨n, hn, ?_⟩
    cases n with
    | anonymous => exact ⟨by simp [NNode.children], h⟩
    | str p s =>
      rw [denoteNNode, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨hlt, hx⟩ := dite_denoteN_some hx
      refine ⟨by simp [NNode.children, hlt], ?_⟩
      rw [denoteNNode, hx]; rfl
    | num p k =>
      rw [denoteNNode, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨hlt, hx⟩ := dite_denoteN_some hx
      refine ⟨by simp [NNode.children, hlt], ?_⟩
      rw [denoteNNode, hx]; rfl

/-- A denoted name node's children denote. -/
theorem denoteNNode_children_some {den : NIdx → Option Name} {n : NNode}
    {a : Name} (h : denoteNNode den n = some a) :
    ∀ c ∈ n.children, ∃ b, den c = some b := by
  cases n <;>
    simp_all [denoteNNode, NNode.children, Option.map_eq_some_iff] <;>
    grind

/-- Successful name denotation implies the index is in range. -/
theorem denoteN_lt_size {st : EStore} {i : NIdx} {a : Name}
    (h : st.denoteN i = some a) : i < st.nnodes.size := by
  obtain ⟨n, hn, -, -⟩ := denoteN_some_inv h
  exact (Array.getElem?_eq_some_iff.mp hn).1

/-- Stores agreeing on the name nodes denote all name indices
identically. -/
theorem denoteN_eq_of_nnodes_eq {st st' : EStore}
    (h : st'.nnodes = st.nnodes) : ∀ i, st'.denoteN i = st.denoteN i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    rw [denoteN.eq_def, denoteN.eq_def, h]
    cases st.nnodes[i]? with
    | none => rfl
    | some n =>
      exact denoteNNode_congr fun c _hc => by
        by_cases hci : c < i
        · simp only [dif_pos hci, ih c hci]
        · simp [dif_neg hci]

/-- Stores agreeing on the name nodes below `k` denote all name
indices below `k` identically. -/
theorem denoteN_agree {st st' : EStore} {k : Nat}
    (hpre : ∀ j, j < k → st'.nnodes[j]? = st.nnodes[j]?) :
    ∀ i, i < k → st'.denoteN i = st.denoteN i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hik
    rw [denoteN.eq_def, denoteN.eq_def, hpre i hik]
    cases st.nnodes[i]? with
    | none => rfl
    | some n =>
      exact denoteNNode_congr fun c _hc => by
        by_cases hci : c < i
        · simp only [dif_pos hci]
          exact ih c hci (Nat.lt_trans hci hik)
        · simp [dif_neg hci]

end EStore

/-- The child indices of a node (annotation, function/argument, binder
domain/body, …). -/
def ENode.children : ENode → List EIdx
  | .bvar _ | .sort _ | .const _ _ | .lit _ => []
  | .fvar _ _ t => [t]
  | .app f a => [f, a]
  | .lam _ t b _ | .forallE _ t b _ => [t, b]
  | .letE _ t v b => [t, v, b]
  | .proj _ _ e => [e]

namespace EStore

/-- Denotation of a single node given denotations for the child
indices and for the level references: rebuild the `Expr` constructor
over the children's values. -/
def denoteNode (den : EIdx → Option Expr) (denL : LIdx → Option Level)
    (denN : NIdx → Option Name) : ENode → Option Expr
  | .bvar i => some (.bvar i)
  | .fvar idx nm t =>
    (den t).bind fun et => (denN nm).map fun name => .fvar idx name et
  | .sort u => (denL u).map Expr.sort
  | .const n us =>
    (denoteLList denL us).bind fun ls => (denN n).map fun name =>
      .const name ls
  | .app f a => (den f).bind fun ef => (den a).map fun ea => .app ef ea
  | .lam n t b m => (den t).bind fun et => (den b).bind fun eb =>
      (denoteBM denL m).bind fun bm => (denN n).map fun name =>
        .lam name et eb bm
  | .forallE n t b m =>
    (den t).bind fun et => (den b).bind fun eb =>
      (denoteBM denL m).bind fun bm => (denN n).map fun name =>
        .forallE name et eb bm
  | .letE n t v b =>
    (den t).bind fun et => (den v).bind fun ev => (den b).bind fun eb =>
      (denN n).map fun name => .letE name et ev eb
  | .lit l => some (.lit l)
  | .proj s j e =>
    (den e).bind fun x => (denN s).map fun name => .proj name j x

/-- Structural denotation of an index: read the node and denote its
children recursively (levels through `denoteL`).  Out-of-range indices
and forward references (children not strictly below their parent)
denote `none`, which makes the recursion well-founded on the index. -/
def denote (st : EStore) (i : EIdx) : Option Expr :=
  match st.nodes[i]? with
  | none => none
  | some n =>
    denoteNode (fun j => if _h : j < i then st.denote j else none)
      st.denoteL st.denoteN n
termination_by i

/-- `denoteNode` only looks at the children and the level references. -/
theorem denoteNode_congr' {d₁ d₂ : EIdx → Option Expr}
    {l₁ l₂ : LIdx → Option Level} {n₁ n₂ : NIdx → Option Name} {n : ENode}
    (h : ∀ c ∈ n.children, d₁ c = d₂ c)
    (hl : ∀ u ∈ n.levels, l₁ u = l₂ u)
    (hn : ∀ p ∈ n.names, n₁ p = n₂ p) :
    denoteNode d₁ l₁ n₁ n = denoteNode d₂ l₂ n₂ n := by
  cases n with
  | sort u => simp_all [denoteNode, ENode.levels]
  | const nm us =>
    simp only [denoteNode, denoteLList_congr (l₂ := l₂)
      (by simpa [ENode.levels] using hl),
      hn nm (by simp [ENode.names])]
  | lam nm t b m =>
    simp only [denoteNode, h t (by simp [ENode.children]),
      h b (by simp [ENode.children]),
      denoteBM_congr (l₂ := l₂) (by simpa [ENode.levels] using hl),
      hn nm (by simp [ENode.names])]
  | forallE nm t b m =>
    simp only [denoteNode, h t (by simp [ENode.children]),
      h b (by simp [ENode.children]),
      denoteBM_congr (l₂ := l₂) (by simpa [ENode.levels] using hl),
      hn nm (by simp [ENode.names])]
  | bvar i => rfl
  | lit l => rfl
  | fvar idx nm t =>
    simp only [denoteNode, h t (by simp [ENode.children]),
      hn nm (by simp [ENode.names])]
  | app f a =>
    simp only [denoteNode, h f (by simp [ENode.children]),
      h a (by simp [ENode.children])]
  | letE nm t v b =>
    simp only [denoteNode, h t (by simp [ENode.children]),
      h v (by simp [ENode.children]), h b (by simp [ENode.children]),
      hn nm (by simp [ENode.names])]
  | proj sN j e =>
    simp only [denoteNode, h e (by simp [ENode.children]),
      hn sN (by simp [ENode.names])]

/-- `denoteNode` at fixed level and name denotations only looks at the
children (the shape every same-store rewrite uses). -/
theorem denoteNode_congr {d₁ d₂ : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name} {n : ENode}
    (h : ∀ c ∈ n.children, d₁ c = d₂ c) :
    denoteNode d₁ denL denN n = denoteNode d₂ denL denN n :=
  denoteNode_congr' h (fun _ _ => rfl) (fun _ _ => rfl)

/-- One-step unfolding of `denote` when the children are known to sit
below the index: the guards disappear. -/
theorem denote_node {st : EStore} {i : EIdx} {n : ENode}
    (hn : st.nodes[i]? = some n) (hc : ∀ c ∈ n.children, c < i) :
    st.denote i = denoteNode st.denote st.denoteL st.denoteN n := by
  rw [denote.eq_def, hn]
  exact denoteNode_congr fun c h => dif_pos (hc c h)

/-- A guarded child lookup that succeeded: the guard held and the
lookup succeeded. -/
private theorem dite_denote_some {st : EStore} {c i : EIdx} {x : Expr}
    (h : (if _h : c < i then st.denote c else none) = some x) :
    c < i ∧ st.denote c = some x := by
  by_cases hc : c < i <;> simp_all

/-- A successful denotation exposes its node, with children strictly
below the index and denoting the subterms. -/
theorem denote_some_inv {st : EStore} {i : EIdx} {a : Expr}
    (h : st.denote i = some a) :
    ∃ n, st.nodes[i]? = some n ∧ (∀ c ∈ n.children, c < i) ∧
      denoteNode st.denote st.denoteL st.denoteN n = some a := by
  rw [denote.eq_def] at h
  split at h
  · exact absurd h (by simp)
  · rename_i n hn
    refine ⟨n, hn, ?_⟩
    cases n with
    | bvar k => exact ⟨by simp [ENode.children], h⟩
    | sort u => exact ⟨by simp [ENode.children], h⟩
    | const nm us => exact ⟨by simp [ENode.children], h⟩
    | lit l => exact ⟨by simp [ENode.children], h⟩
    | fvar idx nm t =>
      rw [denoteNode, Option.bind_eq_some_iff] at h
      obtain ⟨t', ht, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨name, hname, rfl⟩ := h
      obtain ⟨hlt, ht⟩ := dite_denote_some ht
      refine ⟨by simp [ENode.children, hlt], ?_⟩
      rw [denoteNode, ht, hname]; rfl
    | app f a' =>
      rw [denoteNode, Option.bind_eq_some_iff] at h
      obtain ⟨ef, hf, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨ea, ha, rfl⟩ := h
      obtain ⟨hltf, hf⟩ := dite_denote_some hf
      obtain ⟨hlta, ha⟩ := dite_denote_some ha
      refine ⟨by simp [ENode.children, hltf, hlta], ?_⟩
      rw [denoteNode, hf, ha]; rfl
    | lam nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at h
      obtain ⟨et, ht, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨eb, hb, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨bm, hbm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨name, hname, rfl⟩ := h
      obtain ⟨hltt, ht⟩ := dite_denote_some ht
      obtain ⟨hltb, hb⟩ := dite_denote_some hb
      refine ⟨by simp [ENode.children, hltt, hltb], ?_⟩
      rw [denoteNode, ht, hb, hbm, hname]; rfl
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at h
      obtain ⟨et, ht, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨eb, hb, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨bm, hbm, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨name, hname, rfl⟩ := h
      obtain ⟨hltt, ht⟩ := dite_denote_some ht
      obtain ⟨hltb, hb⟩ := dite_denote_some hb
      refine ⟨by simp [ENode.children, hltt, hltb], ?_⟩
      rw [denoteNode, ht, hb, hbm, hname]; rfl
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at h
      obtain ⟨et, ht, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨ev, hv, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨eb, hb, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨name, hname, rfl⟩ := h
      obtain ⟨hltt, ht⟩ := dite_denote_some ht
      obtain ⟨hltv, hv⟩ := dite_denote_some hv
      obtain ⟨hltb, hb⟩ := dite_denote_some hb
      refine ⟨by simp [ENode.children, hltt, hltv, hltb], ?_⟩
      rw [denoteNode, ht, hv, hb, hname]; rfl
    | proj s j e' =>
      rw [denoteNode, Option.bind_eq_some_iff] at h
      obtain ⟨x, hx, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨name, hname, rfl⟩ := h
      obtain ⟨hlt, hx⟩ := dite_denote_some hx
      refine ⟨by simp [ENode.children, hlt], ?_⟩
      rw [denoteNode, hx, hname]; rfl

/-- A denoted node's children denote. -/
theorem denoteNode_children_some {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name} {n : ENode}
    {a : Expr} (h : denoteNode den denL denN n = some a) :
    ∀ c ∈ n.children, ∃ b, den c = some b := by
  cases n <;>
    simp_all [denoteNode, ENode.children, Option.map_eq_some_iff,
      Option.bind_eq_some_iff] <;>
    obtain ⟨x, hx, h⟩ := h <;>
    (try obtain ⟨y, hy, h⟩ := h) <;>
    (try obtain ⟨z, hz, h⟩ := h) <;>
    (try obtain ⟨w, hw, h⟩ := h) <;>
    simp_all

/-- Successful denotation implies the index is in range. -/
theorem denote_lt_size {st : EStore} {i : EIdx} {a : Expr}
    (h : st.denote i = some a) : i < st.nodes.size := by
  obtain ⟨n, hn, -, -⟩ := denote_some_inv h
  exact (Array.getElem?_eq_some_iff.mp hn).1

/-- Store extension: every stored node (expression and level) is still
stored, at the same index.  `intern`/`internL`/`internExpr` only push
new nodes, so they extend. -/
structure Ext (st st' : EStore) : Prop where
  expr : ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n → st'.nodes[i]? = some n
  lvl : ∀ (u : LIdx) (m : LNode), st.lnodes[u]? = some m → st'.lnodes[u]? = some m
  name : ∀ (i : NIdx) (m : NNode), st.nnodes[i]? = some m → st'.nnodes[i]? = some m

theorem Ext.refl (st : EStore) : Ext st st :=
  ⟨fun _ _ h => h, fun _ _ h => h, fun _ _ h => h⟩

theorem Ext.trans {st₁ st₂ st₃ : EStore} (h₁ : Ext st₁ st₂)
    (h₂ : Ext st₂ st₃) : Ext st₁ st₃ :=
  ⟨fun i n h => h₂.expr i n (h₁.expr i n h),
   fun u m h => h₂.lvl u m (h₁.lvl u m h),
   fun i m h => h₂.name i m (h₁.name i m h)⟩

/-- Name denotation is stable under store extension. -/
theorem denoteN_mono {st st' : EStore} (hext : Ext st st') :
    ∀ {i : NIdx} {a : Name}, st.denoteN i = some a → st'.denoteN i = some a := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro a h
    obtain ⟨n, hn, hc, hd⟩ := denoteN_some_inv h
    rw [denoteN_node (hext.name i n hn) hc, ← hd]
    apply denoteNNode_congr
    intro c hcin
    obtain ⟨b, hb⟩ := denoteNNode_children_some hd c hcin
    rw [hb, ih c (hc c hcin) hb]

/-- Level denotation is stable under store extension. -/
theorem denoteL_mono {st st' : EStore} (hext : Ext st st') :
    ∀ {u : LIdx} {a : Level}, st.denoteL u = some a → st'.denoteL u = some a := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro a h
    obtain ⟨n, hn, hc, hd⟩ := denoteL_some_inv h
    rw [denoteL_node (hext.lvl u n hn) hc, ← hd]
    apply denoteLNode_congr
    intro c hcin
    obtain ⟨b, hb⟩ := denoteLNode_children_some hd c hcin
    rw [hb, ih c (hc c hcin) hb]

/-- Level-list denotation is stable under store extension. -/
theorem denoteLList_mono {st st' : EStore} (hext : Ext st st') :
    ∀ {us : List LIdx} {ls : List Level},
      denoteLList st.denoteL us = some ls →
      denoteLList st'.denoteL us = some ls := by
  intro us
  induction us with
  | nil => intro ls h; exact h
  | cons u us ih =>
    intro ls h
    simp only [denoteLList, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨l, hl, ls', hls', rfl⟩ := h
    exact ⟨l, denoteL_mono hext hl, ls', ih hls', rfl⟩

/-- Binder-meta denotation is stable under store extension. -/
theorem denoteBM_mono {st st' : EStore} (hext : Ext st st')
    {m : IBinderMeta} {bm : BinderMeta}
    (h : denoteBM st.denoteL m = some bm) :
    denoteBM st'.denoteL m = some bm := by
  obtain ⟨bi, (_ | u)⟩ := m
  · exact h
  · simp only [denoteBM, Option.map_eq_some_iff] at h ⊢
    obtain ⟨l, hl, rfl⟩ := h
    exact ⟨l, denoteL_mono hext hl, rfl⟩

/-- `denoteNode` transports along extension when the children's
denotations transport. -/
theorem denoteNode_mono {st st' : EStore} (hext : Ext st st')
    {den den' : EIdx → Option Expr} {n : ENode} {a : Expr}
    (hden : ∀ c ∈ n.children, ∀ x, den c = some x → den' c = some x)
    (h : denoteNode den st.denoteL st.denoteN n = some a) :
    denoteNode den' st'.denoteL st'.denoteN n = some a := by
  cases n with
  | bvar i => exact h
  | lit l => exact h
  | sort u =>
    simp only [denoteNode, Option.map_eq_some_iff] at h ⊢
    obtain ⟨l, hl, rfl⟩ := h
    exact ⟨l, denoteL_mono hext hl, rfl⟩
  | const nm us =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h ⊢
    obtain ⟨ls, hls, name, hname, rfl⟩ := h
    exact ⟨ls, denoteLList_mono hext hls,
      name, denoteN_mono hext hname, rfl⟩
  | fvar idx nm t =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h ⊢
    obtain ⟨x, hx, name, hname, rfl⟩ := h
    exact ⟨x, hden t (by simp [ENode.children]) x hx,
      name, denoteN_mono hext hname, rfl⟩
  | app f a' =>
    simp only [denoteNode, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨xf, hf, xa, ha, rfl⟩ := h
    exact ⟨xf, hden f (by simp [ENode.children]) _ hf,
      xa, hden a' (by simp [ENode.children]) _ ha, rfl⟩
  | lam nm t b m =>
    simp only [denoteNode, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨xt, ht, xb, hb, bm, hbm, name, hname, rfl⟩ := h
    exact ⟨xt, hden t (by simp [ENode.children]) _ ht,
      xb, hden b (by simp [ENode.children]) _ hb,
      bm, denoteBM_mono hext hbm,
      name, denoteN_mono hext hname, rfl⟩
  | forallE nm t b m =>
    simp only [denoteNode, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨xt, ht, xb, hb, bm, hbm, name, hname, rfl⟩ := h
    exact ⟨xt, hden t (by simp [ENode.children]) _ ht,
      xb, hden b (by simp [ENode.children]) _ hb,
      bm, denoteBM_mono hext hbm,
      name, denoteN_mono hext hname, rfl⟩
  | letE nm t v b =>
    simp only [denoteNode, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h ⊢
    obtain ⟨xt, ht, xv, hv, xb, hb, name, hname, rfl⟩ := h
    exact ⟨xt, hden t (by simp [ENode.children]) _ ht,
      xv, hden v (by simp [ENode.children]) _ hv,
      xb, hden b (by simp [ENode.children]) _ hb,
      name, denoteN_mono hext hname, rfl⟩
  | proj sN j e' =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h ⊢
    obtain ⟨x, hx, name, hname, rfl⟩ := h
    exact ⟨x, hden e' (by simp [ENode.children]) x hx,
      name, denoteN_mono hext hname, rfl⟩

/-- Denotation is stable under store extension (monotonicity). -/
theorem denote_mono {st st' : EStore} (hext : Ext st st') :
    ∀ {i : EIdx} {a : Expr}, st.denote i = some a → st'.denote i = some a := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro a h
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv h
    rw [denote_node (hext.expr i n hn) hc]
    exact denoteNode_mono hext (fun c hcin x hx => ih c (hc c hcin) hx) hd

/-- Stores agreeing on the nodes below `k` denote all indices below `k`
identically (in particular, pushing nodes never changes the denotation
of old indices, not even `none` ones). -/
theorem denoteL_eq_of_lnodes_eq {st st' : EStore}
    (h : st'.lnodes = st.lnodes) : ∀ u, st'.denoteL u = st.denoteL u := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    rw [denoteL.eq_def, denoteL.eq_def, h]
    cases st.lnodes[u]? with
    | none => rfl
    | some n =>
      exact denoteLNode_congr fun c _hc => by
        by_cases hcu : c < u
        · simp only [dif_pos hcu, ih c hcu]
        · simp [dif_neg hcu]

theorem denote_agree {st st' : EStore} {k : Nat}
    (hpre : ∀ j, j < k → st'.nodes[j]? = st.nodes[j]?)
    (hl : st'.lnodes = st.lnodes) (hnm : st'.nnodes = st.nnodes) :
    ∀ i, i < k → st'.denote i = st.denote i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hik
    rw [denote.eq_def, denote.eq_def, hpre i hik]
    cases st.nodes[i]? with
    | none => rfl
    | some n =>
      refine denoteNode_congr' (fun c _hc => ?_)
        (fun u _hu => denoteL_eq_of_lnodes_eq hl u)
        (fun q _hq => denoteN_eq_of_nnodes_eq hnm q)
      by_cases hci : c < i
      · simp only [dif_pos hci]
        exact ih c hci (Nat.lt_trans hci hik)
      · simp [dif_neg hci]

/-- Stores agreeing on the level nodes below `k` denote all level
indices below `k` identically. -/
theorem denoteL_agree {st st' : EStore} {k : Nat}
    (hpre : ∀ v, v < k → st'.lnodes[v]? = st.lnodes[v]?) :
    ∀ u, u < k → st'.denoteL u = st.denoteL u := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro huk
    rw [denoteL.eq_def, denoteL.eq_def, hpre u huk]
    cases st.lnodes[u]? with
    | none => rfl
    | some n =>
      exact denoteLNode_congr fun c _hc => by
        by_cases hcu : c < u
        · simp only [dif_pos hcu]
          exact ih c hcu (Nat.lt_trans hcu huk)
        · simp [dif_neg hcu]

/-- A valid two-tier index (task #64): a tier-one position (the
identity embedding) or a tagged tier-two position. -/
def Valid2 (st : EStore) (i : EIdx) : Prop :=
  i < st.nodes.size ∨ (tierTag ≤ i ∧ i - tierTag < st.tnodes.size)

/-- Reads of a size-zero array. -/
theorem getElem?_size_zero {α : Type} {a : Array α} (h : a.size = 0)
    (j : Nat) : a[j]? = none :=
  Array.getElem?_eq_none (by omega)

/-- The two-tier store invariant (task #64): the tier-one clauses of
the pre-tier invariant verbatim (every node's children strictly below
its own index, expression nodes' level references in range, each
cons-table exactly the graph of its node table, eager derived-field
arrays congruent and satisfying their recurrences) plus the tier
discipline: flag-off interns append tier one, flag-on interns append
tier two, so tier one is frozen under flag-on operation and tier-one
nodes never reference tier-two indices.  The tag split is carried as
the invariant `flag_bound` — established once by `enableTierTwo`'s
guard (validate-at-insertion, task #42) — so the high-bit index
disambiguation is a theorem (`TWF.tierOne_lt_tag`,
`TWF.getNode_tierTwo`), never an appeal to practical
unreachability. -/
structure TWF (st : EStore) : Prop where
  children_lt : ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n →
    ∀ c ∈ n.children, c < i
  cons_graph : ∀ (n : ENode) (i : EIdx), st.cons[n]? = some i ↔ st.nodes[i]? = some n
  levels_lt : ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n →
    ∀ u ∈ n.levels, u < st.lnodes.size
  lchildren_lt : ∀ (u : LIdx) (m : LNode), st.lnodes[u]? = some m →
    ∀ c ∈ m.children, c < u
  lcons_graph : ∀ (m : LNode) (u : LIdx), st.lcons[m]? = some u ↔ st.lnodes[u]? = some m
  /-- The eager derived-field arrays are congruent with `nodes`
  (task #87). -/
  bvarBs_size : st.bvarBs.size = st.nodes.size
  fvarBs_size : st.fvarBs.size = st.nodes.size
  /-- Each node's bound entry satisfies the recurrence over its
  children's entries. -/
  bvarBs_spec : ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n →
    st.bvarBs[i]? = some (n.bvarBoundOf st.bvarBs)
  /-- Each node's range entry satisfies the recurrence over its
  children's entries. -/
  fvarBs_spec : ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n →
    st.fvarBs[i]? = some (n.fvarRangeOf st.fvarBs)
  /-- The eager level-side has-param array is congruent with
  `lnodes`. -/
  lparamBs_size : st.lparamBs.size = st.lnodes.size
  /-- Each level node's has-param entry satisfies the recurrence over
  its children's entries. -/
  lparamBs_spec : ∀ (u : LIdx) (m : LNode), st.lnodes[u]? = some m →
    st.lparamBs[u]? = some (m.hasParamOf st.lparamBs)
  /-- The eager has-level-param array is congruent with `nodes`. -/
  eparamBs_size : st.eparamBs.size = st.nodes.size
  /-- Each node's has-level-param entry satisfies the recurrence over
  the children's and level entries. -/
  eparamBs_spec : ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n →
    st.eparamBs[i]? = some (n.hasLParamOf st.eparamBs st.lparamBs)
  /-- Expression nodes' name references are in range (task #88). -/
  names_lt : ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n →
    ∀ p ∈ n.names, p < st.nnodes.size
  /-- Name-node prefixes are strictly below their own index
  (task #88). -/
  nchildren_lt : ∀ (i : NIdx) (m : NNode), st.nnodes[i]? = some m →
    ∀ c ∈ m.children, c < i
  /-- The name cons-table is exactly the graph of the name node
  table. -/
  ncons_graph : ∀ (m : NNode) (i : NIdx),
    st.ncons[m]? = some i ↔ st.nnodes[i]? = some m
  /-- The eager readback array is congruent with `nnodes`
  (task #88). -/
  rbNames_size : st.rbNames.size = st.nnodes.size
  /-- Each name node's readback entry satisfies the recurrence over
  its prefix's entry. -/
  rbNames_spec : ∀ (i : NIdx) (m : NNode), st.nnodes[i]? = some m →
    st.rbNames[i]? = some (m.nameOf st.rbNames)
  /-- The tag bound (task #64): while the flag is on, the frozen
  tier-one table sits below the tag, so `i < tierTag` means tier one
  and `tierTag ≤ i` means tier two (offset `i - tierTag`, recovered
  uniquely because `Nat` does not wrap — tier two needs no bound).
  Established by `enableTierTwo`'s guard. -/
  flag_bound : st.tierTwo = true → st.nodes.size ≤ tierTag
  /-- Flag off means tier two is empty (interns only append tier two
  while the flag is on, and `truncateTierTwo` clears both). -/
  toff_tnil : st.tierTwo = false → st.tnodes.size = 0
  /-- Tier-two nodes reference tier-one indices (frozen, so stable) or
  strictly earlier tier-two indices. -/
  t_children_lt : ∀ (j : Nat) (n : ENode), st.tnodes[j]? = some n →
    ∀ c ∈ n.children, c < st.nodes.size ∨ (tierTag ≤ c ∧ c - tierTag < j)
  /-- Tier-two nodes' level references are in (single-tier) range. -/
  t_levels_lt : ∀ (j : Nat) (n : ENode), st.tnodes[j]? = some n →
    ∀ u ∈ n.levels, u < st.lnodes.size
  /-- Tier-two nodes' name references are in (single-tier) range. -/
  t_names_lt : ∀ (j : Nat) (n : ENode), st.tnodes[j]? = some n →
    ∀ p ∈ n.names, p < st.nnodes.size
  /-- The tier-two cons-table is exactly the graph of `tnodes` under
  tagged indices. -/
  t_cons_graph : ∀ (n : ENode) (i : EIdx), st.tcons[n]? = some i ↔
    (tierTag ≤ i ∧ st.tnodes[i - tierTag]? = some n)
  /-- Cross-tier canonicity: a node in the tier-two cons-table is not
  in the (frozen) tier-one one — `internT` probes tier one first. -/
  t_cons_fresh : ∀ (n : ENode) (i : EIdx), st.tcons[n]? = some i →
    st.cons[n]? = none
  /-- The tier-two derived-field arrays are congruent with `tnodes`. -/
  t_bvarBs_size : st.tbvarBs.size = st.tnodes.size
  t_fvarBs_size : st.tfvarBs.size = st.tnodes.size
  t_eparamBs_size : st.teparamBs.size = st.tnodes.size
  /-- Each tier-two node's bound entry satisfies the tier-blind
  recurrence over the dispatching reads. -/
  t_bvarBs_spec : ∀ (j : Nat) (n : ENode), st.tnodes[j]? = some n →
    st.tbvarBs[j]? = some (st.nodeBvarBound n)
  t_fvarBs_spec : ∀ (j : Nat) (n : ENode), st.tnodes[j]? = some n →
    st.tfvarBs[j]? = some (st.nodeFvarRange n)
  t_eparamBs_spec : ∀ (j : Nat) (n : ENode), st.tnodes[j]? = some n →
    st.teparamBs[j]? = some (st.nodeHasLParam n)

/-- The (flag-off) store invariant: the two-tier invariant `TWF` plus
the flag being off — every store the pre-tier interface produces.  The
pre-tier clauses and lemma statements are unchanged (`hwf.children_lt`
etc. project through `toTWF`), so downstream consumers are untouched
(task #64). -/
structure WF (st : EStore) : Prop extends TWF st where
  /-- The tier-two flag is off (so, with `toff_tnil`, tier two is
  empty and every dispatching read reduces to its pre-tier form). -/
  tier_off : st.tierTwo = false

/-- Flag off (with the tier discipline) means no tier-two nodes. -/
theorem TWF.toff_tnodes_none {st : EStore} (h : st.TWF)
    (hoff : st.tierTwo = false) : ∀ j : Nat, st.tnodes[j]? = none :=
  getElem?_size_zero (h.toff_tnil hoff)

/-- Flag off means the tier-two cons-table is semantically empty. -/
theorem TWF.toff_tcons_none {st : EStore} (h : st.TWF)
    (hoff : st.tierTwo = false) : ∀ n : ENode, st.tcons[n]? = none := by
  intro n
  cases hmi : st.tcons[n]? with
  | none => rfl
  | some i =>
    have := ((h.t_cons_graph n i).mp hmi).2
    rw [h.toff_tnodes_none hoff] at this
    cases this

@[inherit_doc TWF.toff_tnodes_none]
theorem WF.tnodes_none {st : EStore} (hwf : st.WF) :
    ∀ j : Nat, st.tnodes[j]? = none :=
  hwf.toff_tnodes_none hwf.tier_off

@[inherit_doc TWF.toff_tcons_none]
theorem WF.tcons_none {st : EStore} (hwf : st.WF) :
    ∀ n : ENode, st.tcons[n]? = none :=
  hwf.toff_tcons_none hwf.tier_off

/-- On a well-formed (flag-off) store the tier-two derived arrays are
empty. -/
theorem WF.tbvarBs_nil {st : EStore} (hwf : st.WF) : st.tbvarBs.size = 0 :=
  hwf.t_bvarBs_size.trans (hwf.toff_tnil hwf.tier_off)

theorem WF.tfvarBs_nil {st : EStore} (hwf : st.WF) : st.tfvarBs.size = 0 :=
  hwf.t_fvarBs_size.trans (hwf.toff_tnil hwf.tier_off)

theorem WF.teparamBs_nil {st : EStore} (hwf : st.WF) : st.teparamBs.size = 0 :=
  hwf.t_eparamBs_size.trans (hwf.toff_tnil hwf.tier_off)

theorem empty_twf : TWF EStore.empty := by
  constructor
  · intro i n h
    simp [EStore.empty] at h
  · intro n i
    simp [EStore.empty]
  · intro i n h
    simp [EStore.empty] at h
  · intro u m h
    simp [EStore.empty] at h
  · intro m u
    simp [EStore.empty]
  · simp [EStore.empty]
  · simp [EStore.empty]
  · intro i n h
    simp [EStore.empty] at h
  · intro i n h
    simp [EStore.empty] at h
  · simp [EStore.empty]
  · intro u m h
    simp [EStore.empty] at h
  · simp [EStore.empty]
  · intro i n h
    simp [EStore.empty] at h
  · intro i n h
    simp [EStore.empty] at h
  · intro i n h
    simp [EStore.empty] at h
  · intro m i
    simp [EStore.empty]
  · simp [EStore.empty]
  · intro i m h
    simp [EStore.empty] at h
  · intro h
    simp [EStore.empty]
  · intro _
    simp [EStore.empty]
  · intro j n h
    simp [EStore.empty] at h
  · intro j n h
    simp [EStore.empty] at h
  · intro j n h
    simp [EStore.empty] at h
  · intro n i
    simp [EStore.empty]
  · intro n i h
    simp [EStore.empty] at h
  · simp [EStore.empty]
  · simp [EStore.empty]
  · simp [EStore.empty]
  · intro j n h
    simp [EStore.empty] at h
  · intro j n h
    simp [EStore.empty] at h
  · intro j n h
    simp [EStore.empty] at h

theorem empty_wf : WF EStore.empty := ⟨empty_twf, rfl⟩

/-! ## `intern` -/

/-- `getD` reads below the size are stable under `push`. -/
theorem getD_push_of_lt {α : Type} {arr : Array α} {x d : α} {c : Nat}
    (h : c < arr.size) : (arr.push x).getD c d = arr.getD c d := by
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?,
    Array.getElem?_push, if_neg (Nat.ne_of_lt h)]

/-- The derived-field recurrences read only the children's entries. -/
theorem _root_.Setlec.ENode.bvarBoundOf_congr {bs bs' : Array Nat}
    {n : ENode} (h : ∀ c ∈ n.children, bs.getD c 0 = bs'.getD c 0) :
    n.bvarBoundOf bs = n.bvarBoundOf bs' := by
  cases n <;>
    simp_all [ENode.bvarBoundOf, ENode.children]

@[inherit_doc ENode.bvarBoundOf_congr]
theorem _root_.Setlec.ENode.fvarRangeOf_congr {bs bs' : Array Nat}
    {n : ENode} (h : ∀ c ∈ n.children, bs.getD c 0 = bs'.getD c 0) :
    n.fvarRangeOf bs = n.fvarRangeOf bs' := by
  cases n <;>
    simp_all [ENode.fvarRangeOf, ENode.children]

@[inherit_doc ENode.bvarBoundOf_congr]
theorem _root_.Setlec.LNode.hasParamOf_congr {bs bs' : Array Bool}
    {n : LNode} (h : ∀ c ∈ n.children, bs.getD c false = bs'.getD c false) :
    n.hasParamOf bs = n.hasParamOf bs' := by
  cases n <;>
    simp_all [LNode.hasParamOf, LNode.children]

/-- The has-level-param recurrence reads only the children's and the
node's level entries. -/
theorem _root_.Setlec.ENode.hasLParamOf_congr {ebs ebs' lbs lbs' : Array Bool}
    {n : ENode}
    (hc : ∀ c ∈ n.children, ebs.getD c false = ebs'.getD c false)
    (hl : ∀ u ∈ n.levels, lbs.getD u false = lbs'.getD u false) :
    n.hasLParamOf ebs lbs = n.hasLParamOf ebs' lbs' := by
  cases n with
  | const nm us =>
    simp only [ENode.hasLParamOf]
    have main : ∀ (l : List LIdx),
        (∀ u ∈ l, lbs.getD u false = lbs'.getD u false) →
        l.any (lbs.getD · false) = l.any (lbs'.getD · false) := by
      intro l hml
      induction l with
      | nil => rfl
      | cons u t iht =>
        simp only [List.any_cons]
        rw [hml u (by simp), iht fun v hv => hml v (by simp [hv])]
    exact main us fun u hu => hl u (by simpa [ENode.levels] using hu)
  | lam nm ty body m =>
    obtain ⟨bi, cod⟩ := m
    cases cod <;>
      simp_all [ENode.hasLParamOf, ENode.children, ENode.levels]
  | forallE nm ty body m =>
    obtain ⟨bi, cod⟩ := m
    cases cod <;>
      simp_all [ENode.hasLParamOf, ENode.children, ENode.levels]
  | _ =>
    simp_all [ENode.hasLParamOf, ENode.children, ENode.levels]

/-- The readback recurrence reads only the prefix's entry. -/
theorem _root_.Setlec.NNode.nameOf_congr {rs rs' : Array Name}
    {n : NNode}
    (h : ∀ c ∈ n.children, rs.getD c .anonymous = rs'.getD c .anonymous) :
    n.nameOf rs = n.nameOf rs' := by
  cases n <;> simp_all [NNode.nameOf, NNode.children]

/-! ### Tier-blind recurrence congruence (task #64)

The tier-two derived entries satisfy the tier-blind recurrences
(`nodeBvarBound` etc.), which read only the children's (and level
references') dispatching reads — the congruence lemmas below, plus the
stability of a dispatching read under a tier-two push
(`tierRead_push_stable`), are all the tier-two spec-preservation
proofs need. -/

/-- `nodeBvarBound` reads only the children's dispatching entries. -/
theorem nodeBvarBound_congr {st st' : EStore} {n : ENode}
    (h : ∀ c ∈ n.children, st'.bvarBoundD c = st.bvarBoundD c) :
    st'.nodeBvarBound n = st.nodeBvarBound n := by
  cases n <;> simp_all [nodeBvarBound, ENode.children]

@[inherit_doc nodeBvarBound_congr]
theorem nodeFvarRange_congr {st st' : EStore} {n : ENode}
    (h : ∀ c ∈ n.children, st'.fvarRangeD c = st.fvarRangeD c) :
    st'.nodeFvarRange n = st.nodeFvarRange n := by
  cases n <;> simp_all [nodeFvarRange, ENode.children]

/-- `nodeHasLParam` reads only the children's and the node's level
entries. -/
theorem nodeHasLParam_congr {st st' : EStore} {n : ENode}
    (hc : ∀ c ∈ n.children, st'.ehasParamD c = st.ehasParamD c)
    (hl : ∀ u ∈ n.levels, st'.lhasParamD u = st.lhasParamD u) :
    st'.nodeHasLParam n = st.nodeHasLParam n := by
  cases n with
  | const nm us =>
    simp only [nodeHasLParam]
    have main : ∀ (l : List LIdx),
        (∀ u ∈ l, st'.lhasParamD u = st.lhasParamD u) →
        l.any st'.lhasParamD = l.any st.lhasParamD := by
      intro l hml
      induction l with
      | nil => rfl
      | cons u t iht =>
        simp only [List.any_cons]
        rw [hml u (by simp), iht fun v hv => hml v (by simp [hv])]
    exact main us fun u hu => hl u (by simpa [ENode.levels] using hu)
  | lam nm ty body m =>
    obtain ⟨bi, cod⟩ := m
    cases cod <;>
      simp_all [nodeHasLParam, ENode.children, ENode.levels]
  | forallE nm ty body m =>
    obtain ⟨bi, cod⟩ := m
    cases cod <;>
      simp_all [nodeHasLParam, ENode.children, ENode.levels]
  | _ =>
    simp_all [nodeHasLParam, ENode.children, ENode.levels]

/-- A dispatching tier read is stable under a tier-two push at any
valid index (the tier-one branch is untouched; a tagged index reads
below the pushed slot).  `hbound` is the tag bound: it keeps a tagged
index out of the tier-one branch. -/
theorem tierRead_push_stable {α : Type} {bs tbs : Array α} {x d : α}
    (hbound : bs.size ≤ tierTag) {c : Nat}
    (hv : c < bs.size ∨ (tierTag ≤ c ∧ c - tierTag < tbs.size)) :
    (if h : c < bs.size then bs[c] else (tbs.push x).getD (c - tierTag) d)
      = (if h : c < bs.size then bs[c] else tbs.getD (c - tierTag) d) := by
  rcases hv with hlt | ⟨htag, hoff⟩
  · rw [dif_pos hlt, dif_pos hlt]
  · have hge : ¬ c < bs.size := by omega
    rw [dif_neg hge, dif_neg hge]
    exact getD_push_of_lt hoff

/-- `internP` with the store destructuring (an RC optimization)
eliminated. -/
theorem internP_eq (st : EStore) (n : ENode) :
    st.internP n = match st.cons[n]? with
      | some i => (i, st)
      | none =>
        (st.nodes.size, ⟨st.nodes.push n, st.cons.insert n st.nodes.size,
          st.lnodes, st.lcons,
          st.bvarBs.push (n.bvarBoundOf st.bvarBs),
          st.fvarBs.push (n.fvarRangeOf st.fvarBs), st.lparamBs,
          st.eparamBs.push (n.hasLParamOf st.eparamBs st.lparamBs),
          st.nnodes, st.ncons, st.rbNames, st.tierTwo, st.tnodes,
          st.tcons, st.tbvarBs, st.tfvarBs, st.teparamBs⟩) := by
  obtain ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
    nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs, tfvarBs,
    teparamBs⟩ := st
  rfl

/-- `internT` with the store destructuring eliminated. -/
theorem internT_eq (st : EStore) (n : ENode) :
    st.internT n = match st.cons[n]? with
      | some i => (i, st)
      | none =>
        match st.tcons[n]? with
        | some i => (i, st)
        | none =>
          (tierTag + st.tnodes.size,
            ⟨st.nodes, st.cons, st.lnodes, st.lcons, st.bvarBs,
              st.fvarBs, st.lparamBs, st.eparamBs, st.nnodes, st.ncons,
              st.rbNames, st.tierTwo, st.tnodes.push n,
              st.tcons.insert n (tierTag + st.tnodes.size),
              st.tbvarBs.push (st.nodeBvarBound n),
              st.tfvarBs.push (st.nodeFvarRange n),
              st.teparamBs.push (st.nodeHasLParam n)⟩) := by
  obtain ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
    nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs, tfvarBs,
    teparamBs⟩ := st
  rfl

/-- With the flag off, `intern` is the tier-one intern. -/
theorem intern_off {st : EStore} (hoff : st.tierTwo = false) (n : ENode) :
    st.intern n = st.internP n := by
  simp [intern, hoff]

/-- With the flag on, `intern` is the tier-two intern. -/
theorem intern_on {st : EStore} (hflag : st.tierTwo = true) (n : ENode) :
    st.intern n = st.internT n := by
  simp [intern, hflag]

theorem internP_ext (st : EStore) (n : ENode) : Ext st (st.internP n).2 := by
  refine ⟨fun i m h => ?_, fun u m h => ?_, fun i m h => ?_⟩
  · rw [internP_eq]
    split
    · exact h
    · have : i < st.nodes.size := (Array.getElem?_eq_some_iff.mp h).1
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt this)]
      exact h
  · rw [internP_eq]
    split
    · exact h
    · exact h
  · rw [internP_eq]
    split
    · exact h
    · exact h

/-- `internT` leaves every tier-one table unchanged. -/
theorem internT_nodes (st : EStore) (n : ENode) :
    (st.internT n).2.nodes = st.nodes := by
  rw [internT_eq]
  split
  · rfl
  · split <;> rfl

@[inherit_doc internT_nodes]
theorem internT_lnodes (st : EStore) (n : ENode) :
    (st.internT n).2.lnodes = st.lnodes := by
  rw [internT_eq]
  split
  · rfl
  · split <;> rfl

@[inherit_doc internT_nodes]
theorem internT_nnodes (st : EStore) (n : ENode) :
    (st.internT n).2.nnodes = st.nnodes := by
  rw [internT_eq]
  split
  · rfl
  · split <;> rfl

/-- `internT` touches no tier-one table. -/
theorem internT_ext (st : EStore) (n : ENode) : Ext st (st.internT n).2 := by
  refine ⟨fun i m h => ?_, fun u m h => ?_, fun i m h => ?_⟩
  · rw [internT_nodes]
    exact h
  · rw [internT_lnodes]
    exact h
  · rw [internT_nnodes]
    exact h

theorem intern_ext (st : EStore) (n : ENode) : Ext st (st.intern n).2 := by
  unfold intern
  split
  · exact internT_ext st n
  · exact internP_ext st n

/-- Interning stores the node at the returned index. -/
theorem intern_node {st : EStore} {n : ENode} (hwf : st.WF) :
    (st.intern n).2.nodes[(st.intern n).1]? = some n := by
  rw [intern_off hwf.tier_off, internP_eq]
  split
  · rename_i i h
    exact (hwf.cons_graph n i).mp h
  · rw [Array.getElem?_push, if_pos rfl]

/-- The returned index is in range of the extended store. -/
theorem intern_lt_size {st : EStore} {n : ENode} (hwf : st.WF) :
    (st.intern n).1 < (st.intern n).2.nodes.size :=
  (Array.getElem?_eq_some_iff.mp (intern_node hwf)).1

/-- `intern` preserves the invariant when the node's children are
already-stored indices and its level references are in range. -/
theorem intern_wf {st : EStore} {n : ENode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nodes.size)
    (hlv : ∀ u ∈ n.levels, u < st.lnodes.size)
    (hnm : ∀ p ∈ n.names, p < st.nnodes.size) : (st.intern n).2.WF := by
  rw [intern_off hwf.tier_off, internP_eq]
  split
  · exact hwf
  · rename_i hmiss
    refine ⟨?_, hwf.tier_off⟩
    constructor
    · intro i m h c hcin
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        exact hc c hcin
      · exact hwf.children_lt i m h c hcin
    · intro m i
      constructor
      · intro h
        rw [Std.HashMap.getElem?_insert] at h
        by_cases hnm : n = m
        · subst hnm
          simp only [BEq.rfl, if_pos] at h
          cases h
          rw [Array.getElem?_push, if_pos rfl]
        · rw [if_neg (by simpa using hnm)] at h
          have h' := (hwf.cons_graph m i).mp h
          have hi : i < st.nodes.size := (Array.getElem?_eq_some_iff.mp h').1
          rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hi)]
          exact h'
      · intro h
        rw [Array.getElem?_push] at h
        rw [Std.HashMap.getElem?_insert]
        split at h
        · cases h
          subst_eqs
          simp
        · have hne : ¬ n = m := by
            rintro rfl
            have hcontra := (hwf.cons_graph n i).mpr h
            rw [hmiss] at hcontra
            simp at hcontra
          rw [if_neg (by simpa using hne)]
          exact (hwf.cons_graph m i).mpr h
    · intro i m h u huin
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        exact hlv u huin
      · exact hwf.levels_lt i m h u huin
    · exact hwf.lchildren_lt
    · exact hwf.lcons_graph
    · simpa using hwf.bvarBs_size
    · simpa using hwf.fvarBs_size
    · intro i m h
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        rw [Array.getElem?_push, hwf.bvarBs_size, if_pos rfl]
        refine congrArg some (ENode.bvarBoundOf_congr fun c hcin => ?_)
        exact (getD_push_of_lt (hwf.bvarBs_size ▸ hc c hcin)).symm
      · rename_i hne
        have hi : i < st.nodes.size := by
          rcases Array.getElem?_eq_some_iff.mp h with ⟨hlt, -⟩
          exact hlt
        rw [Array.getElem?_push, if_neg (hwf.bvarBs_size ▸ Nat.ne_of_lt hi),
          hwf.bvarBs_spec i m h]
        refine congrArg some (ENode.bvarBoundOf_congr fun c hcin => ?_)
        exact (getD_push_of_lt (hwf.bvarBs_size ▸
          Nat.lt_trans (hwf.children_lt i m h c hcin) hi)).symm
    · intro i m h
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        rw [Array.getElem?_push, hwf.fvarBs_size, if_pos rfl]
        refine congrArg some (ENode.fvarRangeOf_congr fun c hcin => ?_)
        exact (getD_push_of_lt (hwf.fvarBs_size ▸ hc c hcin)).symm
      · rename_i hne
        have hi : i < st.nodes.size := by
          rcases Array.getElem?_eq_some_iff.mp h with ⟨hlt, -⟩
          exact hlt
        rw [Array.getElem?_push, if_neg (hwf.fvarBs_size ▸ Nat.ne_of_lt hi),
          hwf.fvarBs_spec i m h]
        refine congrArg some (ENode.fvarRangeOf_congr fun c hcin => ?_)
        exact (getD_push_of_lt (hwf.fvarBs_size ▸
          Nat.lt_trans (hwf.children_lt i m h c hcin) hi)).symm
    · exact hwf.lparamBs_size
    · exact hwf.lparamBs_spec
    · simpa using hwf.eparamBs_size
    · intro i m h
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        rw [Array.getElem?_push, hwf.eparamBs_size, if_pos rfl]
        refine congrArg some
          (ENode.hasLParamOf_congr (fun c hcin => ?_) (fun u _ => rfl))
        exact (getD_push_of_lt (hwf.eparamBs_size ▸ hc c hcin)).symm
      · have hi : i < st.nodes.size := by
          rcases Array.getElem?_eq_some_iff.mp h with ⟨hlt, -⟩
          exact hlt
        rw [Array.getElem?_push, if_neg (hwf.eparamBs_size ▸ Nat.ne_of_lt hi),
          hwf.eparamBs_spec i m h]
        refine congrArg some
          (ENode.hasLParamOf_congr (fun c hcin => ?_) (fun u _ => rfl))
        exact (getD_push_of_lt (hwf.eparamBs_size ▸
          Nat.lt_trans (hwf.children_lt i m h c hcin) hi)).symm
    · intro i m h p hpin
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        exact hnm p hpin
      · exact hwf.names_lt i m h p hpin
    · exact hwf.nchildren_lt
    · exact hwf.ncons_graph
    · exact hwf.rbNames_size
    · exact hwf.rbNames_spec
    · exact fun hflag => absurd hflag (by simp [hwf.tier_off])
    · exact fun _ => hwf.toff_tnil hwf.tier_off
    · intro j m hj
      simp [hwf.tnodes_none] at hj
    · intro j m hj
      simp [hwf.tnodes_none] at hj
    · intro j m hj
      simp [hwf.tnodes_none] at hj
    · exact hwf.t_cons_graph
    · intro m i hmi
      simp [hwf.tcons_none] at hmi
    · exact hwf.t_bvarBs_size
    · exact hwf.t_fvarBs_size
    · exact hwf.t_eparamBs_size
    · intro j m hj
      simp [hwf.tnodes_none] at hj
    · intro j m hj
      simp [hwf.tnodes_none] at hj
    · intro j m hj
      simp [hwf.tnodes_none] at hj

/-- Interning a node whose children are already stored: the result
denotes the node's denotation over the *old* store. -/
theorem intern_denote {st : EStore} {n : ENode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nodes.size) :
    (st.intern n).2.denote (st.intern n).1
      = denoteNode st.denote st.denoteL st.denoteN n := by
  have hn := intern_node (n := n) hwf
  rw [intern_off hwf.tier_off, internP_eq] at hn ⊢
  split at hn
  · rename_i i h
    rw [denote_node hn (hwf.children_lt _ _ hn)]
  · rename_i hmiss
    have hagree : ∀ j, j < st.nodes.size →
        (⟨st.nodes.push n, st.cons.insert n st.nodes.size,
          st.lnodes, st.lcons,
          st.bvarBs.push (n.bvarBoundOf st.bvarBs),
          st.fvarBs.push (n.fvarRangeOf st.fvarBs), st.lparamBs,
          st.eparamBs.push (n.hasLParamOf st.eparamBs st.lparamBs),
          st.nnodes, st.ncons, st.rbNames, st.tierTwo, st.tnodes,
          st.tcons, st.tbvarBs, st.tfvarBs, st.teparamBs⟩
          : EStore).denote j
          = st.denote j := by
      refine denote_agree (fun j hj => ?_) rfl rfl
      simp [Array.getElem?_push, Nat.ne_of_lt hj]
    rw [denote_node hn hc]
    exact denoteNode_congr' (fun c hcin => hagree c (hc c hcin))
      (fun u _ => denoteL_eq_of_lnodes_eq
        (st' := (⟨st.nodes.push n, st.cons.insert n st.nodes.size,
          st.lnodes, st.lcons,
          st.bvarBs.push (n.bvarBoundOf st.bvarBs),
          st.fvarBs.push (n.fvarRangeOf st.fvarBs), st.lparamBs,
          st.eparamBs.push (n.hasLParamOf st.eparamBs st.lparamBs),
          st.nnodes, st.ncons, st.rbNames, st.tierTwo, st.tnodes,
          st.tcons, st.tbvarBs, st.tfvarBs, st.teparamBs⟩
          : EStore)) (st := st)
        rfl u)
      (fun q _ => denoteN_eq_of_nnodes_eq
        (st' := (⟨st.nodes.push n, st.cons.insert n st.nodes.size,
          st.lnodes, st.lcons,
          st.bvarBs.push (n.bvarBoundOf st.bvarBs),
          st.fvarBs.push (n.fvarRangeOf st.fvarBs), st.lparamBs,
          st.eparamBs.push (n.hasLParamOf st.eparamBs st.lparamBs),
          st.nnodes, st.ncons, st.rbNames, st.tierTwo, st.tnodes,
          st.tcons, st.tbvarBs, st.tfvarBs, st.teparamBs⟩
          : EStore)) (st := st)
        rfl q)

/-! ## `internL` / `internLevel`: the level round-trip -/

/-- `internL` with the store destructuring eliminated. -/
theorem internL_eq (st : EStore) (n : LNode) :
    st.internL n = match st.lcons[n]? with
      | some i => (i, st)
      | none =>
        (st.lnodes.size, ⟨st.nodes, st.cons, st.lnodes.push n,
          st.lcons.insert n st.lnodes.size, st.bvarBs, st.fvarBs,
          st.lparamBs.push (n.hasParamOf st.lparamBs), st.eparamBs,
          st.nnodes, st.ncons, st.rbNames, st.tierTwo, st.tnodes,
          st.tcons, st.tbvarBs, st.tfvarBs, st.teparamBs⟩) := by
  obtain ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
    nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs, tfvarBs,
    teparamBs⟩ := st
  rfl

theorem internL_ext (st : EStore) (n : LNode) : Ext st (st.internL n).2 := by
  refine ⟨fun i m h => ?_, fun u m h => ?_, fun i m h => ?_⟩
  · rw [internL_eq]
    split
    · exact h
    · exact h
  · rw [internL_eq]
    split
    · exact h
    · have : u < st.lnodes.size := (Array.getElem?_eq_some_iff.mp h).1
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt this)]
      exact h
  · rw [internL_eq]
    split
    · exact h
    · exact h

/-- Interning a level node stores it at the returned index. -/
theorem internL_node {st : EStore} {n : LNode} (hwf : st.WF) :
    (st.internL n).2.lnodes[(st.internL n).1]? = some n := by
  rw [internL_eq]
  split
  · rename_i i h
    exact (hwf.lcons_graph n i).mp h
  · rw [Array.getElem?_push, if_pos rfl]

theorem internL_lt_size {st : EStore} {n : LNode} (hwf : st.WF) :
    (st.internL n).1 < (st.internL n).2.lnodes.size :=
  (Array.getElem?_eq_some_iff.mp (internL_node hwf)).1

/-- `internL` preserves the two-tier invariant when the node's
children are already-stored level indices (levels are single-tier;
the tier-two clauses only see the level table grow). -/
theorem internL_twf {st : EStore} {n : LNode} (hwf : st.TWF)
    (hc : ∀ c ∈ n.children, c < st.lnodes.size) : (st.internL n).2.TWF := by
  rw [internL_eq]
  split
  · exact hwf
  · rename_i hmiss
    constructor
    · exact hwf.children_lt
    · exact hwf.cons_graph
    · intro i m h u huin
      exact Nat.lt_trans (hwf.levels_lt i m h u huin) (by simp)
    · intro u m h c hcin
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        exact hc c hcin
      · exact hwf.lchildren_lt u m h c hcin
    · intro m u
      constructor
      · intro h
        rw [Std.HashMap.getElem?_insert] at h
        by_cases hnm : n = m
        · subst hnm
          simp only [BEq.rfl, if_pos] at h
          cases h
          rw [Array.getElem?_push, if_pos rfl]
        · rw [if_neg (by simpa using hnm)] at h
          have h' := (hwf.lcons_graph m u).mp h
          have hu : u < st.lnodes.size := (Array.getElem?_eq_some_iff.mp h').1
          rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hu)]
          exact h'
      · intro h
        rw [Array.getElem?_push] at h
        rw [Std.HashMap.getElem?_insert]
        split at h
        · cases h
          subst_eqs
          simp
        · have hne : ¬ n = m := by
            rintro rfl
            have hcontra := (hwf.lcons_graph n u).mpr h
            rw [hmiss] at hcontra
            simp at hcontra
          rw [if_neg (by simpa using hne)]
          exact (hwf.lcons_graph m u).mpr h
    · exact hwf.bvarBs_size
    · exact hwf.fvarBs_size
    · exact hwf.bvarBs_spec
    · exact hwf.fvarBs_spec
    · simpa using hwf.lparamBs_size
    · intro u m h
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        rw [Array.getElem?_push, hwf.lparamBs_size, if_pos rfl]
        refine congrArg some (LNode.hasParamOf_congr fun c hcin => ?_)
        exact (getD_push_of_lt (hwf.lparamBs_size ▸ hc c hcin)).symm
      · have hu : u < st.lnodes.size := by
          rcases Array.getElem?_eq_some_iff.mp h with ⟨hlt, -⟩
          exact hlt
        rw [Array.getElem?_push, if_neg (hwf.lparamBs_size ▸ Nat.ne_of_lt hu),
          hwf.lparamBs_spec u m h]
        refine congrArg some (LNode.hasParamOf_congr fun c hcin => ?_)
        exact (getD_push_of_lt (hwf.lparamBs_size ▸
          Nat.lt_trans (hwf.lchildren_lt u m h c hcin) hu)).symm
    · exact hwf.eparamBs_size
    · intro i m h
      rw [hwf.eparamBs_spec i m h]
      refine congrArg some
        (ENode.hasLParamOf_congr (fun c _ => rfl) (fun u hu => ?_))
      exact (getD_push_of_lt (hwf.lparamBs_size ▸
        hwf.levels_lt i m h u hu)).symm
    · exact hwf.names_lt
    · exact hwf.nchildren_lt
    · exact hwf.ncons_graph
    · exact hwf.rbNames_size
    · exact hwf.rbNames_spec
    · exact hwf.flag_bound
    · exact hwf.toff_tnil
    · exact hwf.t_children_lt
    · intro j m hj u hu
      exact Nat.lt_trans (hwf.t_levels_lt j m hj u hu) (by simp)
    · exact hwf.t_names_lt
    · exact hwf.t_cons_graph
    · exact hwf.t_cons_fresh
    · exact hwf.t_bvarBs_size
    · exact hwf.t_fvarBs_size
    · exact hwf.t_eparamBs_size
    · exact hwf.t_bvarBs_spec
    · exact hwf.t_fvarBs_spec
    · intro j m hj
      rw [hwf.t_eparamBs_spec j m hj]
      refine congrArg some
        (nodeHasLParam_congr (fun c _ => rfl) (fun u hu => ?_))
      show st.lparamBs.getD u false
          = (st.lparamBs.push (n.hasParamOf st.lparamBs)).getD u false
      exact (getD_push_of_lt
        (hwf.lparamBs_size ▸ hwf.t_levels_lt j m hj u hu)).symm

/-- `internL` never touches the flag. -/
theorem internL_tierTwo (st : EStore) (n : LNode) :
    (st.internL n).2.tierTwo = st.tierTwo := by
  rw [internL_eq]
  split <;> rfl

/-- `internL` preserves the invariant when the node's children are
already-stored level indices. -/
theorem internL_wf {st : EStore} {n : LNode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.lnodes.size) : (st.internL n).2.WF :=
  ⟨internL_twf hwf.toTWF hc, (internL_tierTwo st n).trans hwf.tier_off⟩

/-- Interning a level node whose children are already stored: the
result denotes the node's denotation over the *old* store. -/
theorem internL_denoteL {st : EStore} {n : LNode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.lnodes.size) :
    (st.internL n).2.denoteL (st.internL n).1
      = denoteLNode st.denoteL n := by
  have hn := internL_node (n := n) hwf
  rw [internL_eq] at hn ⊢
  split at hn
  · rename_i i h
    rw [denoteL_node hn (hwf.lchildren_lt _ _ hn)]
  · rename_i hmiss
    have hagree : ∀ j, j < st.lnodes.size →
        (⟨st.nodes, st.cons, st.lnodes.push n,
          st.lcons.insert n st.lnodes.size, st.bvarBs, st.fvarBs,
          st.lparamBs.push (n.hasParamOf st.lparamBs), st.eparamBs,
          st.nnodes, st.ncons, st.rbNames, st.tierTwo, st.tnodes,
          st.tcons, st.tbvarBs, st.tfvarBs, st.teparamBs⟩
          : EStore).denoteL j
          = st.denoteL j := by
      apply denoteL_agree
      intro j hj
      simp [Array.getElem?_push, Nat.ne_of_lt hj]
    rw [denoteL_node hn hc]
    exact denoteLNode_congr fun c hcin => hagree c (hc c hcin)

/-- One level-interning step. -/
theorem internL_step {st : EStore} {n : LNode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.lnodes.size) {a : Level}
    (hd : denoteLNode st.denoteL n = some a) :
    (st.internL n).2.WF ∧ Ext st (st.internL n).2 ∧
      (st.internL n).2.denoteL (st.internL n).1 = some a :=
  ⟨internL_wf hwf hc, internL_ext st n, by rw [internL_denoteL hwf hc]; exact hd⟩

/-- `internLevel` preserves the invariant, extends the store, and its
result denotes the interned level. -/
theorem internLevel_spec {st : EStore} (hwf : st.WF) (l : Level) :
    (st.internLevel l).2.WF ∧ Ext st (st.internLevel l).2 ∧
      (st.internLevel l).2.denoteL (st.internLevel l).1 = some l := by
  induction l generalizing st with
  | zero => exact internL_step hwf (by simp [LNode.children]) rfl
  | param p => exact internL_step hwf (by simp [LNode.children]) rfl
  | succ u ih =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ih hwf
    rcases hI : st.internLevel u with ⟨ui, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    have hstep := internL_step (n := .succ ui) hwf₁
      (by simpa [LNode.children] using denoteL_lt_size hden₁)
      (a := .succ u) (by rw [denoteLNode, hden₁]; rfl)
    simp only [internLevel, hI]
    exact ⟨hstep.1, hext₁.trans hstep.2.1, hstep.2.2⟩
  | max u v ihu ihv =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihu hwf
    rcases hI₁ : st.internLevel u with ⟨ui, st₁⟩
    simp only [hI₁] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ihv hwf₁
    rcases hI₂ : st₁.internLevel v with ⟨vi, st₂⟩
    simp only [hI₂] at hwf₂ hext₂ hden₂
    have hden₁' := denoteL_mono hext₂ hden₁
    have hstep := internL_step (n := .max ui vi) hwf₂
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size hden₁'
        · exact denoteL_lt_size hden₂)
      (a := .max u v) (by rw [denoteLNode, hden₁', hden₂]; rfl)
    simp only [internLevel, hI₁, hI₂]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans hstep.2.1), hstep.2.2⟩
  | imax u v ihu ihv =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihu hwf
    rcases hI₁ : st.internLevel u with ⟨ui, st₁⟩
    simp only [hI₁] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ihv hwf₁
    rcases hI₂ : st₁.internLevel v with ⟨vi, st₂⟩
    simp only [hI₂] at hwf₂ hext₂ hden₂
    have hden₁' := denoteL_mono hext₂ hden₁
    have hstep := internL_step (n := .imax ui vi) hwf₂
      (by
        simp only [LNode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denoteL_lt_size hden₁'
        · exact denoteL_lt_size hden₂)
      (a := .imax u v) (by rw [denoteLNode, hden₁', hden₂]; rfl)
    simp only [internLevel, hI₁, hI₂]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans hstep.2.1), hstep.2.2⟩

/-- `internLevels` round-trip over a level list. -/
theorem internLevels_spec {st : EStore} (hwf : st.WF) (ls : List Level) :
    (st.internLevels ls).2.WF ∧ Ext st (st.internLevels ls).2 ∧
      denoteLList (st.internLevels ls).2.denoteL (st.internLevels ls).1
        = some ls := by
  induction ls generalizing st with
  | nil => exact ⟨hwf, Ext.refl st, rfl⟩
  | cons l ls ih =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := internLevel_spec hwf l
    rcases hI₁ : st.internLevel l with ⟨ui, st₁⟩
    simp only [hI₁] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ih hwf₁
    rcases hI₂ : st₁.internLevels ls with ⟨uis, st₂⟩
    simp only [hI₂] at hwf₂ hext₂ hden₂
    simp only [internLevels, hI₁, hI₂]
    refine ⟨hwf₂, hext₁.trans hext₂, ?_⟩
    simp only [denoteLList, denoteL_mono hext₂ hden₁, hden₂,
      Option.bind_some, Option.map_some]

/-- `internBM` round-trip. -/
theorem internBM_spec {st : EStore} (hwf : st.WF) (m : BinderMeta) :
    (st.internBM m).2.WF ∧ Ext st (st.internBM m).2 ∧
      denoteBM (st.internBM m).2.denoteL (st.internBM m).1 = some m := by
  obtain ⟨bi, (_ | u)⟩ := m
  · exact ⟨hwf, Ext.refl st, rfl⟩
  · obtain ⟨hwf₁, hext₁, hden₁⟩ := internLevel_spec hwf u
    rcases hI : st.internLevel u with ⟨ui, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    simp only [internBM, hI]
    exact ⟨hwf₁, hext₁, by simp [denoteBM, hden₁]⟩

/-! ## `internN` / `internName`: the name round-trip (task #88) -/

/-- `internN` with the store destructuring eliminated. -/
theorem internN_eq (st : EStore) (n : NNode) :
    st.internN n = match st.ncons[n]? with
      | some i => (i, st)
      | none =>
        (st.nnodes.size, ⟨st.nodes, st.cons, st.lnodes, st.lcons,
          st.bvarBs, st.fvarBs, st.lparamBs, st.eparamBs,
          st.nnodes.push n, st.ncons.insert n st.nnodes.size,
          st.rbNames.push (n.nameOf st.rbNames), st.tierTwo, st.tnodes,
          st.tcons, st.tbvarBs, st.tfvarBs, st.teparamBs⟩) := by
  obtain ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
    nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs, tfvarBs,
    teparamBs⟩ := st
  rfl

theorem internN_ext (st : EStore) (n : NNode) : Ext st (st.internN n).2 := by
  refine ⟨fun i m h => ?_, fun u m h => ?_, fun i m h => ?_⟩
  · rw [internN_eq]
    split
    · exact h
    · exact h
  · rw [internN_eq]
    split
    · exact h
    · exact h
  · rw [internN_eq]
    split
    · exact h
    · have : i < st.nnodes.size := (Array.getElem?_eq_some_iff.mp h).1
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt this)]
      exact h

/-- Interning a name node stores it at the returned index. -/
theorem internN_node {st : EStore} {n : NNode} (hwf : st.WF) :
    (st.internN n).2.nnodes[(st.internN n).1]? = some n := by
  rw [internN_eq]
  split
  · rename_i i h
    exact (hwf.ncons_graph n i).mp h
  · rw [Array.getElem?_push, if_pos rfl]

theorem internN_lt_size {st : EStore} {n : NNode} (hwf : st.WF) :
    (st.internN n).1 < (st.internN n).2.nnodes.size :=
  (Array.getElem?_eq_some_iff.mp (internN_node hwf)).1

/-- `internN` preserves the two-tier invariant when the node's prefix
is an already-stored name index (names are single-tier; the tier-two
clauses only see the name table grow). -/
theorem internN_twf {st : EStore} {n : NNode} (hwf : st.TWF)
    (hc : ∀ c ∈ n.children, c < st.nnodes.size) : (st.internN n).2.TWF := by
  rw [internN_eq]
  split
  · exact hwf
  · rename_i hmiss
    constructor
    · exact hwf.children_lt
    · exact hwf.cons_graph
    · exact hwf.levels_lt
    · exact hwf.lchildren_lt
    · exact hwf.lcons_graph
    · exact hwf.bvarBs_size
    · exact hwf.fvarBs_size
    · exact hwf.bvarBs_spec
    · exact hwf.fvarBs_spec
    · exact hwf.lparamBs_size
    · exact hwf.lparamBs_spec
    · exact hwf.eparamBs_size
    · exact hwf.eparamBs_spec
    · intro i m h p hpin
      exact Nat.lt_trans (hwf.names_lt i m h p hpin) (by simp)
    · intro i m h c hcin
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        exact hc c hcin
      · exact hwf.nchildren_lt i m h c hcin
    · intro m i
      constructor
      · intro h
        rw [Std.HashMap.getElem?_insert] at h
        by_cases hnm : n = m
        · subst hnm
          simp only [BEq.rfl, if_pos] at h
          cases h
          rw [Array.getElem?_push, if_pos rfl]
        · rw [if_neg (by simpa using hnm)] at h
          have h' := (hwf.ncons_graph m i).mp h
          have hi : i < st.nnodes.size := (Array.getElem?_eq_some_iff.mp h').1
          rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hi)]
          exact h'
      · intro h
        rw [Array.getElem?_push] at h
        rw [Std.HashMap.getElem?_insert]
        split at h
        · cases h
          subst_eqs
          simp
        · have hne : ¬ n = m := by
            rintro rfl
            have hcontra := (hwf.ncons_graph n i).mpr h
            rw [hmiss] at hcontra
            simp at hcontra
          rw [if_neg (by simpa using hne)]
          exact (hwf.ncons_graph m i).mpr h
    · simpa using hwf.rbNames_size
    · intro i m h
      rw [Array.getElem?_push] at h
      split at h
      · cases h
        subst_eqs
        rw [Array.getElem?_push, hwf.rbNames_size, if_pos rfl]
        refine congrArg some (NNode.nameOf_congr fun c hcin => ?_)
        exact (getD_push_of_lt (hwf.rbNames_size ▸ hc c hcin)).symm
      · have hi : i < st.nnodes.size := by
          rcases Array.getElem?_eq_some_iff.mp h with ⟨hlt, -⟩
          exact hlt
        rw [Array.getElem?_push, if_neg (hwf.rbNames_size ▸ Nat.ne_of_lt hi),
          hwf.rbNames_spec i m h]
        refine congrArg some (NNode.nameOf_congr fun c hcin => ?_)
        exact (getD_push_of_lt (hwf.rbNames_size ▸
          Nat.lt_trans (hwf.nchildren_lt i m h c hcin) hi)).symm
    · exact hwf.flag_bound
    · exact hwf.toff_tnil
    · exact hwf.t_children_lt
    · exact hwf.t_levels_lt
    · intro j m hj p hp
      exact Nat.lt_trans (hwf.t_names_lt j m hj p hp) (by simp)
    · exact hwf.t_cons_graph
    · exact hwf.t_cons_fresh
    · exact hwf.t_bvarBs_size
    · exact hwf.t_fvarBs_size
    · exact hwf.t_eparamBs_size
    · exact hwf.t_bvarBs_spec
    · exact hwf.t_fvarBs_spec
    · exact hwf.t_eparamBs_spec

/-- `internN` never touches the flag. -/
theorem internN_tierTwo (st : EStore) (n : NNode) :
    (st.internN n).2.tierTwo = st.tierTwo := by
  rw [internN_eq]
  split <;> rfl

/-- `internN` preserves the invariant when the node's prefix is an
already-stored name index. -/
theorem internN_wf {st : EStore} {n : NNode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nnodes.size) : (st.internN n).2.WF :=
  ⟨internN_twf hwf.toTWF hc, (internN_tierTwo st n).trans hwf.tier_off⟩

/-- Interning a name node whose prefix is already stored: the result
denotes the node's denotation over the *old* store. -/
theorem internN_denoteN {st : EStore} {n : NNode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nnodes.size) :
    (st.internN n).2.denoteN (st.internN n).1
      = denoteNNode st.denoteN n := by
  have hn := internN_node (n := n) hwf
  rw [internN_eq] at hn ⊢
  split at hn
  · rename_i i h
    rw [denoteN_node hn (hwf.nchildren_lt _ _ hn)]
  · rename_i hmiss
    have hagree : ∀ j, j < st.nnodes.size →
        (⟨st.nodes, st.cons, st.lnodes, st.lcons,
          st.bvarBs, st.fvarBs, st.lparamBs, st.eparamBs,
          st.nnodes.push n, st.ncons.insert n st.nnodes.size,
          st.rbNames.push (n.nameOf st.rbNames), st.tierTwo, st.tnodes,
          st.tcons, st.tbvarBs, st.tfvarBs, st.teparamBs⟩
          : EStore).denoteN j
          = st.denoteN j := by
      apply denoteN_agree
      intro j hj
      simp [Array.getElem?_push, Nat.ne_of_lt hj]
    rw [denoteN_node hn hc]
    exact denoteNNode_congr fun c hcin => hagree c (hc c hcin)

/-- One name-interning step. -/
theorem internN_step {st : EStore} {n : NNode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nnodes.size) {a : Name}
    (hd : denoteNNode st.denoteN n = some a) :
    (st.internN n).2.WF ∧ Ext st (st.internN n).2 ∧
      (st.internN n).2.denoteN (st.internN n).1 = some a :=
  ⟨internN_wf hwf hc, internN_ext st n, by rw [internN_denoteN hwf hc]; exact hd⟩

/-- `internName` extends the store (no well-formedness needed). -/
theorem internName_ext (st : EStore) (nm : Name) :
    Ext st (st.internName nm).2 := by
  induction nm generalizing st with
  | anonymous => exact internN_ext st .anonymous
  | str p sfx ih =>
    rcases hI : st.internName p with ⟨pi, st₁⟩
    have h := ih st
    rw [hI] at h
    simpa [internName, hI] using h.trans (internN_ext st₁ (.str pi sfx))
  | num p k ih =>
    rcases hI : st.internName p with ⟨pi, st₁⟩
    have h := ih st
    rw [hI] at h
    simpa [internName, hI] using h.trans (internN_ext st₁ (.num pi k))

/-- `internName` preserves the invariant, extends the store, and its
result denotes the interned name. -/
theorem internName_spec {st : EStore} (hwf : st.WF) (nm : Name) :
    (st.internName nm).2.WF ∧ Ext st (st.internName nm).2 ∧
      (st.internName nm).2.denoteN (st.internName nm).1 = some nm := by
  induction nm generalizing st with
  | anonymous => exact internN_step hwf (by simp [NNode.children]) rfl
  | str p s ih =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ih hwf
    rcases hI : st.internName p with ⟨pi, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    have hstep := internN_step (n := .str pi s) hwf₁
      (by simpa [NNode.children] using denoteN_lt_size hden₁)
      (a := .str p s) (by rw [denoteNNode, hden₁]; rfl)
    simp only [internName, hI]
    exact ⟨hstep.1, hext₁.trans hstep.2.1, hstep.2.2⟩
  | num p k ih =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ih hwf
    rcases hI : st.internName p with ⟨pi, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    have hstep := internN_step (n := .num pi k) hwf₁
      (by simpa [NNode.children] using denoteN_lt_size hden₁)
      (a := .num p k) (by rw [denoteNNode, hden₁]; rfl)
    simp only [internName, hI]
    exact ⟨hstep.1, hext₁.trans hstep.2.1, hstep.2.2⟩

/-! ## `internExpr`: round-trip -/

/-- One interning step of the round-trip: interning a node whose
children are stored and denote the subterms gives the invariant, the
extension, and the node's denotation. -/
private theorem intern_step {st : EStore} {n : ENode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nodes.size)
    (hlv : ∀ u ∈ n.levels, u < st.lnodes.size)
    (hnm : ∀ p ∈ n.names, p < st.nnodes.size) {a : Expr}
    (hd : denoteNode st.denote st.denoteL st.denoteN n = some a) :
    (st.intern n).2.WF ∧ Ext st (st.intern n).2 ∧
      (st.intern n).2.denote (st.intern n).1 = some a :=
  ⟨intern_wf hwf hc hlv hnm, intern_ext st n,
    by rw [intern_denote hwf hc]; exact hd⟩

/-- In-range level references from a successful level-list
denotation. -/
theorem denoteLList_lt_size {st : EStore} :
    ∀ {us : List LIdx} {ls : List Level},
      denoteLList st.denoteL us = some ls → ∀ u ∈ us, u < st.lnodes.size := by
  intro us
  induction us with
  | nil => simp
  | cons u us ih =>
    intro ls h v hv
    simp only [denoteLList, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, ls', hls', rfl⟩ := h
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact denoteL_lt_size hl
    · exact ih hls' v hv'

/-- In-range level reference from a successful binder-meta
denotation. -/
theorem denoteBM_lt_size {st : EStore} {m : IBinderMeta} {bm : BinderMeta}
    (h : denoteBM st.denoteL m = some bm) :
    ∀ u ∈ m.cod.toList, u < st.lnodes.size := by
  obtain ⟨bi, (_ | u)⟩ := m
  · simp
  · simp only [denoteBM, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, rfl⟩ := h
    simpa using denoteL_lt_size hl

/-- `internExpr` preserves the invariant, extends the store, and its
result denotes the interned expression. -/
theorem internExpr_spec {st : EStore} (hwf : st.WF) (e : Expr) :
    (st.internExpr e).2.WF ∧ Ext st (st.internExpr e).2 ∧
      (st.internExpr e).2.denote (st.internExpr e).1 = some e := by
  induction e generalizing st with
  | bvar i =>
    exact intern_step hwf (by simp [ENode.children])
      (by simp [ENode.levels]) (by simp [ENode.names]) rfl
  | sort u =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := internLevel_spec hwf u
    rcases hI : st.internLevel u with ⟨ui, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    have hstep := intern_step (n := .sort ui) hwf₁
      (by simp [ENode.children])
      (by simpa [ENode.levels] using denoteL_lt_size hden₁)
      (by simp [ENode.names])
      (a := .sort u) (by rw [denoteNode, hden₁]; rfl)
    simp only [internExpr, hI]
    exact ⟨hstep.1, hext₁.trans hstep.2.1, hstep.2.2⟩
  | const n us =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := internLevels_spec hwf us
    rcases hI : st.internLevels us with ⟨uis, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := internName_spec hwf₁ n
    rcases hN : st₁.internName n with ⟨ni, st₂⟩
    simp only [hN] at hwf₂ hext₂ hden₂
    have hden₁' := denoteLList_mono hext₂ hden₁
    have hstep := intern_step (n := .const ni uis) hwf₂
      (by simp [ENode.children])
      (by simpa [ENode.levels] using denoteLList_lt_size hden₁')
      (by simpa [ENode.names] using denoteN_lt_size hden₂)
      (a := .const n us) (by rw [denoteNode, hden₁', hden₂]; rfl)
    simp only [internExpr, hI, hN]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans hstep.2.1), hstep.2.2⟩
  | lit l =>
    exact intern_step hwf (by simp [ENode.children])
      (by simp [ENode.levels]) (by simp [ENode.names]) rfl
  | fvar idx nm ty ih =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ih hwf
    rcases hI : st.internExpr ty with ⟨t, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := internName_spec hwf₁ nm
    rcases hN : st₁.internName nm with ⟨ni, st₂⟩
    simp only [hN] at hwf₂ hext₂ hden₂
    have hden₁' := denote_mono hext₂ hden₁
    have hstep := intern_step (n := .fvar idx ni t) hwf₂
      (by simpa [ENode.children] using denote_lt_size hden₁')
      (by simp [ENode.levels])
      (by simpa [ENode.names] using denoteN_lt_size hden₂)
      (a := .fvar idx nm ty) (by rw [denoteNode, hden₁', hden₂]; rfl)
    simp only [internExpr, hI, hN]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans hstep.2.1), hstep.2.2⟩
  | app f a ihf iha =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihf hwf
    rcases hI₁ : st.internExpr f with ⟨fi, st₁⟩
    simp only [hI₁] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := iha hwf₁
    rcases hI₂ : st₁.internExpr a with ⟨ai, st₂⟩
    simp only [hI₂] at hwf₂ hext₂ hden₂
    have hden₁' := denote_mono hext₂ hden₁
    have hstep := intern_step (n := .app fi ai) hwf₂
      (by
        simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denote_lt_size hden₁'
        · exact denote_lt_size hden₂)
      (by simp [ENode.levels])
      (by simp [ENode.names])
      (a := .app f a) (by rw [denoteNode, hden₁', hden₂]; rfl)
    simp only [internExpr, hI₁, hI₂]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans hstep.2.1), hstep.2.2⟩
  | lam n ty body m ihty ihbody =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihty hwf
    rcases hI₁ : st.internExpr ty with ⟨ti, st₁⟩
    simp only [hI₁] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ihbody hwf₁
    rcases hI₂ : st₁.internExpr body with ⟨bi, st₂⟩
    simp only [hI₂] at hwf₂ hext₂ hden₂
    obtain ⟨hwf₃, hext₃, hden₃⟩ := internBM_spec hwf₂ m
    rcases hI₃ : st₂.internBM m with ⟨mi, st₃⟩
    simp only [hI₃] at hwf₃ hext₃ hden₃
    obtain ⟨hwf₄, hext₄, hden₄⟩ := internName_spec hwf₃ n
    rcases hI₄ : st₃.internName n with ⟨ni, st₄⟩
    simp only [hI₄] at hwf₄ hext₄ hden₄
    have hden₁' := denote_mono hext₄
      (denote_mono hext₃ (denote_mono hext₂ hden₁))
    have hden₂' := denote_mono hext₄ (denote_mono hext₃ hden₂)
    have hden₃' := denoteBM_mono hext₄ hden₃
    have hstep := intern_step (n := .lam ni ti bi mi) hwf₄
      (by
        simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denote_lt_size hden₁'
        · exact denote_lt_size hden₂')
      (by simpa [ENode.levels] using denoteBM_lt_size hden₃')
      (by simpa [ENode.names] using denoteN_lt_size hden₄)
      (a := .lam n ty body m)
      (by rw [denoteNode, hden₁', hden₂', hden₃', hden₄]; rfl)
    simp only [internExpr, hI₁, hI₂, hI₃, hI₄]
    exact ⟨hstep.1,
      hext₁.trans (hext₂.trans (hext₃.trans (hext₄.trans hstep.2.1))),
      hstep.2.2⟩
  | forallE n ty body m ihty ihbody =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihty hwf
    rcases hI₁ : st.internExpr ty with ⟨ti, st₁⟩
    simp only [hI₁] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ihbody hwf₁
    rcases hI₂ : st₁.internExpr body with ⟨bi, st₂⟩
    simp only [hI₂] at hwf₂ hext₂ hden₂
    obtain ⟨hwf₃, hext₃, hden₃⟩ := internBM_spec hwf₂ m
    rcases hI₃ : st₂.internBM m with ⟨mi, st₃⟩
    simp only [hI₃] at hwf₃ hext₃ hden₃
    obtain ⟨hwf₄, hext₄, hden₄⟩ := internName_spec hwf₃ n
    rcases hI₄ : st₃.internName n with ⟨ni, st₄⟩
    simp only [hI₄] at hwf₄ hext₄ hden₄
    have hden₁' := denote_mono hext₄
      (denote_mono hext₃ (denote_mono hext₂ hden₁))
    have hden₂' := denote_mono hext₄ (denote_mono hext₃ hden₂)
    have hden₃' := denoteBM_mono hext₄ hden₃
    have hstep := intern_step (n := .forallE ni ti bi mi) hwf₄
      (by
        simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denote_lt_size hden₁'
        · exact denote_lt_size hden₂')
      (by simpa [ENode.levels] using denoteBM_lt_size hden₃')
      (by simpa [ENode.names] using denoteN_lt_size hden₄)
      (a := .forallE n ty body m)
      (by rw [denoteNode, hden₁', hden₂', hden₃', hden₄]; rfl)
    simp only [internExpr, hI₁, hI₂, hI₃, hI₄]
    exact ⟨hstep.1,
      hext₁.trans (hext₂.trans (hext₃.trans (hext₄.trans hstep.2.1))),
      hstep.2.2⟩
  | letE n ty val body ihty ihval ihbody =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihty hwf
    rcases hI₁ : st.internExpr ty with ⟨ti, st₁⟩
    simp only [hI₁] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ihval hwf₁
    rcases hI₂ : st₁.internExpr val with ⟨vi, st₂⟩
    simp only [hI₂] at hwf₂ hext₂ hden₂
    obtain ⟨hwf₃, hext₃, hden₃⟩ := ihbody hwf₂
    rcases hI₃ : st₂.internExpr body with ⟨bi, st₃⟩
    simp only [hI₃] at hwf₃ hext₃ hden₃
    obtain ⟨hwf₄, hext₄, hden₄⟩ := internName_spec hwf₃ n
    rcases hI₄ : st₃.internName n with ⟨ni, st₄⟩
    simp only [hI₄] at hwf₄ hext₄ hden₄
    have hden₁' := denote_mono hext₄
      (denote_mono hext₃ (denote_mono hext₂ hden₁))
    have hden₂' := denote_mono hext₄ (denote_mono hext₃ hden₂)
    have hden₃' := denote_mono hext₄ hden₃
    have hstep := intern_step (n := .letE ni ti vi bi) hwf₄
      (by
        simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl | rfl)
        · exact denote_lt_size hden₁'
        · exact denote_lt_size hden₂'
        · exact denote_lt_size hden₃')
      (by simp [ENode.levels])
      (by simpa [ENode.names] using denoteN_lt_size hden₄)
      (a := .letE n ty val body)
      (by rw [denoteNode, hden₁', hden₂', hden₃', hden₄]; rfl)
    simp only [internExpr, hI₁, hI₂, hI₃, hI₄]
    exact ⟨hstep.1,
      hext₁.trans (hext₂.trans (hext₃.trans (hext₄.trans hstep.2.1))),
      hstep.2.2⟩
  | proj sN i e ih =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ih hwf
    rcases hI : st.internExpr e with ⟨ei, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := internName_spec hwf₁ sN
    rcases hN : st₁.internName sN with ⟨si, st₂⟩
    simp only [hN] at hwf₂ hext₂ hden₂
    have hden₁' := denote_mono hext₂ hden₁
    have hstep := intern_step (n := .proj si i ei) hwf₂
      (by simpa [ENode.children] using denote_lt_size hden₁')
      (by simp [ENode.levels])
      (by simpa [ENode.names] using denoteN_lt_size hden₂)
      (a := .proj sN i e) (by rw [denoteNode, hden₁', hden₂]; rfl)
    simp only [internExpr, hI, hN]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans hstep.2.1), hstep.2.2⟩

/-! ## Canonicity: index equality is expression equality -/

/-- Inversion of `denoteLNode` at each `Level` head constructor. -/
theorem denoteLNode_zero_inv {den : LIdx → Option Level} {n : LNode}
    (h : denoteLNode den n = some .zero) : n = .zero := by
  cases n <;> simp_all [denoteLNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteLNode_param_inv {den : LIdx → Option Level} {n : LNode}
    {p : Name} (h : denoteLNode den n = some (.param p)) : n = .param p := by
  cases n <;> simp_all [denoteLNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteLNode_succ_inv {den : LIdx → Option Level} {n : LNode}
    {l : Level} (h : denoteLNode den n = some (.succ l)) :
    ∃ u, n = .succ u ∧ den u = some l := by
  cases n <;> simp_all [denoteLNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteLNode_max_inv {den : LIdx → Option Level} {n : LNode}
    {x y : Level} (h : denoteLNode den n = some (.max x y)) :
    ∃ u v, n = .max u v ∧ den u = some x ∧ den v = some y := by
  cases n <;> simp_all [denoteLNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteLNode_imax_inv {den : LIdx → Option Level} {n : LNode}
    {x y : Level} (h : denoteLNode den n = some (.imax x y)) :
    ∃ u v, n = .imax u v ∧ den u = some x ∧ den v = some y := by
  cases n <;> simp_all [denoteLNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

/-- The level cons-table makes stored level nodes unique. -/
theorem lindex_unique {st : EStore} (hwf : st.WF) {n : LNode} {i j : LIdx}
    (hi : st.lnodes[i]? = some n) (hj : st.lnodes[j]? = some n) : i = j :=
  Option.some.inj
    (((hwf.lcons_graph n i).mpr hi).symm.trans ((hwf.lcons_graph n j).mpr hj))

/-- Level denotation is injective on a well-formed store. -/
theorem denoteL_inj {st : EStore} (hwf : st.WF) :
    ∀ {a : Level} {i j : LIdx}, st.denoteL i = some a → st.denoteL j = some a →
      i = j := by
  intro a
  induction a with
  | zero =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denoteL_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denoteL_some_inv hj
    obtain rfl := denoteLNode_zero_inv hdn
    obtain rfl := denoteLNode_zero_inv hdm
    exact lindex_unique hwf hn hm
  | param p =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denoteL_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denoteL_some_inv hj
    obtain rfl := denoteLNode_param_inv hdn
    obtain rfl := denoteLNode_param_inv hdm
    exact lindex_unique hwf hn hm
  | succ l ih =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denoteL_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denoteL_some_inv hj
    obtain ⟨u, rfl, hu⟩ := denoteLNode_succ_inv hdn
    obtain ⟨u', rfl, hu'⟩ := denoteLNode_succ_inv hdm
    obtain rfl := ih hu hu'
    exact lindex_unique hwf hn hm
  | max x y ihx ihy =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denoteL_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denoteL_some_inv hj
    obtain ⟨u, v, rfl, hu, hv⟩ := denoteLNode_max_inv hdn
    obtain ⟨u', v', rfl, hu', hv'⟩ := denoteLNode_max_inv hdm
    obtain rfl := ihx hu hu'
    obtain rfl := ihy hv hv'
    exact lindex_unique hwf hn hm
  | imax x y ihx ihy =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denoteL_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denoteL_some_inv hj
    obtain ⟨u, v, rfl, hu, hv⟩ := denoteLNode_imax_inv hdn
    obtain ⟨u', v', rfl, hu', hv'⟩ := denoteLNode_imax_inv hdm
    obtain rfl := ihx hu hu'
    obtain rfl := ihy hv hv'
    exact lindex_unique hwf hn hm

/-- Level-list denotation is injective on a well-formed store. -/
theorem denoteLList_inj {st : EStore} (hwf : st.WF) :
    ∀ {us vs : List LIdx} {ls : List Level},
      denoteLList st.denoteL us = some ls →
      denoteLList st.denoteL vs = some ls → us = vs := by
  intro us
  induction us with
  | nil =>
    intro vs ls h h'
    cases vs with
    | nil => rfl
    | cons v vs =>
      simp only [denoteLList] at h h'
      cases h
      simp [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h'
  | cons u us ih =>
    intro vs ls h h'
    cases vs with
    | nil =>
      simp only [denoteLList] at h h'
      cases h'
      simp [Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
    | cons v vs =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at h h'
      obtain ⟨l, hl, ls', hls', rfl⟩ := h
      obtain ⟨l', hl', ls'', hls'', heq⟩ := h'
      obtain ⟨rfl, rfl⟩ : l' = l ∧ ls'' = ls' := by
        constructor <;> grind
      obtain rfl := denoteL_inj hwf hl hl'
      obtain rfl := ih hls' hls''
      rfl

/-- Binder-meta denotation is injective on a well-formed store. -/
theorem denoteBM_inj {st : EStore} (hwf : st.WF) {m m' : IBinderMeta}
    {bm : BinderMeta} (h : denoteBM st.denoteL m = some bm)
    (h' : denoteBM st.denoteL m' = some bm) : m = m' := by
  obtain ⟨bi, (_ | u)⟩ := m <;> obtain ⟨bi', (_ | u')⟩ := m'
  · simp only [denoteBM, Option.some.injEq] at h h'
    rw [← h] at h'
    simp only [BinderMeta.mk.injEq] at h'
    simp [h'.1]
  · simp only [denoteBM, Option.some.injEq, Option.map_eq_some_iff] at h h'
    subst h
    obtain ⟨l, -, hcon⟩ := h'
    simp [BinderMeta.mk.injEq] at hcon
  · simp only [denoteBM, Option.some.injEq, Option.map_eq_some_iff] at h h'
    subst h'
    obtain ⟨l, -, hcon⟩ := h
    simp [BinderMeta.mk.injEq] at hcon
  · simp only [denoteBM, Option.map_eq_some_iff] at h h'
    obtain ⟨l, hl, rfl⟩ := h
    obtain ⟨l', hl', heq⟩ := h'
    simp only [BinderMeta.mk.injEq, Option.some.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    rw [denoteL_inj hwf hl hl']

/-- Inversion of `denoteNNode` at each `Name` head constructor
(task #88). -/
theorem denoteNNode_anonymous_inv {den : NIdx → Option Name} {n : NNode}
    (h : denoteNNode den n = some .anonymous) : n = .anonymous := by
  cases n <;> simp_all [denoteNNode, Option.map_eq_some_iff]

theorem denoteNNode_str_inv {den : NIdx → Option Name} {n : NNode}
    {p : Name} {s : String} (h : denoteNNode den n = some (.str p s)) :
    ∃ q, n = .str q s ∧ den q = some p := by
  cases n <;> simp_all [denoteNNode, Option.map_eq_some_iff] <;> grind

theorem denoteNNode_num_inv {den : NIdx → Option Name} {n : NNode}
    {p : Name} {k : Nat} (h : denoteNNode den n = some (.num p k)) :
    ∃ q, n = .num q k ∧ den q = some p := by
  cases n <;> simp_all [denoteNNode, Option.map_eq_some_iff] <;> grind

/-- The name cons-table makes stored name nodes unique. -/
theorem nindex_unique {st : EStore} (hwf : st.WF) {n : NNode} {i j : NIdx}
    (hi : st.nnodes[i]? = some n) (hj : st.nnodes[j]? = some n) : i = j :=
  Option.some.inj
    (((hwf.ncons_graph n i).mpr hi).symm.trans ((hwf.ncons_graph n j).mpr hj))

/-- Name denotation is injective on a well-formed store: index equality
is name equality. -/
theorem denoteN_inj {st : EStore} (hwf : st.WF) :
    ∀ {a : Name} {i j : NIdx}, st.denoteN i = some a → st.denoteN j = some a →
      i = j := by
  intro a
  induction a with
  | anonymous =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denoteN_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denoteN_some_inv hj
    obtain rfl := denoteNNode_anonymous_inv hdn
    obtain rfl := denoteNNode_anonymous_inv hdm
    exact nindex_unique hwf hn hm
  | str p s ih =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denoteN_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denoteN_some_inv hj
    obtain ⟨q, rfl, hq⟩ := denoteNNode_str_inv hdn
    obtain ⟨q', rfl, hq'⟩ := denoteNNode_str_inv hdm
    obtain rfl := ih hq hq'
    exact nindex_unique hwf hn hm
  | num p k ih =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denoteN_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denoteN_some_inv hj
    obtain ⟨q, rfl, hq⟩ := denoteNNode_num_inv hdn
    obtain ⟨q', rfl, hq'⟩ := denoteNNode_num_inv hdm
    obtain rfl := ih hq hq'
    exact nindex_unique hwf hn hm

/-- Interned name equality is name equality (`O(1)` equality on
denoting indices). -/
theorem denoteN_eq_iff {st : EStore} (hwf : st.WF) {i j : NIdx}
    {a b : Name} (ha : st.denoteN i = some a) (hb : st.denoteN j = some b) :
    i = j ↔ a = b := by
  constructor
  · rintro rfl
    rw [ha] at hb
    exact Option.some.inj hb
  · rintro rfl
    exact denoteN_inj hwf ha hb

/-- `beqNameI` decides equality of the denoted name against a fixed
`Name` (task #88). -/
theorem beqNameI_eq {st : EStore} :
    ∀ {nm : Name} {i : NIdx} {a : Name}, st.denoteN i = some a →
      st.beqNameI i nm = (a == nm) := by
  intro nm
  induction nm with
  | anonymous =>
    intro i a h
    obtain ⟨n, hn, -, hdn⟩ := denoteN_some_inv h
    cases n with
    | anonymous =>
      cases hdn
      simp [beqNameI, hn]
    | str p sfx =>
      rw [denoteNNode, Option.map_eq_some_iff] at hdn
      obtain ⟨pa, -, rfl⟩ := hdn
      simp only [beqNameI, hn]
      rfl
    | num p k =>
      rw [denoteNNode, Option.map_eq_some_iff] at hdn
      obtain ⟨pa, -, rfl⟩ := hdn
      simp only [beqNameI, hn]
      rfl
  | str p sfx ih =>
    intro i a h
    obtain ⟨n, hn, -, hdn⟩ := denoteN_some_inv h
    cases n with
    | anonymous =>
      cases hdn
      simp only [beqNameI, hn]
      rfl
    | str pi s' =>
      rw [denoteNNode, Option.map_eq_some_iff] at hdn
      obtain ⟨pa, hpa, rfl⟩ := hdn
      simp only [beqNameI, hn]
      rw [ih hpa]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq, Name.str.injEq]
      grind
    | num pi k =>
      rw [denoteNNode, Option.map_eq_some_iff] at hdn
      obtain ⟨pa, -, rfl⟩ := hdn
      simp only [beqNameI, hn]
      rfl
  | num p k ih =>
    intro i a h
    obtain ⟨n, hn, -, hdn⟩ := denoteN_some_inv h
    cases n with
    | anonymous =>
      cases hdn
      simp only [beqNameI, hn]
      rfl
    | str pi s' =>
      rw [denoteNNode, Option.map_eq_some_iff] at hdn
      obtain ⟨pa, -, rfl⟩ := hdn
      simp only [beqNameI, hn]
      rfl
    | num pi k' =>
      rw [denoteNNode, Option.map_eq_some_iff] at hdn
      obtain ⟨pa, hpa, rfl⟩ := hdn
      simp only [beqNameI, hn]
      rw [ih hpa]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.and_eq_true, beq_iff_eq, Name.num.injEq]
      grind

/-- Inversion of `denoteNode` at each `Expr` head constructor. -/
theorem denoteNode_bvar_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name}
    {n : ENode} {k : Nat}
    (h : denoteNode den denL denN n = some (.bvar k)) : n = .bvar k := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_fvar_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name} {n : ENode}
    {idx : Nat} {nm : Name} {ty : Expr}
    (h : denoteNode den denL denN n = some (.fvar idx nm ty)) :
    ∃ ni t, n = .fvar idx ni t ∧ denN ni = some nm ∧ den t = some ty := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_sort_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name}
    {n : ENode} {u : Level}
    (h : denoteNode den denL denN n = some (.sort u)) :
    ∃ ui, n = .sort ui ∧ denL ui = some u := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_const_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name} {n : ENode}
    {nm : Name} {us : List Level}
    (h : denoteNode den denL denN n = some (.const nm us)) :
    ∃ ni uis, n = .const ni uis ∧ denN ni = some nm ∧
      denoteLList denL uis = some us := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_app_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name}
    {n : ENode} {x y : Expr}
    (h : denoteNode den denL denN n = some (.app x y)) :
    ∃ f a, n = .app f a ∧ den f = some x ∧ den a = some y := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_lam_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name} {n : ENode}
    {nm : Name} {ty body : Expr} {m : BinderMeta}
    (h : denoteNode den denL denN n = some (.lam nm ty body m)) :
    ∃ ni t b mi, n = .lam ni t b mi ∧ denN ni = some nm ∧
      den t = some ty ∧ den b = some body ∧
      denoteBM denL mi = some m := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_forallE_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name} {n : ENode}
    {nm : Name} {ty body : Expr} {m : BinderMeta}
    (h : denoteNode den denL denN n = some (.forallE nm ty body m)) :
    ∃ ni t b mi, n = .forallE ni t b mi ∧ denN ni = some nm ∧
      den t = some ty ∧ den b = some body ∧
      denoteBM denL mi = some m := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_letE_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name} {n : ENode}
    {nm : Name} {ty val body : Expr}
    (h : denoteNode den denL denN n = some (.letE nm ty val body)) :
    ∃ ni t v b, n = .letE ni t v b ∧ denN ni = some nm ∧
      den t = some ty ∧ den v = some val ∧
      den b = some body := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_lit_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name}
    {n : ENode} {l : Literal}
    (h : denoteNode den denL denN n = some (.lit l)) : n = .lit l := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_proj_inv {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {denN : NIdx → Option Name} {n : ENode}
    {s : Name} {j : Nat} {x : Expr}
    (h : denoteNode den denL denN n = some (.proj s j x)) :
    ∃ si e, n = .proj si j e ∧ denN si = some s ∧ den e = some x := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

/-- The cons-table makes stored nodes unique: two indices holding the
same node coincide. -/
theorem index_unique {st : EStore} (hwf : st.WF) {n : ENode} {i j : EIdx}
    (hi : st.nodes[i]? = some n) (hj : st.nodes[j]? = some n) : i = j :=
  Option.some.inj
    (((hwf.cons_graph n i).mpr hi).symm.trans ((hwf.cons_graph n j).mpr hj))

/-- Denotation is injective on a well-formed store: two indices denoting
the same expression are equal (canonicity — hash-consing stores every
expression at most once, and children determine the node). -/
theorem denote_inj {st : EStore} (hwf : st.WF) :
    ∀ {a : Expr} {i j : EIdx}, st.denote i = some a → st.denote j = some a →
      i = j := by
  intro a
  induction a with
  | bvar k =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain rfl := denoteNode_bvar_inv hdn
    obtain rfl := denoteNode_bvar_inv hdm
    exact index_unique hwf hn hm
  | sort u =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨ui, rfl, hui⟩ := denoteNode_sort_inv hdn
    obtain ⟨uj, rfl, huj⟩ := denoteNode_sort_inv hdm
    obtain rfl := denoteL_inj hwf hui huj
    exact index_unique hwf hn hm
  | const nm us =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨ni, uis, rfl, hni, huis⟩ := denoteNode_const_inv hdn
    obtain ⟨nj, ujs, rfl, hnj, hujs⟩ := denoteNode_const_inv hdm
    obtain rfl := denoteN_inj hwf hni hnj
    obtain rfl := denoteLList_inj hwf huis hujs
    exact index_unique hwf hn hm
  | lit l =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain rfl := denoteNode_lit_inv hdn
    obtain rfl := denoteNode_lit_inv hdm
    exact index_unique hwf hn hm
  | fvar idx nm ty ih =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨ni, t, rfl, hni, ht⟩ := denoteNode_fvar_inv hdn
    obtain ⟨nj, t', rfl, hnj, ht'⟩ := denoteNode_fvar_inv hdm
    obtain rfl := denoteN_inj hwf hni hnj
    obtain rfl := ih ht ht'
    exact index_unique hwf hn hm
  | app x y ihx ihy =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨f, a, rfl, hf, ha⟩ := denoteNode_app_inv hdn
    obtain ⟨g, b, rfl, hg, hb⟩ := denoteNode_app_inv hdm
    obtain rfl := ihx hf hg
    obtain rfl := ihy ha hb
    exact index_unique hwf hn hm
  | lam nm ty body m ihty ihbody =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m', hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨ni, t, b, mi, rfl, hni, ht, hb, hmi⟩ := denoteNode_lam_inv hdn
    obtain ⟨nj, t', b', mi', rfl, hnj, ht', hb', hmi'⟩ :=
      denoteNode_lam_inv hdm
    obtain rfl := denoteN_inj hwf hni hnj
    obtain rfl := ihty ht ht'
    obtain rfl := ihbody hb hb'
    obtain rfl := denoteBM_inj hwf hmi hmi'
    exact index_unique hwf hn hm
  | forallE nm ty body m ihty ihbody =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m', hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨ni, t, b, mi, rfl, hni, ht, hb, hmi⟩ :=
      denoteNode_forallE_inv hdn
    obtain ⟨nj, t', b', mi', rfl, hnj, ht', hb', hmi'⟩ :=
      denoteNode_forallE_inv hdm
    obtain rfl := denoteN_inj hwf hni hnj
    obtain rfl := ihty ht ht'
    obtain rfl := ihbody hb hb'
    obtain rfl := denoteBM_inj hwf hmi hmi'
    exact index_unique hwf hn hm
  | letE nm ty val body ihty ihval ihbody =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨ni, t, v, b, rfl, hni, ht, hv, hb⟩ := denoteNode_letE_inv hdn
    obtain ⟨nj, t', v', b', rfl, hnj, ht', hv', hb'⟩ :=
      denoteNode_letE_inv hdm
    obtain rfl := denoteN_inj hwf hni hnj
    obtain rfl := ihty ht ht'
    obtain rfl := ihval hv hv'
    obtain rfl := ihbody hb hb'
    exact index_unique hwf hn hm
  | proj s k x ih =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨si, e, rfl, hsi, he⟩ := denoteNode_proj_inv hdn
    obtain ⟨sj, e', rfl, hsj, he'⟩ := denoteNode_proj_inv hdm
    obtain rfl := denoteN_inj hwf hsi hsj
    obtain rfl := ih he he'
    exact index_unique hwf hn hm

/-- O(1) equality: on a well-formed store, comparing indices is
comparing the denoted expressions. -/
theorem denote_eq_iff {st : EStore} (hwf : st.WF) {i j : EIdx} {a b : Expr}
    (ha : st.denote i = some a) (hb : st.denote j = some b) :
    i = j ↔ a = b := by
  constructor
  · rintro rfl
    rw [ha] at hb
    exact Option.some.inj hb
  · rintro rfl
    exact denote_inj hwf ha hb

/-! ## Totality and extension helpers for the operation proofs -/

/-- On a well-formed store, every in-range name index denotes. -/
theorem denoteN_total {st : EStore} (hwf : st.WF) :
    ∀ (i : NIdx), i < st.nnodes.size → ∃ x, st.denoteN i = some x := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    have hn : st.nnodes[i]? = some st.nnodes[i] := by
      simp [hi]
    have hc := hwf.nchildren_lt i _ hn
    rw [denoteN_node hn hc]
    cases hnn : st.nnodes[i] with
    | anonymous => exact ⟨_, rfl⟩
    | str p sfx =>
      obtain ⟨x, hx⟩ := ih p (hc p (by simp [hnn, NNode.children]))
        (Nat.lt_trans (hc p (by simp [hnn, NNode.children])) hi)
      exact ⟨_, by rw [denoteNNode, hx]; rfl⟩
    | num p k =>
      obtain ⟨x, hx⟩ := ih p (hc p (by simp [hnn, NNode.children]))
        (Nat.lt_trans (hc p (by simp [hnn, NNode.children])) hi)
      exact ⟨_, by rw [denoteNNode, hx]; rfl⟩

/-- The executable readback (the eager array read) agrees with the
structural name denotation on a well-formed store (task #88). -/
theorem WF.readbackN_eq_denoteN {st : EStore} (hwf : st.WF) :
    ∀ i, st.readbackN i = st.denoteN i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    show st.rbNames[i]? = st.denoteN i
    cases hn : st.nnodes[i]? with
    | none =>
      have hsz : st.nnodes.size ≤ i := by
        rcases Nat.lt_or_ge i st.nnodes.size with hlt | hge
        · rw [Array.getElem?_eq_getElem hlt] at hn
          cases hn
        · exact hge
      rw [denoteN.eq_def, hn]
      exact Array.getElem?_eq_none (hwf.rbNames_size ▸ hsz)
    | some n =>
      have hc := hwf.nchildren_lt i n hn
      have hisz : i < st.nnodes.size := (Array.getElem?_eq_some_iff.mp hn).1
      rw [hwf.rbNames_spec i n hn, denoteN_node hn hc]
      cases n with
      | anonymous => rfl
      | str p sfx =>
        have hp := hc p (by simp [NNode.children])
        obtain ⟨pn, hpn⟩ := denoteN_total hwf p (Nat.lt_trans hp hisz)
        have hrb : st.rbNames[p]? = some pn := (ih p hp).trans hpn
        rw [denoteNNode, hpn]
        show some (NNode.nameOf st.rbNames (.str p sfx)) = _
        simp [NNode.nameOf, Array.getD_eq_getD_getElem?, hrb]
      | num p k =>
        have hp := hc p (by simp [NNode.children])
        obtain ⟨pn, hpn⟩ := denoteN_total hwf p (Nat.lt_trans hp hisz)
        have hrb : st.rbNames[p]? = some pn := (ih p hp).trans hpn
        rw [denoteNNode, hpn]
        show some (NNode.nameOf st.rbNames (.num p k)) = _
        simp [NNode.nameOf, Array.getD_eq_getD_getElem?, hrb]

/-- On a well-formed store, every in-range level index denotes. -/
theorem denoteL_total {st : EStore} (hwf : st.WF) :
    ∀ (u : LIdx), u < st.lnodes.size → ∃ x, st.denoteL u = some x := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro hu
    have hn : st.lnodes[u]? = some st.lnodes[u] := by
      simp [hu]
    have hc := hwf.lchildren_lt u _ hn
    rw [denoteL_node hn hc]
    have hcs : ∀ c ∈ (st.lnodes[u]).children, ∃ x, st.denoteL c = some x :=
      fun c hcin => ih c (hc c hcin)
        (Nat.lt_trans (hc c hcin) hu)
    cases hnn : st.lnodes[u] with
    | zero => exact ⟨_, rfl⟩
    | param p => exact ⟨_, rfl⟩
    | succ l =>
      obtain ⟨x, hx⟩ := hcs l (by simp [hnn, LNode.children])
      exact ⟨_, by rw [denoteLNode, hx]; rfl⟩
    | max l r =>
      obtain ⟨x, hx⟩ := hcs l (by simp [hnn, LNode.children])
      obtain ⟨y, hy⟩ := hcs r (by simp [hnn, LNode.children])
      exact ⟨_, by rw [denoteLNode, hx, hy]; rfl⟩
    | imax l r =>
      obtain ⟨x, hx⟩ := hcs l (by simp [hnn, LNode.children])
      obtain ⟨y, hy⟩ := hcs r (by simp [hnn, LNode.children])
      exact ⟨_, by rw [denoteLNode, hx, hy]; rfl⟩

/-- On a well-formed store, every in-range level index list denotes. -/
theorem denoteLList_total {st : EStore} (hwf : st.WF) :
    ∀ (us : List LIdx), (∀ u ∈ us, u < st.lnodes.size) →
      ∃ ls, denoteLList st.denoteL us = some ls := by
  intro us
  induction us with
  | nil => exact fun _ => ⟨[], rfl⟩
  | cons u us ih =>
    intro h
    obtain ⟨l, hl⟩ := denoteL_total hwf u (h u (by simp))
    obtain ⟨ls, hls⟩ := ih (fun v hv => h v (by simp [hv]))
    exact ⟨l :: ls, by simp [denoteLList, hl, hls]⟩

/-- On a well-formed store, in-range binder metadata denotes. -/
theorem denoteBM_total {st : EStore} (hwf : st.WF) (m : IBinderMeta)
    (h : ∀ u ∈ m.cod.toList, u < st.lnodes.size) :
    ∃ bm, denoteBM st.denoteL m = some bm := by
  obtain ⟨bi, (_ | u)⟩ := m
  · exact ⟨_, rfl⟩
  · obtain ⟨l, hl⟩ := denoteL_total hwf u (h u (by simp))
    exact ⟨⟨bi, some l⟩, by simp [denoteBM, hl]⟩

/-- On a well-formed store, every in-range index denotes. -/
theorem denote_total {st : EStore} (hwf : st.WF) :
    ∀ (i : EIdx), i < st.nodes.size → ∃ x, st.denote i = some x := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hi
    have hn : st.nodes[i]? = some st.nodes[i] := by
      simp [hi]
    have hc := hwf.children_lt i _ hn
    have hlv := hwf.levels_lt i _ hn
    have hnms := hwf.names_lt i _ hn
    rw [denote_node hn hc]
    have hcs : ∀ c ∈ (st.nodes[i]).children, ∃ x, st.denote c = some x :=
      fun c hcin => ih c (hc c hcin)
        (Nat.lt_trans (hc c hcin) hi)
    cases hnn : st.nodes[i] with
    | bvar k => exact ⟨_, rfl⟩
    | sort u =>
      obtain ⟨l, hl⟩ := denoteL_total hwf u
        (hlv u (by simp [hnn, ENode.levels]))
      exact ⟨_, by rw [denoteNode, hl]; rfl⟩
    | const nm us =>
      obtain ⟨ls, hls⟩ := denoteLList_total hwf us
        (fun u hu => hlv u (by simp [hnn, ENode.levels, hu]))
      obtain ⟨name, hname⟩ := denoteN_total hwf nm
        (hnms nm (by simp [hnn, ENode.names]))
      exact ⟨_, by rw [denoteNode, hls, hname]; rfl⟩
    | lit l => exact ⟨_, rfl⟩
    | fvar idx nm t =>
      obtain ⟨x, hx⟩ := hcs t (by simp [hnn, ENode.children])
      obtain ⟨name, hname⟩ := denoteN_total hwf nm
        (hnms nm (by simp [hnn, ENode.names]))
      exact ⟨_, by rw [denoteNode, hx, hname]; rfl⟩
    | app f a =>
      obtain ⟨xf, hf⟩ := hcs f (by simp [hnn, ENode.children])
      obtain ⟨xa, ha⟩ := hcs a (by simp [hnn, ENode.children])
      exact ⟨_, by rw [denoteNode, hf, ha]; rfl⟩
    | lam nm t b m =>
      obtain ⟨xt, ht⟩ := hcs t (by simp [hnn, ENode.children])
      obtain ⟨xb, hb⟩ := hcs b (by simp [hnn, ENode.children])
      obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
        (fun u hu => hlv u (by simp [hnn, ENode.levels, hu]))
      obtain ⟨name, hname⟩ := denoteN_total hwf nm
        (hnms nm (by simp [hnn, ENode.names]))
      exact ⟨_, by rw [denoteNode, ht, hb, hbm, hname]; rfl⟩
    | forallE nm t b m =>
      obtain ⟨xt, ht⟩ := hcs t (by simp [hnn, ENode.children])
      obtain ⟨xb, hb⟩ := hcs b (by simp [hnn, ENode.children])
      obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
        (fun u hu => hlv u (by simp [hnn, ENode.levels, hu]))
      obtain ⟨name, hname⟩ := denoteN_total hwf nm
        (hnms nm (by simp [hnn, ENode.names]))
      exact ⟨_, by rw [denoteNode, ht, hb, hbm, hname]; rfl⟩
    | letE nm t vv b =>
      obtain ⟨xt, ht⟩ := hcs t (by simp [hnn, ENode.children])
      obtain ⟨xv, hv⟩ := hcs vv (by simp [hnn, ENode.children])
      obtain ⟨xb, hb⟩ := hcs b (by simp [hnn, ENode.children])
      obtain ⟨name, hname⟩ := denoteN_total hwf nm
        (hnms nm (by simp [hnn, ENode.names]))
      exact ⟨_, by rw [denoteNode, ht, hv, hb, hname]; rfl⟩
    | proj s j e' =>
      obtain ⟨x, hx⟩ := hcs e' (by simp [hnn, ENode.children])
      obtain ⟨name, hname⟩ := denoteN_total hwf s
        (hnms s (by simp [hnn, ENode.names]))
      exact ⟨_, by rw [denoteNode, hx, hname]; rfl⟩

/-- Extension never shrinks the node table. -/
theorem Ext.size_le {st st' : EStore} (hext : Ext st st') :
    st.nodes.size ≤ st'.nodes.size := by
  by_cases h0 : st.nodes.size = 0
  · omega
  · have hlast : st.nodes[st.nodes.size - 1]? = some st.nodes[st.nodes.size - 1] := by
      simp
    have := hext.expr _ _ hlast
    have := (Array.getElem?_eq_some_iff.mp this).1
    omega

/-- Extension never shrinks the level table. -/
theorem Ext.lsize_le {st st' : EStore} (hext : Ext st st') :
    st.lnodes.size ≤ st'.lnodes.size := by
  by_cases h0 : st.lnodes.size = 0
  · omega
  · have hlast : st.lnodes[st.lnodes.size - 1]?
        = some st.lnodes[st.lnodes.size - 1] := by
      simp
    have := hext.lvl _ _ hlast
    have := (Array.getElem?_eq_some_iff.mp this).1
    omega

/-- Extension never shrinks the name table. -/
theorem Ext.nsize_le {st st' : EStore} (hext : Ext st st') :
    st.nnodes.size ≤ st'.nnodes.size := by
  cases hsz : st.nnodes.size with
  | zero => exact Nat.zero_le _
  | succ k =>
    have h : st.nnodes[k]? = some st.nnodes[k] := by
      simp [hsz]
    have := hext.name k _ h
    have := (Array.getElem?_eq_some_iff.mp this).1
    omega

/-- Below the old size, an extension does not change the node table. -/
theorem Ext.nodes_eq_of_lt {st st' : EStore} (hext : Ext st st') {j : EIdx}
    (hj : j < st.nodes.size) : st'.nodes[j]? = st.nodes[j]? := by
  have hn : st.nodes[j]? = some st.nodes[j] := by
    simp [hj]
  rw [hn]
  exact hext.expr _ _ hn

/-- Below the old size, an extension does not change the level table. -/
theorem Ext.lnodes_eq_of_lt {st st' : EStore} (hext : Ext st st') {u : LIdx}
    (hu : u < st.lnodes.size) : st'.lnodes[u]? = st.lnodes[u]? := by
  have hn : st.lnodes[u]? = some st.lnodes[u] := by
    simp [hu]
  rw [hn]
  exact hext.lvl _ _ hn

/-- Below the old size, an extension does not change the level
denotation. -/
theorem Ext.denoteL_eq_of_lt {st st' : EStore} (hext : Ext st st') {u : LIdx}
    (hu : u < st.lnodes.size) : st'.denoteL u = st.denoteL u :=
  denoteL_agree (fun _ hv => hext.lnodes_eq_of_lt hv) u hu

/-- Below the old size, an extension does not change the name table. -/
theorem Ext.nnodes_eq_of_lt {st st' : EStore} (hext : Ext st st') {q : NIdx}
    (hq : q < st.nnodes.size) : st'.nnodes[q]? = st.nnodes[q]? := by
  have hn : st.nnodes[q]? = some st.nnodes[q] := by
    simp [hq]
  rw [hn]
  exact hext.name _ _ hn

/-- Below the old size, an extension does not change the name
denotation. -/
theorem Ext.denoteN_eq_of_lt {st st' : EStore} (hext : Ext st st') {q : NIdx}
    (hq : q < st.nnodes.size) : st'.denoteN q = st.denoteN q :=
  denoteN_agree (fun _ hv => hext.nnodes_eq_of_lt hv) q hq

/-- Below the old sizes, an extension does not change the denotation
(not even `none` ones — the guards in `denote` are index-based).
`denote` reads levels only through stored nodes, whose references an
extension preserves; but the raw statement needs the level table
agreement, supplied by `WF` at every use site. -/
theorem Ext.denote_eq_of_lt {st st' : EStore} (hext : Ext st st')
    (hwf : st.WF) {j : EIdx}
    (hj : j < st.nodes.size) : st'.denote j = st.denote j := by
  induction j using Nat.strongRecOn with
  | _ j ih =>
    rw [denote.eq_def, denote.eq_def, hext.nodes_eq_of_lt hj]
    cases hn : st.nodes[j]? with
    | none => rfl
    | some n =>
      refine denoteNode_congr' (fun c _hc => ?_) (fun u hu => ?_)
        (fun q hq => ?_)
      · by_cases hcj : c < j
        · simp only [dif_pos hcj]
          exact ih c hcj (Nat.lt_trans hcj hj)
        · simp [dif_neg hcj]
      · exact hext.denoteL_eq_of_lt (hwf.levels_lt j n hn u hu)
      · exact hext.denoteN_eq_of_lt (hwf.names_lt j n hn q hq)

/-! ## The eager derived-field arrays (task #87)

`bvarBs`/`fvarBs` are total over the arena (`WF`: one entry per node,
satisfying the child recurrence — established at `intern` time from
the children's entries).  The spec functions `Expr.bvarBound` (least
`k` with `looseBVarsBounded k`) and `Expr.fvarRange` (least `d` with
`fvarsBelow d`, `fvar` annotations not descended) tie the entries to
the denotation *exactly* (`WF.bvarBoundD_exact` /
`WF.fvarRangeD_exact`); the traversal cutoffs, the wrappers' root
shortcuts and the `O(1)` `hasFvarI`/`bvarBoundM` reads all reduce to
these. -/

/-- `looseBVarsBounded` is monotone in the bound. -/
theorem lbbMono : ∀ {e : Expr} {k k' : Nat}, k ≤ k' →
    e.looseBVarsBounded k = true → e.looseBVarsBounded k' = true := by
  intro e
  induction e with
  | bvar i =>
    intro k k' hle hb
    simp only [Expr.looseBVarsBounded, decide_eq_true_eq] at hb ⊢
    omega
  | fvar idx n ty ih => intro k k' hle hb; exact hb
  | sort u => intro k k' hle hb; exact hb
  | const n us => intro k k' hle hb; exact hb
  | lit l => intro k k' hle hb; exact hb
  | app f a ihf iha =>
    intro k k' hle hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨ihf hle hb.1, iha hle hb.2⟩
  | lam n ty body m iht ihb =>
    intro k k' hle hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨iht hle hb.1, ihb (Nat.succ_le_succ hle) hb.2⟩
  | forallE n ty body m iht ihb =>
    intro k k' hle hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨iht hle hb.1, ihb (Nat.succ_le_succ hle) hb.2⟩
  | letE n ty val body iht ihv ihb =>
    intro k k' hle hb
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hb ⊢
    exact ⟨⟨iht hle hb.1.1, ihv hle hb.1.2⟩, ihb (Nat.succ_le_succ hle) hb.2⟩
  | proj s j e ihe =>
    intro k k' hle hb
    exact ihe hle hb

/-- The least `k` with `looseBVarsBounded k` (the spec function of the
eager `bvarBs` entries). -/
def _root_.Setlec.Expr.bvarBound : Expr → Nat
  | .bvar i => i + 1
  | .fvar _ _ _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max f.bvarBound a.bvarBound
  | .lam _ ty body _ | .forallE _ ty body _ =>
    max ty.bvarBound (body.bvarBound - 1)
  | .letE _ ty val body =>
    max (max ty.bvarBound val.bvarBound) (body.bvarBound - 1)
  | .proj _ _ e => e.bvarBound

/-- `bvarBound` is exact for `looseBVarsBounded`. -/
theorem looseBVarsBounded_iff {x : Expr} :
    ∀ {k : Nat}, x.looseBVarsBounded k = true ↔ x.bvarBound ≤ k := by
  induction x <;> intro k <;>
    (try simp [Expr.looseBVarsBounded, Expr.bvarBound, Nat.max_le, *]) <;>
    omega

/-- The least `d` with `fvarsBelow d` (the spec function of the eager
`fvarBs` entries; `fvar` type annotations are not descended, matching
`fvarsBelow` and the abstraction traversals). -/
def _root_.Setlec.Expr.fvarRange : Expr → Nat
  | .fvar idx _ _ => idx + 1
  | .bvar _ | .sort _ | .const _ _ | .lit _ => 0
  | .app f a => max f.fvarRange a.fvarRange
  | .lam _ ty body _ | .forallE _ ty body _ =>
    max ty.fvarRange body.fvarRange
  | .letE _ ty val body =>
    max (max ty.fvarRange val.fvarRange) body.fvarRange
  | .proj _ _ e => e.fvarRange

/-- A term is fvar-free iff its range is zero. -/
theorem hasFvar_eq_false_iff {x : Expr} :
    x.hasFvar = false ↔ x.fvarRange = 0 := by
  induction x <;>
    simp_all [Expr.hasFvar, Expr.fvarRange, Nat.max_eq_zero_iff,
      and_assoc]

/-- A term has a reachable fvar leaf iff its range is nonzero. -/
theorem fvarRange_bne_zero {x : Expr} : (x.fvarRange != 0) = x.hasFvar := by
  cases hh : x.hasFvar with
  | false => simp [hasFvar_eq_false_iff.mp hh]
  | true =>
    have hne : x.fvarRange ≠ 0 := by
      intro h0
      rw [hasFvar_eq_false_iff.mpr h0] at hh
      cases hh
    simpa using hne

/-- On a well-formed (flag-off) store the dispatching bound read is
the tier-one array read (tier two is empty, so the fallback is the
default `0` either way; task #64). -/
theorem WF.bvarBoundD_eq_getD {st : EStore} (hwf : st.WF) (e : EIdx) :
    st.bvarBoundD e = st.bvarBs.getD e 0 := by
  unfold bvarBoundD
  split
  · simp
  · rename_i hge
    simp [Array.getD_eq_getD_getElem?, getElem?_size_zero hwf.tbvarBs_nil]

@[inherit_doc WF.bvarBoundD_eq_getD]
theorem WF.fvarRangeD_eq_getD {st : EStore} (hwf : st.WF) (e : EIdx) :
    st.fvarRangeD e = st.fvarBs.getD e 0 := by
  unfold fvarRangeD
  split
  · simp
  · rename_i hge
    simp [Array.getD_eq_getD_getElem?, getElem?_size_zero hwf.tfvarBs_nil]

@[inherit_doc WF.bvarBoundD_eq_getD]
theorem WF.ehasParamD_eq_getD {st : EStore} (hwf : st.WF) (e : EIdx) :
    st.ehasParamD e = st.eparamBs.getD e false := by
  unfold ehasParamD
  split
  · simp
  · rename_i hge
    simp [Array.getD_eq_getD_getElem?, getElem?_size_zero hwf.teparamBs_nil]

/-- The eager bound entry is exactly the spec bound of the node's
denotation. -/
theorem WF.bvarBoundD_exact {st : EStore} (hwf : st.WF) :
    ∀ (i : EIdx) {x : Expr}, st.denote i = some x →
      st.bvarBoundD i = x.bvarBound := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro x hx
    obtain ⟨n, hn, hcl, hdn⟩ := denote_some_inv hx
    have hisz : i < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
    have hread : st.bvarBoundD i = n.bvarBoundOf st.bvarBs := by
      rw [hwf.bvarBoundD_eq_getD, Array.getD_eq_getD_getElem?,
        hwf.bvarBs_spec i n hn]
      rfl
    rw [hread]
    cases n with
    | bvar j =>
      rw [denoteNode] at hdn
      cases hdn
      rfl
    | fvar idx nm t =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, -, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      rfl
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hdn
      obtain ⟨lu, -, rfl⟩ := hdn
      rfl
    | const nm us =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨lus, -, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      rfl
    | lit l =>
      rw [denoteNode] at hdn
      cases hdn
      rfl
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xf, hxf, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨xa, hxa, rfl⟩ := hdn
      have hf := hcl f (by simp [ENode.children])
      have ha := hcl a (by simp [ENode.children])
      show max (st.bvarBs.getD f 0) (st.bvarBs.getD a 0) = _
      rw [← hwf.bvarBoundD_eq_getD f, ← hwf.bvarBoundD_eq_getD a,
        ih f hf hxf, ih a ha hxa]
      rfl
    | lam nm ty body m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨bm, -, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      show max (st.bvarBs.getD ty 0) (st.bvarBs.getD body 0 - 1) = _
      rw [← hwf.bvarBoundD_eq_getD ty, ← hwf.bvarBoundD_eq_getD body,
        ih ty ht hxt, ih body hb hxb]
      rfl
    | forallE nm ty body m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨bm, -, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      show max (st.bvarBs.getD ty 0) (st.bvarBs.getD body 0 - 1) = _
      rw [← hwf.bvarBoundD_eq_getD ty, ← hwf.bvarBoundD_eq_getD body,
        ih ty ht hxt, ih body hb hxb]
      rfl
    | letE nm ty val body =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xv, hxv, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hv := hcl val (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      show max (max (st.bvarBs.getD ty 0) (st.bvarBs.getD val 0))
        (st.bvarBs.getD body 0 - 1) = _
      rw [← hwf.bvarBoundD_eq_getD ty, ← hwf.bvarBoundD_eq_getD val,
        ← hwf.bvarBoundD_eq_getD body,
        ih ty ht hxt, ih val hv hxv, ih body hb hxb]
      rfl
    | proj sp j sub =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xs, hxs, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have hs := hcl sub (by simp [ENode.children])
      show st.bvarBs.getD sub 0 = _
      rw [← hwf.bvarBoundD_eq_getD sub, ih sub hs hxs]
      rfl

/-- The eager range entry is exactly the spec range of the node's
denotation. -/
theorem WF.fvarRangeD_exact {st : EStore} (hwf : st.WF) :
    ∀ (i : EIdx) {x : Expr}, st.denote i = some x →
      st.fvarRangeD i = x.fvarRange := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro x hx
    obtain ⟨n, hn, hcl, hdn⟩ := denote_some_inv hx
    have hisz : i < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
    have hread : st.fvarRangeD i = n.fvarRangeOf st.fvarBs := by
      rw [hwf.fvarRangeD_eq_getD, Array.getD_eq_getD_getElem?,
        hwf.fvarBs_spec i n hn]
      rfl
    rw [hread]
    cases n with
    | bvar j =>
      rw [denoteNode] at hdn
      cases hdn
      rfl
    | fvar idx nm t =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, -, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      rfl
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hdn
      obtain ⟨lu, -, rfl⟩ := hdn
      rfl
    | const nm us =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨lus, -, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      rfl
    | lit l =>
      rw [denoteNode] at hdn
      cases hdn
      rfl
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xf, hxf, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨xa, hxa, rfl⟩ := hdn
      have hf := hcl f (by simp [ENode.children])
      have ha := hcl a (by simp [ENode.children])
      show max (st.fvarBs.getD f 0) (st.fvarBs.getD a 0) = _
      rw [← hwf.fvarRangeD_eq_getD f, ← hwf.fvarRangeD_eq_getD a,
        ih f hf hxf, ih a ha hxa]
      rfl
    | lam nm ty body m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨bm, -, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      show max (st.fvarBs.getD ty 0) (st.fvarBs.getD body 0) = _
      rw [← hwf.fvarRangeD_eq_getD ty, ← hwf.fvarRangeD_eq_getD body,
        ih ty ht hxt, ih body hb hxb]
      rfl
    | forallE nm ty body m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨bm, -, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      show max (st.fvarBs.getD ty 0) (st.fvarBs.getD body 0) = _
      rw [← hwf.fvarRangeD_eq_getD ty, ← hwf.fvarRangeD_eq_getD body,
        ih ty ht hxt, ih body hb hxb]
      rfl
    | letE nm ty val body =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xv, hxv, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hv := hcl val (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      show max (max (st.fvarBs.getD ty 0) (st.fvarBs.getD val 0))
        (st.fvarBs.getD body 0) = _
      rw [← hwf.fvarRangeD_eq_getD ty, ← hwf.fvarRangeD_eq_getD val,
        ← hwf.fvarRangeD_eq_getD body,
        ih ty ht hxt, ih val hv hxv, ih body hb hxb]
      rfl
    | proj sp j sub =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xs, hxs, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have hs := hcl sub (by simp [ENode.children])
      show st.fvarBs.getD sub 0 = _
      rw [← hwf.fvarRangeD_eq_getD sub, ih sub hs hxs]
      rfl

/-- Cutoff consequence: a bound entry at or below the cursor certifies
`looseBVarsBounded` of the denotation (the instantiation traversals'
identity branch). -/
theorem WF.bvarBoundD_le {st : EStore} (hwf : st.WF) {e : EIdx}
    {x : Expr} {d : Nat} (hx : st.denote e = some x)
    (hle : st.bvarBoundD e ≤ d) : x.looseBVarsBounded d = true :=
  looseBVarsBounded_iff.mpr (hwf.bvarBoundD_exact e hx ▸ hle)

/-- Whether a level mentions any parameter (the spec function of the
eager `lparamBs` entries; official kernel `level.cpp` `has_param`,
task #87). -/
def _root_.Setlec.Level.hasParam : Level → Bool
  | .param _ => true
  | .zero => false
  | .succ u => u.hasParam
  | .max u v | .imax u v => u.hasParam || v.hasParam

/-- Substitution is the identity on param-free levels. -/
theorem _root_.Setlec.Level.subst_eq_self {ks : List Name}
    {vs : List Level} {l : Level} (h : l.hasParam = false) :
    l.subst ks vs = l := by
  induction l <;> simp_all [Level.hasParam, Level.subst]

/-- Parameter definedness is trivial on param-free levels. -/
theorem _root_.Setlec.Level.allParamsDefined_of_not_hasParam
    {params : List Name} {l : Level} (h : l.hasParam = false) :
    l.allParamsDefined params = true := by
  induction l <;> simp_all [Level.hasParam, Level.allParamsDefined]

/-- The eager has-param entry is exactly `hasParam` of the level
node's denotation. -/
theorem WF.lhasParamD_exact {st : EStore} (hwf : st.WF) :
    ∀ (u : LIdx) {x : Level}, st.denoteL u = some x →
      st.lhasParamD u = x.hasParam := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro x hx
    obtain ⟨n, hn, hcl, hdn⟩ := denoteL_some_inv hx
    have hread : st.lhasParamD u = n.hasParamOf st.lparamBs := by
      show st.lparamBs.getD u false = n.hasParamOf st.lparamBs
      rw [Array.getD_eq_getD_getElem?, hwf.lparamBs_spec u n hn]
      rfl
    rw [hread]
    cases n with
    | zero =>
      rw [denoteLNode] at hdn
      cases hdn
      rfl
    | param p =>
      rw [denoteLNode] at hdn
      cases hdn
      rfl
    | succ l =>
      rw [denoteLNode, Option.map_eq_some_iff] at hdn
      obtain ⟨xl, hxl, rfl⟩ := hdn
      have hl := hcl l (by simp [LNode.children])
      show st.lhasParamD l = _
      rw [ih l hl hxl]
      rfl
    | max l r =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xl, hxl, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨xr, hxr, rfl⟩ := hdn
      have hl := hcl l (by simp [LNode.children])
      have hr := hcl r (by simp [LNode.children])
      show (st.lhasParamD l || st.lhasParamD r) = _
      rw [ih l hl hxl, ih r hr hxr]
      rfl
    | imax l r =>
      rw [denoteLNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xl, hxl, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨xr, hxr, rfl⟩ := hdn
      have hl := hcl l (by simp [LNode.children])
      have hr := hcl r (by simp [LNode.children])
      show (st.lhasParamD l || st.lhasParamD r) = _
      rw [ih l hl hxl, ih r hr hxr]
      rfl

/-- Prune consequence: a `false` has-param entry certifies the
denotation param-free. -/
theorem WF.lhasParamD_false {st : EStore} (hwf : st.WF) {u : LIdx}
    {x : Level} (hx : st.denoteL u = some x)
    (hp : (!st.lhasParamD u) = true) : x.hasParam = false := by
  rw [Bool.not_eq_eq_eq_not, Bool.not_true] at hp
  rw [← hwf.lhasParamD_exact u hx]
  exact hp

/-- Whether an expression mentions any level parameter (the spec
function of the eager `eparamBs` entries; `fvar` type annotations and
binder-cod annotations included, matching
`Expr.instantiateLevelParams`). -/
def _root_.Setlec.Expr.hasLevelParam : Expr → Bool
  | .bvar _ | .lit _ => false
  | .sort u => u.hasParam
  | .const _ us => us.any Level.hasParam
  | .fvar _ _ ty => ty.hasLevelParam
  | .app f a => f.hasLevelParam || a.hasLevelParam
  | .lam _ ty body m | .forallE _ ty body m =>
    ty.hasLevelParam || body.hasLevelParam ||
      (match m.cod with
       | some v => v.hasParam
       | none => false)
  | .letE _ ty val body =>
    ty.hasLevelParam || val.hasLevelParam || body.hasLevelParam
  | .proj _ _ e => e.hasLevelParam

/-- Level-parameter instantiation is the identity on level-param-free
expressions. -/
theorem _root_.Setlec.Expr.instantiateLevelParams_eq_self
    {ks : List Name} {us : List Level} {x : Expr}
    (h : x.hasLevelParam = false) :
    x.instantiateLevelParams ks us = x := by
  induction x with
  | bvar i => rfl
  | lit l => rfl
  | sort u =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, Level.subst_eq_self h]
  | const nm vs =>
    simp only [Expr.hasLevelParam, List.any_eq_false] at h
    have hmap : vs.map (Level.subst ks us) = vs := by
      induction vs with
      | nil => rfl
      | cons v t iht =>
        simp only [List.map_cons]
        rw [Level.subst_eq_self (by simpa using h v (by simp)),
          iht fun w hw => h w (by simp [hw])]
    simp [Expr.instantiateLevelParams, hmap]
  | fvar idx nm ty ih =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, ih h]
  | app f a ihf iha =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    simp [Expr.instantiateLevelParams, ihf h.1, iha h.2]
  | lam nm ty body m iht ihb =>
    obtain ⟨bi, cod⟩ := m
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hcod⟩ := h
    cases cod with
    | none =>
      simp [Expr.instantiateLevelParams, iht ht, ihb hb]
    | some v =>
      have hcv : v.hasParam = false := hcod
      simp [Expr.instantiateLevelParams, iht ht, ihb hb,
        Level.subst_eq_self hcv]
  | forallE nm ty body m iht ihb =>
    obtain ⟨bi, cod⟩ := m
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hcod⟩ := h
    cases cod with
    | none =>
      simp [Expr.instantiateLevelParams, iht ht, ihb hb]
    | some v =>
      have hcv : v.hasParam = false := hcod
      simp [Expr.instantiateLevelParams, iht ht, ihb hb,
        Level.subst_eq_self hcv]
  | letE nm ty val body iht ihv ihb =>
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    simp [Expr.instantiateLevelParams, iht h.1.1, ihv h.1.2, ihb h.2]
  | proj sp j e ihe =>
    simp only [Expr.hasLevelParam] at h
    simp [Expr.instantiateLevelParams, ihe h]

/-- Level-parameter definedness is trivial on level-param-free
expressions. -/
theorem _root_.Setlec.Expr.allLevelParamsDefined_of_not_hasLevelParam
    {params : List Name} {x : Expr} (h : x.hasLevelParam = false) :
    x.allLevelParamsDefined params = true := by
  induction x with
  | lam nm ty body m iht ihb =>
    obtain ⟨bi, cod⟩ := m
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hcod⟩ := h
    cases cod with
    | none =>
      simp [Expr.allLevelParamsDefined, iht ht, ihb hb]
    | some v =>
      have hcv : v.hasParam = false := hcod
      simp [Expr.allLevelParamsDefined, iht ht, ihb hb,
        Level.allParamsDefined_of_not_hasParam hcv]
  | forallE nm ty body m iht ihb =>
    obtain ⟨bi, cod⟩ := m
    simp only [Expr.hasLevelParam, Bool.or_eq_false_iff] at h
    obtain ⟨⟨ht, hb⟩, hcod⟩ := h
    cases cod with
    | none =>
      simp [Expr.allLevelParamsDefined, iht ht, ihb hb]
    | some v =>
      have hcv : v.hasParam = false := hcod
      simp [Expr.allLevelParamsDefined, iht ht, ihb hb,
        Level.allParamsDefined_of_not_hasParam hcv]
  | const nm vs =>
    simp only [Expr.hasLevelParam, List.any_eq_false] at h
    simp only [Expr.allLevelParamsDefined, List.all_eq_true]
    exact fun v hv =>
      Level.allParamsDefined_of_not_hasParam (by simpa using h v hv)
  | sort u =>
    simp only [Expr.hasLevelParam] at h
    exact Level.allParamsDefined_of_not_hasParam h
  | _ =>
    simp_all [Expr.hasLevelParam, Expr.allLevelParamsDefined]

/-- List form of `lhasParamD` exactness (a `const` node's levels). -/
theorem WF.lhasParamD_list {st : EStore} (hwf : st.WF) :
    ∀ {us : List LIdx} {lus : List Level},
      denoteLList st.denoteL us = some lus →
      us.any (st.lparamBs.getD · false) = lus.any Level.hasParam := by
  intro us
  induction us with
  | nil =>
    intro lus h
    cases h
    rfl
  | cons u us ih =>
    intro lus h
    rw [denoteLList, Option.bind_eq_some_iff] at h
    obtain ⟨l, hl, h⟩ := h
    rw [Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, rfl⟩ := h
    show (st.lhasParamD u || us.any (st.lparamBs.getD · false)) = _
    rw [hwf.lhasParamD_exact u hl, ih hls]
    rfl

/-- The eager has-level-param entry is exactly `hasLevelParam` of the
node's denotation. -/
theorem WF.ehasParamD_exact {st : EStore} (hwf : st.WF) :
    ∀ (i : EIdx) {x : Expr}, st.denote i = some x →
      st.ehasParamD i = x.hasLevelParam := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro x hx
    obtain ⟨n, hn, hcl, hdn⟩ := denote_some_inv hx
    have hread : st.ehasParamD i = n.hasLParamOf st.eparamBs st.lparamBs := by
      rw [hwf.ehasParamD_eq_getD, Array.getD_eq_getD_getElem?,
        hwf.eparamBs_spec i n hn]
      rfl
    rw [hread]
    cases n with
    | bvar j =>
      rw [denoteNode] at hdn
      cases hdn
      rfl
    | lit l =>
      rw [denoteNode] at hdn
      cases hdn
      rfl
    | sort u =>
      rw [denoteNode, Option.map_eq_some_iff] at hdn
      obtain ⟨lu, hlu, rfl⟩ := hdn
      show st.lhasParamD u = _
      rw [hwf.lhasParamD_exact u hlu]
      rfl
    | const nm us =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨lus, hlus, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      exact hwf.lhasParamD_list hlus
    | fvar idx nm t =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have hlt := hcl t (by simp [ENode.children])
      show st.eparamBs.getD t false = _
      rw [← hwf.ehasParamD_eq_getD t, ih t hlt hxt]
      rfl
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xf, hxf, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨xa, hxa, rfl⟩ := hdn
      have hf := hcl f (by simp [ENode.children])
      have ha := hcl a (by simp [ENode.children])
      show (st.eparamBs.getD f false || st.eparamBs.getD a false) = _
      rw [← hwf.ehasParamD_eq_getD f, ← hwf.ehasParamD_eq_getD a,
        ih f hf hxf, ih a ha hxa]
      rfl
    | lam nm ty body m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨bm, hbm, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      obtain ⟨bi, cod⟩ := m
      cases cod with
      | none =>
        rw [denoteBM] at hbm
        cases hbm
        show (st.eparamBs.getD ty false || st.eparamBs.getD body false
            || false) = _
        rw [← hwf.ehasParamD_eq_getD ty, ← hwf.ehasParamD_eq_getD body,
          ih ty ht hxt, ih body hb hxb]
        rfl
      | some u =>
        rw [denoteBM, Option.map_eq_some_iff] at hbm
        obtain ⟨lv, hlv, rfl⟩ := hbm
        show (st.eparamBs.getD ty false || st.eparamBs.getD body false
            || st.lhasParamD u) = _
        rw [← hwf.ehasParamD_eq_getD ty, ← hwf.ehasParamD_eq_getD body,
          ih ty ht hxt, ih body hb hxb, hwf.lhasParamD_exact u hlv]
        rfl
    | forallE nm ty body m =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨bm, hbm, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      obtain ⟨bi, cod⟩ := m
      cases cod with
      | none =>
        rw [denoteBM] at hbm
        cases hbm
        show (st.eparamBs.getD ty false || st.eparamBs.getD body false
            || false) = _
        rw [← hwf.ehasParamD_eq_getD ty, ← hwf.ehasParamD_eq_getD body,
          ih ty ht hxt, ih body hb hxb]
        rfl
      | some u =>
        rw [denoteBM, Option.map_eq_some_iff] at hbm
        obtain ⟨lv, hlv, rfl⟩ := hbm
        show (st.eparamBs.getD ty false || st.eparamBs.getD body false
            || st.lhasParamD u) = _
        rw [← hwf.ehasParamD_eq_getD ty, ← hwf.ehasParamD_eq_getD body,
          ih ty ht hxt, ih body hb hxb, hwf.lhasParamD_exact u hlv]
        rfl
    | letE nm ty val body =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xt, hxt, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xv, hxv, hdn⟩ := hdn
      rw [Option.bind_eq_some_iff] at hdn
      obtain ⟨xb, hxb, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have ht := hcl ty (by simp [ENode.children])
      have hv := hcl val (by simp [ENode.children])
      have hb := hcl body (by simp [ENode.children])
      show (st.eparamBs.getD ty false || st.eparamBs.getD val false
          || st.eparamBs.getD body false) = _
      rw [← hwf.ehasParamD_eq_getD ty, ← hwf.ehasParamD_eq_getD val,
        ← hwf.ehasParamD_eq_getD body,
        ih ty ht hxt, ih val hv hxv, ih body hb hxb]
      rfl
    | proj sp j sub =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xs, hxs, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have hs := hcl sub (by simp [ENode.children])
      show st.eparamBs.getD sub false = _
      rw [← hwf.ehasParamD_eq_getD sub, ih sub hs hxs]
      rfl

/-- Prune consequence: a `false` has-level-param entry certifies the
denotation level-param-free. -/
theorem WF.ehasParamD_false {st : EStore} (hwf : st.WF) {e : EIdx}
    {x : Expr} (hx : st.denote e = some x)
    (hp : (!st.ehasParamD e) = true) : x.hasLevelParam = false := by
  rw [Bool.not_eq_eq_eq_not, Bool.not_true] at hp
  rw [← hwf.ehasParamD_exact e hx]
  exact hp

/-! ## `internExprFast` equals `internExpr` (task #72) -/

/-- Re-interning an already-stored level is a pure lookup: the same
index, the same store — the codomain-chain fast path's justification. -/
theorem internLevel_of_denoteL {st : EStore} (hwf : st.WF) :
    ∀ {l : Level} {i : LIdx}, st.denoteL i = some l →
      st.internLevel l = (i, st) := by
  intro l
  induction l with
  | zero =>
    intro i h
    obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv h
    obtain rfl := denoteLNode_zero_inv hd
    show st.internL .zero = (i, st)
    rw [internL_eq, (hwf.lcons_graph _ i).mpr hn]
  | param p =>
    intro i h
    obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv h
    obtain rfl := denoteLNode_param_inv hd
    show st.internL (.param p) = (i, st)
    rw [internL_eq, (hwf.lcons_graph _ i).mpr hn]
  | succ u ihu =>
    intro i h
    obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv h
    obtain ⟨ui, rfl, hdu⟩ := denoteLNode_succ_inv hd
    show (st.internLevel u).2.internL (.succ (st.internLevel u).1) = (i, st)
    rw [ihu hdu]
    rw [internL_eq, (hwf.lcons_graph _ i).mpr hn]
  | max u v ihu ihv =>
    intro i h
    obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv h
    obtain ⟨ui, vi, rfl, hdu, hdv⟩ := denoteLNode_max_inv hd
    show ((st.internLevel u).2.internLevel v).2.internL
      (.max (st.internLevel u).1 ((st.internLevel u).2.internLevel v).1)
      = (i, st)
    rw [ihu hdu, ihv hdv]
    rw [internL_eq, (hwf.lcons_graph _ i).mpr hn]
  | imax u v ihu ihv =>
    intro i h
    obtain ⟨n, hn, -, hd⟩ := denoteL_some_inv h
    obtain ⟨ui, vi, rfl, hdu, hdv⟩ := denoteLNode_imax_inv hd
    show ((st.internLevel u).2.internLevel v).2.internL
      (.imax (st.internLevel u).1 ((st.internLevel u).2.internLevel v).1)
      = (i, st)
    rw [ihu hdu, ihv hdv]
    rw [internL_eq, (hwf.lcons_graph _ i).mpr hn]

/-- With a valid child-codomain fact, `internBMFast` is `internBM`. -/
theorem internBMFast_eq {st : EStore} (hwf : st.WF) {m : BinderMeta}
    {child : Option (Level × LIdx)}
    (hchild : ∀ v i, child = some (v, i) → st.denoteL i = some v) :
    st.internBMFast m child = st.internBM m := by
  obtain ⟨bi, (_ | v)⟩ := m
  · cases child with
    | none => rfl
    | some p => rfl
  · match child with
    | none => rfl
    | some (vc, ic) =>
      have hden : st.denoteL ic = some vc := hchild vc ic rfl
      cases v with
      | zero => rfl
      | succ u => rfl
      | max u v => rfl
      | param p => rfl
      | imax u vtail =>
        show (if levelPtrBEq vtail vc then _ else _) = _
        by_cases hb : levelPtrBEq vtail vc = true
        · have hvv : vtail = vc := by
            have hbeq : (vtail == vc) = true := hb
            exact eq_of_beq hbeq
          subst hvv
          rw [if_pos hb]
          show ((⟨bi, some ((st.internLevel u).2.internL
              (.imax (st.internLevel u).1 ic)).1⟩ : IBinderMeta),
            ((st.internLevel u).2.internL
              (.imax (st.internLevel u).1 ic)).2)
            = st.internBM ⟨bi, some (.imax u vtail)⟩
          obtain ⟨hwf₁, hext₁, -⟩ := internLevel_spec hwf u
          have hstep : (st.internLevel u).2.internLevel vtail
              = (ic, (st.internLevel u).2) :=
            internLevel_of_denoteL hwf₁ (denoteL_mono hext₁ hden)
          show _ = ((⟨bi, some (st.internLevel (.imax u vtail)).1⟩ :
              IBinderMeta), (st.internLevel (.imax u vtail)).2)
          have hlvl : st.internLevel (.imax u vtail)
              = (st.internLevel u).2.internL
                (.imax (st.internLevel u).1 ic) := by
            show ((st.internLevel u).2.internLevel vtail).2.internL
                (.imax (st.internLevel u).1
                  ((st.internLevel u).2.internLevel vtail).1)
              = _
            rw [hstep]
          rw [hlvl]
        · rw [if_neg hb]
          rfl

/-- The codomain slot of `internBM` on an annotated meta. -/
theorem internBM_cod {st : EStore} (hwf : st.WF) {bi : BinderInfo}
    {v : Level} :
    (st.internBM ⟨bi, some v⟩).1
        = ⟨bi, some (st.internLevel v).1⟩ ∧
      (st.internBM ⟨bi, some v⟩).2 = (st.internLevel v).2 ∧
      (st.internBM ⟨bi, some v⟩).2.denoteL (st.internLevel v).1
        = some v := by
  obtain ⟨-, -, hden⟩ := internLevel_spec hwf v
  exact ⟨rfl, rfl, hden⟩

/-- The fast-path traversal computes exactly `internExpr`, and a
returned codomain fact is valid in the result store. -/
theorem internExprFastGo_eq :
    ∀ (x : Expr) {st : EStore}, st.WF →
      (st.internExprFastGo x).1 = st.internExpr x ∧
      (∀ v i, (st.internExprFastGo x).2 = some (v, i) →
        (st.internExpr x).2.denoteL i = some v) := by
  intro x
  induction x with
  | bvar i =>
    intro st hwf
    exact ⟨rfl, fun v i h => nomatch h⟩
  | sort u =>
    intro st hwf
    exact ⟨rfl, fun v i h => nomatch h⟩
  | const n us =>
    intro st hwf
    exact ⟨rfl, fun v i h => nomatch h⟩
  | lit l =>
    intro st hwf
    exact ⟨rfl, fun v i h => nomatch h⟩
  | fvar idx n ty ih =>
    intro st hwf
    have h1 : (st.internExprFastGo ty).1 = st.internExpr ty := (ih hwf).1
    constructor
    · show (((st.internExprFastGo ty).1.2.internName n).2.intern
          (.fvar idx ((st.internExprFastGo ty).1.2.internName n).1
            (st.internExprFastGo ty).1.1)) = _
      rw [h1]
      rfl
    · intro v i h
      exact nomatch h
  | app f a ihf iha =>
    intro st hwf
    have h1 : (st.internExprFastGo f).1 = st.internExpr f := (ihf hwf).1
    have hwf₁ : (st.internExpr f).2.WF := (internExpr_spec hwf f).1
    have h2 : ((st.internExpr f).2.internExprFastGo a).1
        = (st.internExpr f).2.internExpr a := (iha hwf₁).1
    constructor
    · show (((st.internExprFastGo f).1.2.internExprFastGo a).1.2.intern
          (.app (st.internExprFastGo f).1.1
            ((st.internExprFastGo f).1.2.internExprFastGo a).1.1)) = _
      rw [h1, h2]
      rfl
    · intro v i h
      exact nomatch h
  | proj s j e ihe =>
    intro st hwf
    have h1 : (st.internExprFastGo e).1 = st.internExpr e := (ihe hwf).1
    constructor
    · show (((st.internExprFastGo e).1.2.internName s).2.intern
          (.proj ((st.internExprFastGo e).1.2.internName s).1 j
            (st.internExprFastGo e).1.1)) = _
      rw [h1]
      rfl
    · intro v i h
      exact nomatch h
  | letE n ty val body iht ihv ihb =>
    intro st hwf
    have h1 : (st.internExprFastGo ty).1 = st.internExpr ty := (iht hwf).1
    have hwf₁ : (st.internExpr ty).2.WF := (internExpr_spec hwf ty).1
    have h2 : ((st.internExpr ty).2.internExprFastGo val).1
        = (st.internExpr ty).2.internExpr val := (ihv hwf₁).1
    have hwf₂ : ((st.internExpr ty).2.internExpr val).2.WF :=
      (internExpr_spec hwf₁ val).1
    have h3 : (((st.internExpr ty).2.internExpr val).2.internExprFastGo
          body).1
        = ((st.internExpr ty).2.internExpr val).2.internExpr body :=
      (ihb hwf₂).1
    constructor
    · show (((((st.internExprFastGo ty).1.2.internExprFastGo
          val).1.2.internExprFastGo body).1.2.internName n).2.intern
          (.letE
            ((((st.internExprFastGo ty).1.2.internExprFastGo
              val).1.2.internExprFastGo body).1.2.internName n).1
            (st.internExprFastGo ty).1.1
            ((st.internExprFastGo ty).1.2.internExprFastGo val).1.1
            (((st.internExprFastGo ty).1.2.internExprFastGo
              val).1.2.internExprFastGo body).1.1)) = _
      rw [h1, h2, h3]
      rfl
    · intro v i h
      exact nomatch h
  | lam n ty body m iht ihb =>
    intro st hwf
    have h1 : (st.internExprFastGo ty).1 = st.internExpr ty := (iht hwf).1
    have hwf₁ : (st.internExpr ty).2.WF := (internExpr_spec hwf ty).1
    obtain ⟨h2, hchild⟩ := ihb (st := (st.internExpr ty).2) hwf₁
    have hwf₂ : ((st.internExpr ty).2.internExpr body).2.WF :=
      (internExpr_spec hwf₁ body).1
    have hbm : ((st.internExpr ty).2.internExpr body).2.internBMFast m
          ((st.internExpr ty).2.internExprFastGo body).2
        = ((st.internExpr ty).2.internExpr body).2.internBM m := by
      refine internBMFast_eq hwf₂ ?_
      intro v i h
      exact hchild v i h
    constructor
    · show (((((st.internExprFastGo ty).1.2.internExprFastGo
          body).1.2.internBMFast m
          ((st.internExprFastGo ty).1.2.internExprFastGo
            body).2).2.internName n).2.intern
          (.lam
            (((((st.internExprFastGo ty).1.2.internExprFastGo
              body).1.2.internBMFast m
              ((st.internExprFastGo ty).1.2.internExprFastGo
                body).2).2.internName n).1)
            (st.internExprFastGo ty).1.1
            ((st.internExprFastGo ty).1.2.internExprFastGo body).1.1
            (((st.internExprFastGo ty).1.2.internExprFastGo
              body).1.2.internBMFast m
              ((st.internExprFastGo ty).1.2.internExprFastGo body).2).1)) = _
      rw [h1, h2, hbm]
      rfl
    · intro v i h
      revert h
      show (match m.cod,
          ((((st.internExprFastGo ty).1.2.internExprFastGo
            body).1.2.internBMFast m
            ((st.internExprFastGo ty).1.2.internExprFastGo body).2).1).cod
          with
        | some v, some i => some (v, i)
        | _, _ => none) = some (v, i) → _
      rw [h1, h2, hbm]
      obtain ⟨bi, (_ | v₀)⟩ := m
      · intro h
        exact nomatch h
      · obtain ⟨hm', hst', hden'⟩ := internBM_cod (bi := bi) (v := v₀) hwf₂
        rw [hm']
        intro h
        simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
        show (((((st.internExpr ty).2.internExpr body).2.internBM
            ⟨bi, some v₀⟩).2.internName n).2.intern _).2.denoteL _ = some v₀
        rw [hst']
        exact denoteL_mono (intern_ext _ _)
          (denoteL_mono (internName_ext _ _) hden')
  | forallE n ty body m iht ihb =>
    intro st hwf
    have h1 : (st.internExprFastGo ty).1 = st.internExpr ty := (iht hwf).1
    have hwf₁ : (st.internExpr ty).2.WF := (internExpr_spec hwf ty).1
    obtain ⟨h2, hchild⟩ := ihb (st := (st.internExpr ty).2) hwf₁
    have hwf₂ : ((st.internExpr ty).2.internExpr body).2.WF :=
      (internExpr_spec hwf₁ body).1
    have hbm : ((st.internExpr ty).2.internExpr body).2.internBMFast m
          ((st.internExpr ty).2.internExprFastGo body).2
        = ((st.internExpr ty).2.internExpr body).2.internBM m := by
      refine internBMFast_eq hwf₂ ?_
      intro v i h
      exact hchild v i h
    constructor
    · show (((((st.internExprFastGo ty).1.2.internExprFastGo
          body).1.2.internBMFast m
          ((st.internExprFastGo ty).1.2.internExprFastGo
            body).2).2.internName n).2.intern
          (.forallE
            (((((st.internExprFastGo ty).1.2.internExprFastGo
              body).1.2.internBMFast m
              ((st.internExprFastGo ty).1.2.internExprFastGo
                body).2).2.internName n).1)
            (st.internExprFastGo ty).1.1
            ((st.internExprFastGo ty).1.2.internExprFastGo body).1.1
            (((st.internExprFastGo ty).1.2.internExprFastGo
              body).1.2.internBMFast m
              ((st.internExprFastGo ty).1.2.internExprFastGo body).2).1)) = _
      rw [h1, h2, hbm]
      rfl
    · intro v i h
      revert h
      show (match m.cod,
          ((((st.internExprFastGo ty).1.2.internExprFastGo
            body).1.2.internBMFast m
            ((st.internExprFastGo ty).1.2.internExprFastGo body).2).1).cod
          with
        | some v, some i => some (v, i)
        | _, _ => none) = some (v, i) → _
      rw [h1, h2, hbm]
      obtain ⟨bi, (_ | v₀)⟩ := m
      · intro h
        exact nomatch h
      · obtain ⟨hm', hst', hden'⟩ := internBM_cod (bi := bi) (v := v₀) hwf₂
        rw [hm']
        intro h
        simp only [Option.some.injEq] at h
        obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ h
        show (((((st.internExpr ty).2.internExpr body).2.internBM
            ⟨bi, some v₀⟩).2.internName n).2.intern _).2.denoteL _ = some v₀
        rw [hst']
        exact denoteL_mono (intern_ext _ _)
          (denoteL_mono (internName_ext _ _) hden')

/-- The entry-boundary interning with the codomain-chain fast path is
`internExpr` (task #72). -/
theorem internExprFast_eq {st : EStore} (hwf : st.WF) (e : Expr) :
    st.internExprFast e = st.internExpr e :=
  (internExprFastGo_eq e hwf).1

/-! ## Tier two: dispatch theorems and preservation (task #64)

The tier discipline (`TWF`) makes the tag split a theorem: while tier
two is live the frozen tier-one table sits below `tierTag`
(`flag_bound`), so an index `< tierTag` is tier one (at its identity
position) and an index `≥ tierTag` is tier two with offset
`i - tierTag`, recovered uniquely because `Nat` does not wrap — tier
two itself needs no bound at all (`tierTag ≤ tierTag + j` for every
`j`).  No proof below appeals to practical unreachability. -/

/-- A tier-two index is at or above the tag — for free, `Nat` does not
wrap. -/
theorem tierTwo_idx_ge (j : Nat) : tierTag ≤ tierTag + j :=
  Nat.le_add_right _ _

/-- A tier-two index determines its offset uniquely. -/
theorem tierTwo_idx_offset (j : Nat) : tierTag + j - tierTag = j := by
  omega

/-- With the flag on, stored tier-one indices sit strictly below the
tag (the disambiguation direction that needs the bound). -/
theorem TWF.tierOne_lt_tag {st : EStore} (h : st.TWF)
    (hflag : st.tierTwo = true) {i : EIdx} (hi : i < st.nodes.size) :
    i < tierTag :=
  Nat.lt_of_lt_of_le hi (h.flag_bound hflag)

/-- A stored tier-two node forces the flag on (contrapositive of
`toff_tnil`). -/
theorem TWF.flag_of_tnodes {st : EStore} (h : st.TWF) {j : Nat}
    {n : ENode} (hj : st.tnodes[j]? = some n) : st.tierTwo = true := by
  cases hb : st.tierTwo
  · rw [h.toff_tnodes_none hb] at hj
    cases hj
  · rfl

/-- `getNode` below the tier-one size is the identity read (no bound
needed: tier one is the identity embedding). -/
theorem getNode_lt {st : EStore} {i : EIdx} (h : i < st.nodes.size) :
    st.getNode i = some st.nodes[i] := by
  unfold getNode
  rw [dif_pos h]

/-- `getNode` of a stored tier-one node. -/
theorem getNode_of_stored {st : EStore} {i : EIdx} {n : ENode}
    (h : st.nodes[i]? = some n) : st.getNode i = some n := by
  have hi : i < st.nodes.size := (Array.getElem?_eq_some_iff.mp h).1
  rw [getNode_lt hi, ← Array.getElem?_eq_getElem hi]
  exact h

/-- On a flag-off well-formed store `getNode` *is* the tier-one
read. -/
theorem WF.getNode_eq {st : EStore} (hwf : st.WF) (i : EIdx) :
    st.getNode i = st.nodes[i]? := by
  unfold getNode
  split
  · rename_i hlt
    rw [Array.getElem?_eq_getElem hlt]
  · rename_i hge
    rw [getElem?_size_zero (hwf.toff_tnil hwf.tier_off),
      Array.getElem?_eq_none (Nat.le_of_not_lt hge)]

/-- With tier two live, `getNode` reads a stored tier-two node at its
tagged index (the other disambiguation direction; the bound keeps the
tagged index out of the tier-one branch). -/
theorem TWF.getNode_tierTwo {st : EStore} (h : st.TWF) {j : Nat}
    {n : ENode} (hj : st.tnodes[j]? = some n) :
    st.getNode (tierTag + j) = some n := by
  have hbound : ¬ tierTag + j < st.nodes.size :=
    Nat.not_lt.mpr (Nat.le_trans (h.flag_bound (h.flag_of_tnodes hj))
      (tierTwo_idx_ge j))
  unfold getNode
  rw [dif_neg hbound, tierTwo_idx_offset]
  exact hj

/-- The dispatching bound read of a stored tier-two node is its
tier-blind recurrence entry. -/
theorem TWF.bvarBoundD_tierTwo {st : EStore} (h : st.TWF) {j : Nat}
    {n : ENode} (hj : st.tnodes[j]? = some n) :
    st.bvarBoundD (tierTag + j) = st.nodeBvarBound n := by
  have hbound : ¬ tierTag + j < st.bvarBs.size := by
    rw [h.bvarBs_size]
    exact Nat.not_lt.mpr (Nat.le_trans
      (h.flag_bound (h.flag_of_tnodes hj)) (tierTwo_idx_ge j))
  unfold bvarBoundD
  rw [dif_neg hbound, tierTwo_idx_offset,
    Array.getD_eq_getD_getElem?, h.t_bvarBs_spec j n hj]
  rfl

@[inherit_doc TWF.bvarBoundD_tierTwo]
theorem TWF.fvarRangeD_tierTwo {st : EStore} (h : st.TWF) {j : Nat}
    {n : ENode} (hj : st.tnodes[j]? = some n) :
    st.fvarRangeD (tierTag + j) = st.nodeFvarRange n := by
  have hbound : ¬ tierTag + j < st.fvarBs.size := by
    rw [h.fvarBs_size]
    exact Nat.not_lt.mpr (Nat.le_trans
      (h.flag_bound (h.flag_of_tnodes hj)) (tierTwo_idx_ge j))
  unfold fvarRangeD
  rw [dif_neg hbound, tierTwo_idx_offset,
    Array.getD_eq_getD_getElem?, h.t_fvarBs_spec j n hj]
  rfl

@[inherit_doc TWF.bvarBoundD_tierTwo]
theorem TWF.ehasParamD_tierTwo {st : EStore} (h : st.TWF) {j : Nat}
    {n : ENode} (hj : st.tnodes[j]? = some n) :
    st.ehasParamD (tierTag + j) = st.nodeHasLParam n := by
  have hbound : ¬ tierTag + j < st.eparamBs.size := by
    rw [h.eparamBs_size]
    exact Nat.not_lt.mpr (Nat.le_trans
      (h.flag_bound (h.flag_of_tnodes hj)) (tierTwo_idx_ge j))
  unfold ehasParamD
  rw [dif_neg hbound, tierTwo_idx_offset,
    Array.getD_eq_getD_getElem?, h.t_eparamBs_spec j n hj]
  rfl

/-- `internT` preserves the two-tier invariant: the tier-one clauses
are untouched (tier one is frozen), and the tier-two clauses extend by
one node whose children are valid two-tier indices. -/
theorem internT_twf {st : EStore} {n : ENode} (h : st.TWF)
    (hflag : st.tierTwo = true)
    (hc : ∀ c ∈ n.children, st.Valid2 c)
    (hlv : ∀ u ∈ n.levels, u < st.lnodes.size)
    (hnm : ∀ p ∈ n.names, p < st.nnodes.size) : (st.internT n).2.TWF := by
  have hbound : st.nodes.size ≤ tierTag := h.flag_bound hflag
  have hbb : st.bvarBs.size ≤ tierTag := by
    rw [h.bvarBs_size]
    exact hbound
  have hfb : st.fvarBs.size ≤ tierTag := by
    rw [h.fvarBs_size]
    exact hbound
  have heb : st.eparamBs.size ≤ tierTag := by
    rw [h.eparamBs_size]
    exact hbound
  rw [internT_eq]
  split
  · exact h
  · rename_i hmiss1
    split
    · exact h
    · rename_i hmiss2
      constructor
      · exact h.children_lt
      · exact h.cons_graph
      · exact h.levels_lt
      · exact h.lchildren_lt
      · exact h.lcons_graph
      · exact h.bvarBs_size
      · exact h.fvarBs_size
      · exact h.bvarBs_spec
      · exact h.fvarBs_spec
      · exact h.lparamBs_size
      · exact h.lparamBs_spec
      · exact h.eparamBs_size
      · exact h.eparamBs_spec
      · exact h.names_lt
      · exact h.nchildren_lt
      · exact h.ncons_graph
      · exact h.rbNames_size
      · exact h.rbNames_spec
      · exact fun _ => hbound
      · intro hoff
        exact absurd hoff (by simp [hflag])
      · intro j m hj c hcin
        rw [Array.getElem?_push] at hj
        split at hj
        · cases hj
          subst_eqs
          exact hc c hcin
        · exact h.t_children_lt j m hj c hcin
      · intro j m hj u hu
        rw [Array.getElem?_push] at hj
        split at hj
        · cases hj
          subst_eqs
          exact hlv u hu
        · exact h.t_levels_lt j m hj u hu
      · intro j m hj p hp
        rw [Array.getElem?_push] at hj
        split at hj
        · cases hj
          subst_eqs
          exact hnm p hp
        · exact h.t_names_lt j m hj p hp
      · intro m i
        constructor
        · intro hmi
          rw [Std.HashMap.getElem?_insert] at hmi
          by_cases hnm' : n = m
          · subst hnm'
            simp only [BEq.rfl, if_pos] at hmi
            cases hmi
            refine ⟨tierTwo_idx_ge _, ?_⟩
            rw [tierTwo_idx_offset, Array.getElem?_push, if_pos rfl]
          · rw [if_neg (by simpa using hnm')] at hmi
            obtain ⟨htag, hold⟩ := (h.t_cons_graph m i).mp hmi
            have hlt : i - tierTag < st.tnodes.size :=
              (Array.getElem?_eq_some_iff.mp hold).1
            refine ⟨htag, ?_⟩
            rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hlt)]
            exact hold
        · rintro ⟨htag, hpush⟩
          rw [Array.getElem?_push] at hpush
          split at hpush
          · rename_i hoff
            cases hpush
            have hieq : i = tierTag + st.tnodes.size := by
              rw [← hoff, Nat.add_sub_cancel' htag]
            subst hieq
            rw [Std.HashMap.getElem?_insert]
            simp
          · rename_i hoff
            have hmi := (h.t_cons_graph m i).mpr ⟨htag, hpush⟩
            rw [Std.HashMap.getElem?_insert]
            have hne : ¬ n = m := by
              rintro rfl
              rw [hmiss2] at hmi
              cases hmi
            rw [if_neg (by simpa using hne)]
            exact hmi
      · intro m i hmi
        rw [Std.HashMap.getElem?_insert] at hmi
        by_cases hnm' : n = m
        · subst hnm'
          exact hmiss1
        · rw [if_neg (by simpa using hnm')] at hmi
          exact h.t_cons_fresh m i hmi
      · simpa using h.t_bvarBs_size
      · simpa using h.t_fvarBs_size
      · simpa using h.t_eparamBs_size
      · intro j m hj
        rw [Array.getElem?_push] at hj
        split at hj
        · cases hj
          subst_eqs
          rw [Array.getElem?_push, h.t_bvarBs_size, if_pos rfl]
          refine congrArg some (nodeBvarBound_congr fun c hcin => ?_)
          have hv : c < st.bvarBs.size ∨
              (tierTag ≤ c ∧ c - tierTag < st.tbvarBs.size) := by
            rw [h.bvarBs_size, h.t_bvarBs_size]
            exact hc c hcin
          unfold bvarBoundD
          exact (tierRead_push_stable hbb hv).symm
        · rename_i hne
          have hjlt : j < st.tnodes.size :=
            (Array.getElem?_eq_some_iff.mp hj).1
          rw [Array.getElem?_push, h.t_bvarBs_size,
            if_neg (Nat.ne_of_lt hjlt), h.t_bvarBs_spec j m hj]
          refine congrArg some (nodeBvarBound_congr fun c hcin => ?_)
          have hv : c < st.bvarBs.size ∨
              (tierTag ≤ c ∧ c - tierTag < st.tbvarBs.size) := by
            rw [h.bvarBs_size, h.t_bvarBs_size]
            rcases h.t_children_lt j m hj c hcin with hlt | ⟨htg, ho⟩
            · exact .inl hlt
            · exact .inr ⟨htg, Nat.lt_trans ho hjlt⟩
          unfold bvarBoundD
          exact (tierRead_push_stable hbb hv).symm
      · intro j m hj
        rw [Array.getElem?_push] at hj
        split at hj
        · cases hj
          subst_eqs
          rw [Array.getElem?_push, h.t_fvarBs_size, if_pos rfl]
          refine congrArg some (nodeFvarRange_congr fun c hcin => ?_)
          have hv : c < st.fvarBs.size ∨
              (tierTag ≤ c ∧ c - tierTag < st.tfvarBs.size) := by
            rw [h.fvarBs_size, h.t_fvarBs_size]
            exact hc c hcin
          unfold fvarRangeD
          exact (tierRead_push_stable hfb hv).symm
        · rename_i hne
          have hjlt : j < st.tnodes.size :=
            (Array.getElem?_eq_some_iff.mp hj).1
          rw [Array.getElem?_push, h.t_fvarBs_size,
            if_neg (Nat.ne_of_lt hjlt), h.t_fvarBs_spec j m hj]
          refine congrArg some (nodeFvarRange_congr fun c hcin => ?_)
          have hv : c < st.fvarBs.size ∨
              (tierTag ≤ c ∧ c - tierTag < st.tfvarBs.size) := by
            rw [h.fvarBs_size, h.t_fvarBs_size]
            rcases h.t_children_lt j m hj c hcin with hlt | ⟨htg, ho⟩
            · exact .inl hlt
            · exact .inr ⟨htg, Nat.lt_trans ho hjlt⟩
          unfold fvarRangeD
          exact (tierRead_push_stable hfb hv).symm
      · intro j m hj
        rw [Array.getElem?_push] at hj
        split at hj
        · cases hj
          subst_eqs
          rw [Array.getElem?_push, h.t_eparamBs_size, if_pos rfl]
          refine congrArg some
            (nodeHasLParam_congr (fun c hcin => ?_) (fun u _ => rfl))
          have hv : c < st.eparamBs.size ∨
              (tierTag ≤ c ∧ c - tierTag < st.teparamBs.size) := by
            rw [h.eparamBs_size, h.t_eparamBs_size]
            exact hc c hcin
          unfold ehasParamD
          exact (tierRead_push_stable heb hv).symm
        · rename_i hne
          have hjlt : j < st.tnodes.size :=
            (Array.getElem?_eq_some_iff.mp hj).1
          rw [Array.getElem?_push, h.t_eparamBs_size,
            if_neg (Nat.ne_of_lt hjlt), h.t_eparamBs_spec j m hj]
          refine congrArg some
            (nodeHasLParam_congr (fun c hcin => ?_) (fun u _ => rfl))
          have hv : c < st.eparamBs.size ∨
              (tierTag ≤ c ∧ c - tierTag < st.teparamBs.size) := by
            rw [h.eparamBs_size, h.t_eparamBs_size]
            rcases h.t_children_lt j m hj c hcin with hlt | ⟨htg, ho⟩
            · exact .inl hlt
            · exact .inr ⟨htg, Nat.lt_trans ho hjlt⟩
          unfold ehasParamD
          exact (tierRead_push_stable heb hv).symm

/-- The dispatching intern preserves the two-tier invariant given
valid two-tier children (levels and names stay single-tier). -/
theorem intern_twf {st : EStore} {n : ENode} (h : st.TWF)
    (hc : ∀ c ∈ n.children, st.Valid2 c)
    (hlv : ∀ u ∈ n.levels, u < st.lnodes.size)
    (hnm : ∀ p ∈ n.names, p < st.nnodes.size) : (st.intern n).2.TWF := by
  cases hflag : st.tierTwo with
  | false =>
    have hc' : ∀ c ∈ n.children, c < st.nodes.size := by
      intro c hcin
      rcases hc c hcin with hlt | ⟨-, ho⟩
      · exact hlt
      · rw [h.toff_tnil hflag] at ho
        exact absurd ho (Nat.not_lt_zero _)
    exact (intern_wf ⟨h, hflag⟩ hc' hlv hnm).toTWF
  | true =>
    rw [intern_on hflag]
    exact internT_twf h hflag hc hlv hnm

/-- The dispatching intern stores the node tier-blind: `getNode` at
the returned index reads it back. -/
theorem intern_getNode {st : EStore} {n : ENode} (h : st.TWF) :
    (st.intern n).2.getNode (st.intern n).1 = some n := by
  cases hflag : st.tierTwo with
  | false =>
    exact getNode_of_stored (intern_node ⟨h, hflag⟩)
  | true =>
    have hbound := h.flag_bound hflag
    rw [intern_on hflag, internT_eq]
    split
    · rename_i i hcons
      exact getNode_of_stored ((h.cons_graph n i).mp hcons)
    · split
      · rename_i i htcons
        obtain ⟨htag, hold⟩ := (h.t_cons_graph n i).mp htcons
        have hieq : i = tierTag + (i - tierTag) :=
          (Nat.add_sub_cancel' htag).symm
        rw [hieq]
        exact h.getNode_tierTwo hold
      · have hkey : ¬ tierTag + st.tnodes.size < st.nodes.size :=
          Nat.not_lt.mpr (Nat.le_trans hbound (tierTwo_idx_ge _))
        simp [getNode, hkey]

/-- The dispatching intern returns a valid two-tier index. -/
theorem intern_valid2 {st : EStore} {n : ENode} (h : st.TWF) :
    (st.intern n).2.Valid2 (st.intern n).1 := by
  cases hflag : st.tierTwo with
  | false =>
    exact .inl (intern_lt_size ⟨h, hflag⟩)
  | true =>
    rw [intern_on hflag, internT_eq]
    split
    · rename_i i hcons
      exact .inl (Array.getElem?_eq_some_iff.mp
        ((h.cons_graph n i).mp hcons)).1
    · split
      · rename_i i htcons
        obtain ⟨htag, hold⟩ := (h.t_cons_graph n i).mp htcons
        exact .inr ⟨htag, (Array.getElem?_eq_some_iff.mp hold).1⟩
      · exact .inr ⟨tierTwo_idx_ge _, by simp⟩

/-- Two-tier validity is monotone under interning (both tiers only
grow). -/
theorem valid2_mono_intern {st : EStore} {n : ENode} {c : EIdx}
    (hv : st.Valid2 c) : (st.intern n).2.Valid2 c := by
  unfold intern
  split
  · rw [internT_eq]
    split
    · exact hv
    · split
      · exact hv
      · rcases hv with hlt | ⟨htg, ho⟩
        · exact .inl hlt
        · exact .inr ⟨htg, by simpa using Nat.lt_succ_of_lt ho⟩
  · rw [internP_eq]
    split
    · exact hv
    · rcases hv with hlt | ⟨htg, ho⟩
      · exact .inl (by simpa using Nat.lt_succ_of_lt hlt)
      · exact .inr ⟨htg, ho⟩

/-! ### `enableTierTwo`: the mode switch -/

/-- `enableTierTwo` changes at most the flag. -/
theorem enableTierTwo_eq_set {st : EStore} (h : st.nodes.size ≤ tierTag) :
    st.enableTierTwo = { st with tierTwo := true } := by
  unfold enableTierTwo
  rw [if_pos h]

theorem enableTierTwo_eq_self {st : EStore}
    (h : ¬ st.nodes.size ≤ tierTag) : st.enableTierTwo = st := by
  unfold enableTierTwo
  rw [if_neg h]

@[simp] theorem enableTierTwo_nodes (st : EStore) :
    st.enableTierTwo.nodes = st.nodes := by
  unfold enableTierTwo
  split <;> rfl

@[simp] theorem enableTierTwo_lnodes (st : EStore) :
    st.enableTierTwo.lnodes = st.lnodes := by
  unfold enableTierTwo
  split <;> rfl

@[simp] theorem enableTierTwo_nnodes (st : EStore) :
    st.enableTierTwo.nnodes = st.nnodes := by
  unfold enableTierTwo
  split <;> rfl

@[simp] theorem enableTierTwo_cons (st : EStore) :
    st.enableTierTwo.cons = st.cons := by
  unfold enableTierTwo
  split <;> rfl

@[simp] theorem enableTierTwo_tnodes (st : EStore) :
    st.enableTierTwo.tnodes = st.tnodes := by
  unfold enableTierTwo
  split <;> rfl

/-- Enabling changes no tier-one observation: extension is trivial. -/
theorem enableTierTwo_ext (st : EStore) : Ext st st.enableTierTwo :=
  ⟨fun i m h => by rw [enableTierTwo_nodes]; exact h,
   fun u m h => by rw [enableTierTwo_lnodes]; exact h,
   fun i m h => by rw [enableTierTwo_nnodes]; exact h⟩

/-- Enabling is invisible to the denotation. -/
theorem enableTierTwo_denote (st : EStore) :
    ∀ i, st.enableTierTwo.denote i = st.denote i := fun i =>
  denote_agree (k := i + 1) (fun j _ => by rw [enableTierTwo_nodes])
    (enableTierTwo_lnodes st) (enableTierTwo_nnodes st) i (Nat.lt_succ_self i)

/-- `enableTierTwo` preserves the two-tier invariant: the guard is
exactly the tag bound (`flag_bound`), checked once at the mode switch
(validate-at-insertion, task #42).  On guard failure the store is
unchanged. -/
theorem enableTierTwo_twf {st : EStore} (h : st.TWF) :
    st.enableTierTwo.TWF := by
  unfold enableTierTwo
  split
  · rename_i hle
    constructor
    · exact h.children_lt
    · exact h.cons_graph
    · exact h.levels_lt
    · exact h.lchildren_lt
    · exact h.lcons_graph
    · exact h.bvarBs_size
    · exact h.fvarBs_size
    · exact h.bvarBs_spec
    · exact h.fvarBs_spec
    · exact h.lparamBs_size
    · exact h.lparamBs_spec
    · exact h.eparamBs_size
    · exact h.eparamBs_spec
    · exact h.names_lt
    · exact h.nchildren_lt
    · exact h.ncons_graph
    · exact h.rbNames_size
    · exact h.rbNames_spec
    · exact fun _ => hle
    · intro hoff
      simp at hoff
    · exact h.t_children_lt
    · exact h.t_levels_lt
    · exact h.t_names_lt
    · exact h.t_cons_graph
    · exact h.t_cons_fresh
    · exact h.t_bvarBs_size
    · exact h.t_fvarBs_size
    · exact h.t_eparamBs_size
    · exact h.t_bvarBs_spec
    · exact h.t_fvarBs_spec
    · exact h.t_eparamBs_spec
  · exact h

/-! ### `truncateTierTwo`: drop tier two, keep every tier-one
observation -/

/-- `truncateTierTwo` with the destructuring eliminated. -/
theorem truncateTierTwo_eq (st : EStore) :
    st.truncateTierTwo =
      ⟨st.nodes, st.cons, st.lnodes, st.lcons, st.bvarBs, st.fvarBs,
        st.lparamBs, st.eparamBs, st.nnodes, st.ncons, st.rbNames,
        false, st.tnodes.shrink 0, {}, st.tbvarBs.shrink 0,
        st.tfvarBs.shrink 0, st.teparamBs.shrink 0⟩ := by
  obtain ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
    nnodes, ncons, rbNames, tierTwo, tnodes, tcons, tbvarBs, tfvarBs,
    teparamBs⟩ := st
  rfl

@[simp] theorem truncateTierTwo_nodes (st : EStore) :
    st.truncateTierTwo.nodes = st.nodes := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_cons (st : EStore) :
    st.truncateTierTwo.cons = st.cons := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_lnodes (st : EStore) :
    st.truncateTierTwo.lnodes = st.lnodes := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_lcons (st : EStore) :
    st.truncateTierTwo.lcons = st.lcons := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_bvarBs (st : EStore) :
    st.truncateTierTwo.bvarBs = st.bvarBs := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_fvarBs (st : EStore) :
    st.truncateTierTwo.fvarBs = st.fvarBs := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_lparamBs (st : EStore) :
    st.truncateTierTwo.lparamBs = st.lparamBs := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_eparamBs (st : EStore) :
    st.truncateTierTwo.eparamBs = st.eparamBs := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_nnodes (st : EStore) :
    st.truncateTierTwo.nnodes = st.nnodes := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_ncons (st : EStore) :
    st.truncateTierTwo.ncons = st.ncons := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_rbNames (st : EStore) :
    st.truncateTierTwo.rbNames = st.rbNames := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_tierTwo (st : EStore) :
    st.truncateTierTwo.tierTwo = false := by
  rw [truncateTierTwo_eq]

@[simp] theorem truncateTierTwo_tnodes_size (st : EStore) :
    st.truncateTierTwo.tnodes.size = 0 := by
  rw [truncateTierTwo_eq]
  simp

/-- Truncation preserves well-formedness — and yields the *flag-off*
invariant `WF`, so the store re-enters the fully verified single-tier
regime. -/
theorem truncateTierTwo_wf {st : EStore} (h : st.TWF) :
    st.truncateTierTwo.WF := by
  have hnil : ∀ j : Nat, (st.tnodes.shrink 0)[j]? = none :=
    getElem?_size_zero (by simp)
  rw [truncateTierTwo_eq]
  refine ⟨?_, rfl⟩
  constructor
  · exact h.children_lt
  · exact h.cons_graph
  · exact h.levels_lt
  · exact h.lchildren_lt
  · exact h.lcons_graph
  · exact h.bvarBs_size
  · exact h.fvarBs_size
  · exact h.bvarBs_spec
  · exact h.fvarBs_spec
  · exact h.lparamBs_size
  · exact h.lparamBs_spec
  · exact h.eparamBs_size
  · exact h.eparamBs_spec
  · exact h.names_lt
  · exact h.nchildren_lt
  · exact h.ncons_graph
  · exact h.rbNames_size
  · exact h.rbNames_spec
  · intro hflag
    simp at hflag
  · intro _
    simp
  · intro j m hj
    simp at hj
  · intro j m hj
    simp at hj
  · intro j m hj
    simp at hj
  · intro m i
    constructor
    · intro hmi
      simp at hmi
    · rintro ⟨-, hpush⟩
      simp at hpush
  · intro m i hmi
    simp at hmi
  · simp
  · simp
  · simp
  · intro j m hj
    simp at hj
  · intro j m hj
    simp at hj
  · intro j m hj
    simp at hj

/-- Truncation extends (tier-one tables untouched). -/
theorem truncateTierTwo_ext (st : EStore) : Ext st st.truncateTierTwo :=
  ⟨fun i m h => by rw [truncateTierTwo_nodes]; exact h,
   fun u m h => by rw [truncateTierTwo_lnodes]; exact h,
   fun i m h => by rw [truncateTierTwo_nnodes]; exact h⟩

/-- Truncation is invisible to the denotation — at *every* index:
`denote` reads only the tier-one tables. -/
theorem truncateTierTwo_denote (st : EStore) :
    ∀ i, st.truncateTierTwo.denote i = st.denote i := fun i =>
  denote_agree (k := i + 1) (fun j _ => by rw [truncateTierTwo_nodes])
    (truncateTierTwo_lnodes st) (truncateTierTwo_nnodes st) i
    (Nat.lt_succ_self i)

@[inherit_doc truncateTierTwo_denote]
theorem truncateTierTwo_denoteL (st : EStore) :
    ∀ u, st.truncateTierTwo.denoteL u = st.denoteL u :=
  denoteL_eq_of_lnodes_eq (truncateTierTwo_lnodes st)

@[inherit_doc truncateTierTwo_denote]
theorem truncateTierTwo_denoteN (st : EStore) :
    ∀ i, st.truncateTierTwo.denoteN i = st.denoteN i :=
  denoteN_eq_of_nnodes_eq (truncateTierTwo_nnodes st)

/-- Truncation is the identity on `getNode` at tier-one indices. -/
theorem truncateTierTwo_getNode {st : EStore} {i : EIdx}
    (h : i < st.nodes.size) :
    st.truncateTierTwo.getNode i = st.getNode i := by
  rw [getNode_lt h, getNode_lt (i := i) (by simpa using h)]
  simp

/-- Truncation is the identity on the dispatching derived reads at
tier-one positions. -/
theorem truncateTierTwo_bvarBoundD {st : EStore} {e : EIdx}
    (h : e < st.bvarBs.size) :
    st.truncateTierTwo.bvarBoundD e = st.bvarBoundD e := by
  unfold bvarBoundD
  rw [dif_pos h, dif_pos (by simpa using h)]
  simp

@[inherit_doc truncateTierTwo_bvarBoundD]
theorem truncateTierTwo_fvarRangeD {st : EStore} {e : EIdx}
    (h : e < st.fvarBs.size) :
    st.truncateTierTwo.fvarRangeD e = st.fvarRangeD e := by
  unfold fvarRangeD
  rw [dif_pos h, dif_pos (by simpa using h)]
  simp

@[inherit_doc truncateTierTwo_bvarBoundD]
theorem truncateTierTwo_ehasParamD {st : EStore} {e : EIdx}
    (h : e < st.eparamBs.size) :
    st.truncateTierTwo.ehasParamD e = st.ehasParamD e := by
  unfold ehasParamD
  rw [dif_pos h, dif_pos (by simpa using h)]
  simp

/-- Truncation is the identity on the level has-param read (levels are
single-tier). -/
theorem truncateTierTwo_lhasParamD (st : EStore) (u : LIdx) :
    st.truncateTierTwo.lhasParamD u = st.lhasParamD u := by
  unfold lhasParamD
  rw [truncateTierTwo_lparamBs]

end EStore

end Setlec
