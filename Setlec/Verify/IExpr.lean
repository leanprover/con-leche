import Setlec.Kernel.IExpr
import Setlec.Kernel.Core
import Setlec.Verify.AbstractRange
import Setlec.Verify.Subst

/-!
# Verification of the interned expression arena

`denote` reads an interned index back as a `Setlec.Expr`; `EStore.WF`
is the store invariant (children strictly below their parent, cons-table
exactly the graph of the node table).  The lemmas connect the arena
operations of `Setlec/Kernel/IExpr.lean` to their `Expr` counterparts:
interning round-trips through `denote`, denotation is stable under store
extension, index equality is expression equality (canonicity), and each
syntactic operation commutes with `denote`.

Progress (stage 1 tracking):
* [x] `children` / `denoteNode` / `denote`
* [x] `EStore.WF`, `EStore.Ext`, `denote_mono`
* [x] `intern` preserves `WF`; `internExpr` round-trips
* [x] canonicity: `denote_inj` / `denote_eq_iff` (O(1) equality)
* [x] `instantiate1I` commutes with `denote`
* [x] `abstract1I`, `instantiateLevelParamsI` commute with `denote`
* [x] pure queries (`hasFvarI`, `looseBVarsBoundedI`, `wscopedBI`,
      `fvarLeavesI`, `constsResolveI`) agree with the `Expr` versions
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

/-- The store invariant: every node's children are strictly below its
own index, expression nodes' level references are in range, and each
cons-table is exactly the graph of its node table (in particular no
node is stored at two indices). -/
structure WF (st : EStore) : Prop where
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

theorem empty_wf : WF EStore.empty := by
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

/-- `intern` with the store destructuring (an RC optimization)
eliminated. -/
theorem intern_eq (st : EStore) (n : ENode) :
    st.intern n = match st.cons[n]? with
      | some i => (i, st)
      | none =>
        (st.nodes.size, ⟨st.nodes.push n, st.cons.insert n st.nodes.size,
          st.lnodes, st.lcons,
          st.bvarBs.push (n.bvarBoundOf st.bvarBs),
          st.fvarBs.push (n.fvarRangeOf st.fvarBs), st.lparamBs,
          st.eparamBs.push (n.hasLParamOf st.eparamBs st.lparamBs),
          st.nnodes, st.ncons⟩) := by
  obtain ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
    nnodes, ncons⟩ := st
  rfl

theorem intern_ext (st : EStore) (n : ENode) : Ext st (st.intern n).2 := by
  refine ⟨fun i m h => ?_, fun u m h => ?_, fun i m h => ?_⟩
  · rw [intern_eq]
    split
    · exact h
    · have : i < st.nodes.size := (Array.getElem?_eq_some_iff.mp h).1
      rw [Array.getElem?_push, if_neg (Nat.ne_of_lt this)]
      exact h
  · rw [intern_eq]
    split
    · exact h
    · exact h
  · rw [intern_eq]
    split
    · exact h
    · exact h

/-- Interning stores the node at the returned index. -/
theorem intern_node {st : EStore} {n : ENode} (hwf : st.WF) :
    (st.intern n).2.nodes[(st.intern n).1]? = some n := by
  rw [intern_eq]
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
  rw [intern_eq]
  split
  · exact hwf
  · rename_i hmiss
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

/-- Interning a node whose children are already stored: the result
denotes the node's denotation over the *old* store. -/
theorem intern_denote {st : EStore} {n : ENode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nodes.size) :
    (st.intern n).2.denote (st.intern n).1
      = denoteNode st.denote st.denoteL st.denoteN n := by
  have hn := intern_node (n := n) hwf
  rw [intern_eq] at hn ⊢
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
          st.nnodes, st.ncons⟩
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
          st.nnodes, st.ncons⟩
          : EStore)) (st := st)
        rfl u)
      (fun q _ => denoteN_eq_of_nnodes_eq
        (st' := (⟨st.nodes.push n, st.cons.insert n st.nodes.size,
          st.lnodes, st.lcons,
          st.bvarBs.push (n.bvarBoundOf st.bvarBs),
          st.fvarBs.push (n.fvarRangeOf st.fvarBs), st.lparamBs,
          st.eparamBs.push (n.hasLParamOf st.eparamBs st.lparamBs),
          st.nnodes, st.ncons⟩
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
          st.nnodes, st.ncons⟩) := by
  obtain ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
    nnodes, ncons⟩ := st
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

/-- `internL` preserves the invariant when the node's children are
already-stored level indices. -/
theorem internL_wf {st : EStore} {n : LNode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.lnodes.size) : (st.internL n).2.WF := by
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
          st.nnodes, st.ncons⟩
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
          st.nnodes.push n, st.ncons.insert n st.nnodes.size⟩) := by
  obtain ⟨nodes, cons, lnodes, lcons, bvarBs, fvarBs, lparamBs, eparamBs,
    nnodes, ncons⟩ := st
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

/-- `internN` preserves the invariant when the node's prefix is an
already-stored name index. -/
theorem internN_wf {st : EStore} {n : NNode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nnodes.size) : (st.internN n).2.WF := by
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
          st.nnodes.push n, st.ncons.insert n st.nnodes.size⟩
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

/-- The executable readback agrees with the structural name
denotation (unconditionally: the two recursions coincide). -/
theorem readbackN_eq_denoteN (st : EStore) : ∀ i, st.readbackN i = st.denoteN i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    rw [readbackN.eq_def, denoteN.eq_def]
    cases hn : st.nnodes[i]? with
    | none => rfl
    | some n =>
      cases n with
      | anonymous => rfl
      | str p s =>
        simp only [denoteNNode]
        by_cases hp : p < i
        · simp only [dif_pos hp, ih p hp]
          cases st.denoteN p <;> rfl
        · simp [dif_neg hp]
      | num p k =>
        simp only [denoteNNode]
        by_cases hp : p < i
        · simp only [dif_pos hp, ih p hp]
          cases st.denoteN p <;> rfl
        · simp [dif_neg hp]

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

/-- On a well-formed store, every in-range level index denotes. -/
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

/-! ## The memo invariant for the index→index traversals -/

/-- Invariant of a per-call memo table for an index→index traversal with
a `Nat` cursor implementing the expression function `g`: every entry's
key is in range and maps denotation-consistently.  (Entries for in-range
keys that do not denote are permanently vacuous: an in-range index's
denotation never changes under extension.) -/
def MemoNInv (st : EStore) (g : Expr → Nat → Expr)
    (memo : Std.HashMap (EIdx × Nat) EIdx) : Prop :=
  ∀ (e : EIdx) (c : Nat) (r : EIdx), memo[(e, c)]? = some r →
    e < st.nodes.size ∧ ∀ x, st.denote e = some x → st.denote r = some (g x c)

theorem MemoNInv.empty {st : EStore} {g : Expr → Nat → Expr} :
    MemoNInv st g {} := by
  intro e c r hr
  simp at hr

theorem MemoNInv.mono {st st' : EStore} {g : Expr → Nat → Expr}
    {memo : Std.HashMap (EIdx × Nat) EIdx} (hext : Ext st st') (hwf : st.WF)
    (h : MemoNInv st g memo) : MemoNInv st' g memo := by
  intro e c r hr
  obtain ⟨hlt, hcond⟩ := h e c r hr
  refine ⟨Nat.lt_of_lt_of_le hlt hext.size_le, ?_⟩
  intro x hx
  rw [hext.denote_eq_of_lt hwf hlt] at hx
  exact denote_mono hext (hcond x hx)

theorem MemoNInv.insert {st : EStore} {g : Expr → Nat → Expr}
    {memo : Std.HashMap (EIdx × Nat) EIdx} {e : EIdx} {c : Nat} {r : EIdx}
    (h : MemoNInv st g memo) (hlt : e < st.nodes.size)
    (hcond : ∀ x, st.denote e = some x → st.denote r = some (g x c)) :
    MemoNInv st g (memo.insert (e, c) r) := by
  intro e' c' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : (e, c) = (e', c')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact ⟨hlt, hcond⟩
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' c' r' hr'

/-- Transport a "old-store input, new-store output" condition to the new
store (the input's denotation is unchanged below the old size). -/
theorem cond_transport {st st' : EStore} (hext : Ext st st') (hwf : st.WF)
    {e r : EIdx}
    (hesz : e < st.nodes.size) {g : Expr → Expr}
    (hcond : ∀ x, st.denote e = some x → st'.denote r = some (g x)) :
    ∀ x, st'.denote e = some x → st'.denote r = some (g x) := by
  intro x hx
  rw [hext.denote_eq_of_lt hwf hesz] at hx
  exact hcond x hx


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

/-- `fvarRange` is exact for `fvarsBelow`. -/
theorem fvarsBelow_iff {x : Expr} {d : Nat} :
    x.fvarsBelow d ↔ x.fvarRange ≤ d := by
  induction x <;>
    (try simp [Expr.fvarsBelow, Expr.fvarRange, Nat.max_le, *]) <;>
    omega

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
      show st.bvarBs.getD i 0 = n.bvarBoundOf st.bvarBs
      rw [Array.getD_eq_getD_getElem?, hwf.bvarBs_spec i n hn]
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
      show max (st.bvarBoundD f) (st.bvarBoundD a) = _
      rw [ih f hf hxf, ih a ha hxa]
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
      show max (st.bvarBoundD ty) (st.bvarBoundD body - 1) = _
      rw [ih ty ht hxt, ih body hb hxb]
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
      show max (st.bvarBoundD ty) (st.bvarBoundD body - 1) = _
      rw [ih ty ht hxt, ih body hb hxb]
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
      show max (max (st.bvarBoundD ty) (st.bvarBoundD val))
        (st.bvarBoundD body - 1) = _
      rw [ih ty ht hxt, ih val hv hxv, ih body hb hxb]
      rfl
    | proj sp j sub =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xs, hxs, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have hs := hcl sub (by simp [ENode.children])
      show st.bvarBoundD sub = _
      rw [ih sub hs hxs]
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
      show st.fvarBs.getD i 0 = n.fvarRangeOf st.fvarBs
      rw [Array.getD_eq_getD_getElem?, hwf.fvarBs_spec i n hn]
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
      show max (st.fvarRangeD f) (st.fvarRangeD a) = _
      rw [ih f hf hxf, ih a ha hxa]
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
      show max (st.fvarRangeD ty) (st.fvarRangeD body) = _
      rw [ih ty ht hxt, ih body hb hxb]
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
      show max (st.fvarRangeD ty) (st.fvarRangeD body) = _
      rw [ih ty ht hxt, ih body hb hxb]
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
      show max (max (st.fvarRangeD ty) (st.fvarRangeD val))
        (st.fvarRangeD body) = _
      rw [ih ty ht hxt, ih val hv hxv, ih body hb hxb]
      rfl
    | proj sp j sub =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xs, hxs, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have hs := hcl sub (by simp [ENode.children])
      show st.fvarRangeD sub = _
      rw [ih sub hs hxs]
      rfl

/-- Cutoff consequence: a bound entry at or below the cursor certifies
`looseBVarsBounded` of the denotation (the instantiation traversals'
identity branch). -/
theorem WF.bvarBoundD_le {st : EStore} (hwf : st.WF) {e : EIdx}
    {x : Expr} {d : Nat} (hx : st.denote e = some x)
    (hle : st.bvarBoundD e ≤ d) : x.looseBVarsBounded d = true :=
  looseBVarsBounded_iff.mpr (hwf.bvarBoundD_exact e hx ▸ hle)

/-- Cutoff consequence: a range entry at or below the base certifies
`fvarsBelow` of the denotation (the abstraction traversals' identity
branch). -/
theorem WF.fvarRangeD_le {st : EStore} (hwf : st.WF) {e : EIdx}
    {x : Expr} {d : Nat} (hx : st.denote e = some x)
    (hle : st.fvarRangeD e ≤ d) : x.fvarsBelow d :=
  fvarsBelow_iff.mpr (hwf.fvarRangeD_exact e hx ▸ hle)

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
      show st.eparamBs.getD i false = n.hasLParamOf st.eparamBs st.lparamBs
      rw [Array.getD_eq_getD_getElem?, hwf.eparamBs_spec i n hn]
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
      show st.ehasParamD t = _
      rw [ih t hlt hxt]
      rfl
    | app f a =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xf, hxf, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨xa, hxa, rfl⟩ := hdn
      have hf := hcl f (by simp [ENode.children])
      have ha := hcl a (by simp [ENode.children])
      show (st.ehasParamD f || st.ehasParamD a) = _
      rw [ih f hf hxf, ih a ha hxa]
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
        show (st.ehasParamD ty || st.ehasParamD body || false) = _
        rw [ih ty ht hxt, ih body hb hxb]
        rfl
      | some u =>
        rw [denoteBM, Option.map_eq_some_iff] at hbm
        obtain ⟨lv, hlv, rfl⟩ := hbm
        show (st.ehasParamD ty || st.ehasParamD body || st.lhasParamD u) = _
        rw [ih ty ht hxt, ih body hb hxb, hwf.lhasParamD_exact u hlv]
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
        show (st.ehasParamD ty || st.ehasParamD body || false) = _
        rw [ih ty ht hxt, ih body hb hxb]
        rfl
      | some u =>
        rw [denoteBM, Option.map_eq_some_iff] at hbm
        obtain ⟨lv, hlv, rfl⟩ := hbm
        show (st.ehasParamD ty || st.ehasParamD body || st.lhasParamD u) = _
        rw [ih ty ht hxt, ih body hb hxb, hwf.lhasParamD_exact u hlv]
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
      show (st.ehasParamD ty || st.ehasParamD val || st.ehasParamD body) = _
      rw [ih ty ht hxt, ih val hv hxv, ih body hb hxb]
      rfl
    | proj sp j sub =>
      rw [denoteNode, Option.bind_eq_some_iff] at hdn
      obtain ⟨xs, hxs, hdn⟩ := hdn
      rw [Option.map_eq_some_iff] at hdn
      obtain ⟨nmv, -, rfl⟩ := hdn
      have hs := hcl sub (by simp [ENode.children])
      show st.ehasParamD sub = _
      rw [ih sub hs hxs]
      rfl

/-- Prune consequence: a `false` has-level-param entry certifies the
denotation level-param-free. -/
theorem WF.ehasParamD_false {st : EStore} (hwf : st.WF) {e : EIdx}
    {x : Expr} (hx : st.denote e = some x)
    (hp : (!st.ehasParamD e) = true) : x.hasLevelParam = false := by
  rw [Bool.not_eq_eq_eq_not, Bool.not_true] at hp
  rw [← hwf.ehasParamD_exact e hx]
  exact hp

/-! ## `instantiate1I` commutes with `denote` -/

/-- Correctness of the memoized traversal core: on a well-formed store,
`instantiate1IGo` preserves the invariant, extends the store, keeps the
memo consistent, and its result denotes `Expr.instantiate1` of the
input's denotation. -/
theorem instantiate1IGo_spec {v : EIdx} {w : Expr} :
    ∀ (e : EIdx) {st : EStore} {memo : MemoN} {d : Nat} {r : EIdx}
      {st' : EStore} {memo' : MemoN},
      st.WF → st.denote v = some w →
      MemoNInv st (fun x c => x.instantiate1 w c) memo →
      instantiate1IGo v st memo e d = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧
        MemoNInv st' (fun x c => x.instantiate1 w c) memo' ∧
        ∀ x, st.denote e = some x → st'.denote r = some (x.instantiate1 w d) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro st memo d r st' memo' hwf hv hinv hgo
    unfold instantiate1IGo at hgo
    split at hgo
    · -- per-node bound cutoff: no loose bvar at or above the cursor
      rename_i hcut
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, ?_⟩
      intro x hx
      rw [Expr.instantiate1_eq_self (hwf.bvarBoundD_le hx hcut)]
      exact hx
    split at hgo
    · -- memo hit
      rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ _ hhit).2⟩
    · split at hgo
      · -- index out of range: identity, no memo insert
        rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          split at hgo
          · -- i = d: the replacement
            rename_i hid
            cases hgo
            subst hid
            have hcond : ∀ x, st.denote e = some x →
                st.denote v = some (x.instantiate1 w i) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.instantiate1] using hv
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
          · split at hgo
            · -- i > d: lowered bvar, interned
              rename_i hne hgt
              rcases hI : st.intern (.bvar (i - 1)) with ⟨ri, sti⟩
              rw [hI] at hgo
              cases hgo
              have hwfI : (st.intern (.bvar (i - 1))).2.WF :=
                intern_wf hwf (by simp [ENode.children]) (by simp [ENode.levels]) (by simp [ENode.names])
              have hextI : Ext st (st.intern (.bvar (i - 1))).2 := intern_ext _ _
              have hdI : (st.intern (.bvar (i - 1))).2.denote
                    (st.intern (.bvar (i - 1))).1
                  = denoteNode st.denote st.denoteL st.denoteN (.bvar (i - 1)) :=
                intern_denote hwf (by simp [ENode.children])
              rw [hI] at hwfI hextI hdI
              have hcond : ∀ x, st.denote e = some x →
                  sti.denote ri = some (x.instantiate1 w d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hdI]
                simp [Expr.instantiate1, denoteNode, hne, hgt]
              refine ⟨hwfI, hextI, ?_, hcond⟩
              exact (hinv.mono hextI hwf).insert
                (Nat.lt_of_lt_of_le hesz hextI.size_le)
                (cond_transport hextI hwf hesz hcond)
            · -- i < d: unchanged
              rename_i hne hngt
              cases hgo
              have hcond : ∀ x, st.denote e = some x →
                  st.denote e = some (x.instantiate1 w d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.instantiate1, hx, hne, hngt]
              exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          cases hgo
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.fvar idx nmv xt) := by
            rw [hde, denoteNode, hxt, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun u hu => hwf.levels_lt e _ hn u (by simp [ENode.levels, hu]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo f d with ⟨f', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiate1IGo v st₁ memo₁ a d with ⟨a', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih f hguard.1 hwf hv hinv h₁
            have hv₁ := denote_mono hext₁ hv
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih a hguard.2 hwf₁ hv₁ hinv₁ h₂
            have hf₂ : st₂.denote f' = some (xf.instantiate1 w d) :=
              denote_mono hext₂ (hden₁ xf hf)
            have ha₂ : st₂.denote a' = some (xa.instantiate1 w d) :=
              hden₂ xa (denote_mono hext₁ ha)
            have hcI : ∀ c ∈ (ENode.app f' a').children, c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size hf₂
              · exact denote_lt_size ha₂
            have hwf₃ : (st₂.intern (.app f' a')).2.WF :=
              intern_wf hwf₂ hcI (by simp [ENode.levels]) (by simp [ENode.names])
            have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 := intern_ext _ _
            have hdI := intern_denote (n := .app f' a') hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hf₂, ha₂]
              simp [Expr.instantiate1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo ty d with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiate1IGo v st₁ memo₁ body (d + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.lam nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hv hinv h₁
            have hv₁ := denote_mono hext₁ hv
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hv₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.instantiate1 w d) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.instantiate1 w (d + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.lam nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.lam nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.lam nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.lam nm ty' body' m)).2 := intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.instantiate1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo ty d with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiate1IGo v st₁ memo₁ body (d + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.forallE nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hv hinv h₁
            have hv₁ := denote_mono hext₁ hv
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hv₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.instantiate1 w d) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.instantiate1 w (d + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.forallE nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.forallE nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.forallE nm ty' body' m)).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.instantiate1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo ty d with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiate1IGo v st₁ memo₁ val d with ⟨val', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : instantiate1IGo v st₂ memo₂ body (d + 1) with ⟨body', st₃, memo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hv hinv h₁
            have hv₁ := denote_mono hext₁ hv
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
              ih val hguard.2.1 hwf₁ hv₁ hinv₁ h₂
            have hv₂ := denote_mono hext₂ hv₁
            obtain ⟨hwf₃, hext₃, hinv₃, hden₃⟩ :=
              ih body hguard.2.2 hwf₂ hv₂ hinv₂ h₃
            have ht₃ : st₃.denote ty' = some (xt.instantiate1 w d) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hvv₃ : st₃.denote val' = some (xv.instantiate1 w d) :=
              denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hvv))
            have hb₃ : st₃.denote body' = some (xb.instantiate1 w (d + 1)) :=
              hden₃ xb (denote_mono hext₂ (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hvv₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
              intern_wf hwf₃ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .letE nm ty' val' body') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃,
                denoteN_mono (hext₁.trans (hext₂.trans hext₃)) hnm]
              simp [Expr.instantiate1]
            refine ⟨hwf₄, hextAll, ?_, hcond⟩
            exact (hinv₃.mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : instantiate1IGo v st memo sub d with ⟨sub', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.proj s j sub') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih sub hguard hwf hv hinv h₁
            have hs₁ : st₁.denote sub' = some (xs.instantiate1 w d) := hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF := intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁, denoteN_mono hext₁ hnm]
              simp [Expr.instantiate1]
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)

/-- `instantiate1I` commutes with `denote`: the result denotes
`Expr.instantiate1` of the inputs' denotations, on an extended
well-formed store. -/
theorem instantiate1I_spec {st : EStore} {e v : EIdx} {d : Nat} {a w : Expr}
    (hwf : st.WF) (he : st.denote e = some a) (hv : st.denote v = some w) :
    (st.instantiate1I e v d).2.WF ∧ Ext st (st.instantiate1I e v d).2 ∧
      (st.instantiate1I e v d).2.denote (st.instantiate1I e v d).1
        = some (a.instantiate1 w d) := by
  rcases hgo : instantiate1IGo v st {} e d with ⟨r, st', memo'⟩
  obtain ⟨hwf', hext', -, hcond⟩ :=
    instantiate1IGo_spec e hwf hv MemoNInv.empty hgo
  simp only [instantiate1I, hgo]
  exact ⟨hwf', hext', hcond a he⟩

/-! ## `abstract1I` commutes with `denote` -/

theorem abstract1IGo_spec {dd : Nat} :
    ∀ (e : EIdx) {st : EStore} {memo : MemoN} {k : Nat} {r : EIdx}
      {st' : EStore} {memo' : MemoN},
      st.WF →
      MemoNInv st (fun x c => x.abstract1 dd c) memo →
      abstract1IGo dd st memo e k = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧
        MemoNInv st' (fun x c => x.abstract1 dd c) memo' ∧
        ∀ x, st.denote e = some x → st'.denote r = some (x.abstract1 dd k) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro st memo k r st' memo' hwf hinv hgo
    unfold abstract1IGo at hgo
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstract1 dd k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstract1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.fvar idx nmv xt) := by
            rw [hde, denoteNode, hxt, hnm]; rfl
          split at hgo
          · -- idx = dd: abstracted to bvar k
            rename_i hid
            rcases hI : st.intern (.bvar k) with ⟨ri, sti⟩
            rw [hI] at hgo
            cases hgo
            have hwfI : (st.intern (.bvar k)).2.WF :=
              intern_wf hwf (by simp [ENode.children]) (by simp [ENode.levels]) (by simp [ENode.names])
            have hextI : Ext st (st.intern (.bvar k)).2 := intern_ext _ _
            have hdI := intern_denote (n := .bvar k) hwf (by simp [ENode.children])
            rw [hI] at hwfI hextI hdI
            have hcond : ∀ x, st.denote e = some x →
                sti.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI]
              simp [Expr.abstract1, denoteNode, hid]
            refine ⟨hwfI, hextI, ?_, hcond⟩
            exact (hinv.mono hextI hwf).insert
              (Nat.lt_of_lt_of_le hesz hextI.size_le)
              (cond_transport hextI hwf hesz hcond)
          · -- idx ≠ dd: unchanged
            rename_i hid
            cases hgo
            have hcond : ∀ x, st.denote e = some x →
                st.denote e = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.abstract1, hid] using hx
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstract1 dd k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstract1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun u hu => hwf.levels_lt e _ hn u (by simp [ENode.levels, hu]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstract1 dd k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstract1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstract1 dd k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstract1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo f k with ⟨f', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstract1IGo dd st₁ memo₁ a k with ⟨a', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih f hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih a hguard.2 hwf₁ hinv₁ h₂
            have hf₂ : st₂.denote f' = some (xf.abstract1 dd k) :=
              denote_mono hext₂ (hden₁ xf hf)
            have ha₂ : st₂.denote a' = some (xa.abstract1 dd k) :=
              hden₂ xa (denote_mono hext₁ ha)
            have hcI : ∀ c ∈ (ENode.app f' a').children, c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size hf₂
              · exact denote_lt_size ha₂
            have hwf₃ : (st₂.intern (.app f' a')).2.WF :=
              intern_wf hwf₂ hcI (by simp [ENode.levels]) (by simp [ENode.names])
            have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 := intern_ext _ _
            have hdI := intern_denote (n := .app f' a') hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hf₂, ha₂]
              simp [Expr.abstract1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstract1IGo dd st₁ memo₁ body (k + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.lam nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.abstract1 dd k) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.abstract1 dd (k + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.lam nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.lam nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.lam nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.lam nm ty' body' m)).2 := intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.abstract1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstract1IGo dd st₁ memo₁ body (k + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.forallE nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.abstract1 dd k) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.abstract1 dd (k + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.forallE nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.forallE nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.forallE nm ty' body' m)).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.abstract1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstract1IGo dd st₁ memo₁ val k with ⟨val', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : abstract1IGo dd st₂ memo₂ body (k + 1) with ⟨body', st₃, memo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
              ih val hguard.2.1 hwf₁ hinv₁ h₂
            obtain ⟨hwf₃, hext₃, hinv₃, hden₃⟩ :=
              ih body hguard.2.2 hwf₂ hinv₂ h₃
            have ht₃ : st₃.denote ty' = some (xt.abstract1 dd k) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hvv₃ : st₃.denote val' = some (xv.abstract1 dd k) :=
              denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hvv))
            have hb₃ : st₃.denote body' = some (xb.abstract1 dd (k + 1)) :=
              hden₃ xb (denote_mono hext₂ (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hvv₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
              intern_wf hwf₃ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .letE nm ty' val' body') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃,
                denoteN_mono (hext₁.trans (hext₂.trans hext₃)) hnm]
              simp [Expr.abstract1]
            refine ⟨hwf₄, hextAll, ?_, hcond⟩
            exact (hinv₃.mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : abstract1IGo dd st memo sub k with ⟨sub', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.proj s j sub') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih sub hguard hwf hinv h₁
            have hs₁ : st₁.denote sub' = some (xs.abstract1 dd k) := hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF := intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.abstract1 dd k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁, denoteN_mono hext₁ hnm]
              simp [Expr.abstract1]
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)

/-! ## `abstractRangeI` commutes with `denote` (task #72) -/

theorem abstractRangeIGo_spec {dd kk : Nat} :
    ∀ (e : EIdx) {st : EStore} {memo : MemoN} {k : Nat} {r : EIdx}
      {st' : EStore} {memo' : MemoN},
      st.WF →
      MemoNInv st (fun x c => x.abstractRange dd kk c) memo →
      abstractRangeIGo dd kk st memo e k = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧
        MemoNInv st' (fun x c => x.abstractRange dd kk c) memo' ∧
        ∀ x, st.denote e = some x → st'.denote r = some (x.abstractRange dd kk k) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro st memo k r st' memo' hwf hinv hgo
    unfold abstractRangeIGo at hgo
    split at hgo
    · -- per-node fvar-range cutoff: no fvar at or above the range base
      rename_i hcut
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, ?_⟩
      intro x hx
      rw [abstractRange_eq_self (hwf.fvarRangeD_le hx hcut)]
      exact hx
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstractRange dd kk k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstractRange] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.fvar idx nmv xt) := by
            rw [hde, denoteNode, hxt, hnm]; rfl
          split at hgo
          · -- dd ≤ idx < dd + kk: abstracted to the range's bvar
            rename_i hid
            rcases hI : st.intern (.bvar (k + (dd + kk - 1 - idx)))
              with ⟨ri, sti⟩
            rw [hI] at hgo
            cases hgo
            have hwfI : (st.intern (.bvar (k + (dd + kk - 1 - idx)))).2.WF :=
              intern_wf hwf (by simp [ENode.children]) (by simp [ENode.levels]) (by simp [ENode.names])
            have hextI : Ext st (st.intern (.bvar (k + (dd + kk - 1 - idx)))).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .bvar (k + (dd + kk - 1 - idx)))
              hwf (by simp [ENode.children])
            rw [hI] at hwfI hextI hdI
            have hcond : ∀ x, st.denote e = some x →
                sti.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI]
              simp [Expr.abstractRange, denoteNode, hid]
            refine ⟨hwfI, hextI, ?_, hcond⟩
            exact (hinv.mono hextI hwf).insert
              (Nat.lt_of_lt_of_le hesz hextI.size_le)
              (cond_transport hextI hwf hesz hcond)
          · -- outside the range: unchanged
            rename_i hid
            cases hgo
            have hcond : ∀ x, st.denote e = some x →
                st.denote e = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.abstractRange, hid] using hx
            exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstractRange dd kk k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstractRange] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          cases hgo
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun u hu => hwf.levels_lt e _ hn u (by simp [ENode.levels, hu]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstractRange dd kk k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstractRange] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.abstractRange dd kk k) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.abstractRange] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo f k with ⟨f', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstractRangeIGo dd kk st₁ memo₁ a k with ⟨a', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih f hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih a hguard.2 hwf₁ hinv₁ h₂
            have hf₂ : st₂.denote f' = some (xf.abstractRange dd kk k) :=
              denote_mono hext₂ (hden₁ xf hf)
            have ha₂ : st₂.denote a' = some (xa.abstractRange dd kk k) :=
              hden₂ xa (denote_mono hext₁ ha)
            have hcI : ∀ c ∈ (ENode.app f' a').children, c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size hf₂
              · exact denote_lt_size ha₂
            have hwf₃ : (st₂.intern (.app f' a')).2.WF :=
              intern_wf hwf₂ hcI (by simp [ENode.levels]) (by simp [ENode.names])
            have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 := intern_ext _ _
            have hdI := intern_denote (n := .app f' a') hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hf₂, ha₂]
              simp [Expr.abstractRange]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstractRangeIGo dd kk st₁ memo₁ body (k + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.lam nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.abstractRange dd kk k) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.abstractRange dd kk (k + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.lam nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.lam nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.lam nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.lam nm ty' body' m)).2 := intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.abstractRange]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstractRangeIGo dd kk st₁ memo₁ body (k + 1) with ⟨body', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.forallE nm ty' body' m) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih body hguard.2 hwf₁ hinv₁ h₂
            have ht₂ : st₂.denote ty' = some (xt.abstractRange dd kk k) :=
              denote_mono hext₂ (hden₁ xt ht)
            have hb₂ : st₂.denote body' = some (xb.abstractRange dd kk (k + 1)) :=
              hden₂ xb (denote_mono hext₁ hb)
            have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m).children,
                c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₂
              · exact denote_lt_size hb₂
            have hlvI : ∀ u ∈ (ENode.forallE nm ty' body' m).levels,
                u < st₂.lnodes.size := fun u hu =>
              Nat.lt_of_lt_of_le
                (hwf.levels_lt e _ hn u (by simpa [ENode.levels] using hu))
                (hext₁.trans hext₂).lsize_le
            have hwf₃ : (st₂.intern (.forallE nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI hlvI (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans hext₂).nsize_le)
            have hext₃ : Ext st₂ (st₂.intern (.forallE nm ty' body' m)).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂, hbm₂, hnm₂]
              simp [Expr.abstractRange]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo ty k with ⟨ty', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : abstractRangeIGo dd kk st₁ memo₁ val k with ⟨val', st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : abstractRangeIGo dd kk st₂ memo₂ body (k + 1) with ⟨body', st₃, memo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih ty hguard.1 hwf hinv h₁
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ :=
              ih val hguard.2.1 hwf₁ hinv₁ h₂
            obtain ⟨hwf₃, hext₃, hinv₃, hden₃⟩ :=
              ih body hguard.2.2 hwf₂ hinv₂ h₃
            have ht₃ : st₃.denote ty' = some (xt.abstractRange dd kk k) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hvv₃ : st₃.denote val' = some (xv.abstractRange dd kk k) :=
              denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hvv))
            have hb₃ : st₃.denote body' = some (xb.abstractRange dd kk (k + 1)) :=
              hden₃ xb (denote_mono hext₂ (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hvv₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
              intern_wf hwf₃ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .letE nm ty' val' body') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃,
                denoteN_mono (hext₁.trans (hext₂.trans hext₃)) hnm]
              simp [Expr.abstractRange]
            refine ⟨hwf₄, hextAll, ?_, hcond⟩
            exact (hinv₃.mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : abstractRangeIGo dd kk st memo sub k with ⟨sub', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.proj s j sub') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih sub hguard hwf hinv h₁
            have hs₁ : st₁.denote sub' = some (xs.abstractRange dd kk k) := hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF := intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.abstractRange dd kk k) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁, denoteN_mono hext₁ hnm]
              simp [Expr.abstractRange]
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)

/-- `abstractRangeI` commutes with `denote`.  The `k = 0` shortcut is
covered by `abstractRange_zero`. -/
theorem abstractRangeI_spec {st : EStore} {e : EIdx} {d k c : Nat} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    (st.abstractRangeI e d k c).2.WF ∧
      Ext st (st.abstractRangeI e d k c).2 ∧
      (st.abstractRangeI e d k c).2.denote (st.abstractRangeI e d k c).1
        = some (a.abstractRange d k c) := by
  match k with
  | 0 =>
    refine ⟨hwf, Ext.refl st, ?_⟩
    rw [abstractRange_zero]
    exact he
  | k + 1 =>
    rcases hgo : abstractRangeIGo d (k + 1) st {} e c with ⟨r, st', memo'⟩
    obtain ⟨hwf', hext', -, hcond⟩ :=
      abstractRangeIGo_spec e hwf MemoNInv.empty hgo
    simp only [abstractRangeI, hgo]
    exact ⟨hwf', hext', hcond a he⟩

/-- `abstract1I` commutes with `denote`. -/
theorem abstract1I_spec {st : EStore} {e : EIdx} {d k : Nat} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    (st.abstract1I e d k).2.WF ∧ Ext st (st.abstract1I e d k).2 ∧
      (st.abstract1I e d k).2.denote (st.abstract1I e d k).1
        = some (a.abstract1 d k) := by
  rcases hgo : abstract1IGo d st {} e k with ⟨r, st', memo'⟩
  obtain ⟨hwf', hext', -, hcond⟩ := abstract1IGo_spec e hwf MemoNInv.empty hgo
  simp only [abstract1I, hgo]
  exact ⟨hwf', hext', hcond a he⟩

/-! ## `instantiateLevelParamsI` commutes with `denote` -/

/-- Cursor-free variant of `MemoNInv` for the level-substitution
traversal. -/
def Memo0Inv (st : EStore) (g : Expr → Expr) (memo : Memo0) : Prop :=
  ∀ (e r : EIdx), memo[e]? = some r →
    e < st.nodes.size ∧ ∀ x, st.denote e = some x → st.denote r = some (g x)

theorem Memo0Inv.empty {st : EStore} {g : Expr → Expr} : Memo0Inv st g {} := by
  intro e r hr
  simp at hr

theorem Memo0Inv.mono {st st' : EStore} {g : Expr → Expr} {memo : Memo0}
    (hext : Ext st st') (hwf : st.WF) (h : Memo0Inv st g memo) : Memo0Inv st' g memo := by
  intro e r hr
  obtain ⟨hlt, hcond⟩ := h e r hr
  refine ⟨Nat.lt_of_lt_of_le hlt hext.size_le, ?_⟩
  intro x hx
  rw [hext.denote_eq_of_lt hwf hlt] at hx
  exact denote_mono hext (hcond x hx)

theorem Memo0Inv.insert {st : EStore} {g : Expr → Expr} {memo : Memo0}
    {e r : EIdx} (h : Memo0Inv st g memo) (hlt : e < st.nodes.size)
    (hcond : ∀ x, st.denote e = some x → st.denote r = some (g x)) :
    Memo0Inv st g (memo.insert e r) := by
  intro e' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : e = e'
  · subst hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact ⟨hlt, hcond⟩
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' r' hr'

/-! ### The level-substitution layer (task #62) -/

/-- Invariant of a level index→index memo implementing the level
function `g`. -/
def LvlMemoInv (st : EStore) (g : Level → Level) (memo : LMemo) : Prop :=
  ∀ (u r : LIdx), memo[u]? = some r →
    u < st.lnodes.size ∧ ∀ x, st.denoteL u = some x → st.denoteL r = some (g x)

theorem LvlMemoInv.empty {st : EStore} {g : Level → Level} :
    LvlMemoInv st g {} := by
  intro u r hr
  simp at hr

theorem LvlMemoInv.mono {st st' : EStore} {g : Level → Level} {memo : LMemo}
    (hext : Ext st st') (h : LvlMemoInv st g memo) : LvlMemoInv st' g memo := by
  intro u r hr
  obtain ⟨hlt, hcond⟩ := h u r hr
  refine ⟨Nat.lt_of_lt_of_le hlt hext.lsize_le, ?_⟩
  intro x hx
  rw [hext.denoteL_eq_of_lt hlt] at hx
  exact denoteL_mono hext (hcond x hx)

theorem LvlMemoInv.insert {st : EStore} {g : Level → Level} {memo : LMemo}
    {u r : LIdx} (h : LvlMemoInv st g memo) (hlt : u < st.lnodes.size)
    (hcond : ∀ x, st.denoteL u = some x → st.denoteL r = some (g x)) :
    LvlMemoInv st g (memo.insert u r) := by
  intro u' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : u = u'
  · subst hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact ⟨hlt, hcond⟩
  · rw [if_neg (by simpa using hk)] at hr'
    exact h u' r' hr'

/-- Level-side `cond_transport`. -/
theorem condL_transport {st st' : EStore} (hext : Ext st st') {u r : LIdx}
    (husz : u < st.lnodes.size) {g : Level → Level}
    (hcond : ∀ x, st.denoteL u = some x → st'.denoteL r = some (g x)) :
    ∀ x, st'.denoteL u = some x → st'.denoteL r = some (g x) := by
  intro x hx
  rw [hext.denoteL_eq_of_lt husz] at hx
  exact hcond x hx

/-- `substLGo?` agrees with `Level.subst.go` under the denotation. -/
theorem substLGo?_spec {st : EStore} :
    ∀ {ks : List Name} {us : List LIdx} {lus : List Level} (n : Name),
      denoteLList st.denoteL us = some lus →
      (∀ v, substLGo? ks us n = some v →
        st.denoteL v = some (Level.subst.go ks lus n)) ∧
      (substLGo? ks us n = none → Level.subst.go ks lus n = .param n) := by
  intro ks
  induction ks with
  | nil =>
    intro us lus n hus
    cases us with
    | nil =>
      cases lus with
      | nil => exact ⟨by simp [substLGo?], fun _ => by simp [Level.subst.go]⟩
      | cons l ls => simp [denoteLList] at hus
    | cons u us' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hus
      obtain ⟨l, hl, ls, hls, rfl⟩ := hus
      exact ⟨by simp [substLGo?], fun _ => by simp [Level.subst.go]⟩
  | cons k ks ih =>
    intro us lus n hus
    cases us with
    | nil =>
      cases lus with
      | nil => exact ⟨by simp [substLGo?], fun _ => by simp [Level.subst.go]⟩
      | cons l ls => simp [denoteLList] at hus
    | cons u us' =>
      simp only [denoteLList, Option.bind_eq_some_iff,
        Option.map_eq_some_iff] at hus
      obtain ⟨l, hl, ls, hls, rfl⟩ := hus
      by_cases hkn : k = n
      · subst hkn
        refine ⟨fun v hv => ?_, fun hnone => ?_⟩
        · simp only [substLGo?] at hv
          cases hv
          simpa [Level.subst.go] using hl
        · simp [substLGo?] at hnone
      · refine ⟨fun v hv => ?_, fun hnone => ?_⟩
        · simp only [substLGo?, if_neg hkn] at hv
          simpa [Level.subst.go, hkn] using (ih n hls).1 v hv
        · simp only [substLGo?, if_neg hkn] at hnone
          simpa [Level.subst.go, hkn] using (ih n hls).2 hnone

/-- `substLIGo` commutes with the denotation (the level analog of
`instantiate1IGo_spec`). -/
theorem substLIGo_spec {ks : List Name} {us : List LIdx} {lus : List Level} :
    ∀ (u : LIdx) {st : EStore} {memo : LMemo} {r : LIdx}
      {st' : EStore} {memo' : LMemo},
      st.WF → denoteLList st.denoteL us = some lus →
      LvlMemoInv st (Level.subst ks lus) memo →
      substLIGo ks us st memo u = (r, st', memo') →
      st'.WF ∧ Ext st st' ∧
        LvlMemoInv st' (Level.subst ks lus) memo' ∧
        ∀ x, st.denoteL u = some x → st'.denoteL r = some (Level.subst ks lus x) := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro st memo r st' memo' hwf hus hinv hgo
    unfold substLIGo at hgo
    split at hgo
    · -- param-free: identity (task #87)
      rename_i hnp
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, ?_⟩
      intro x hx
      rw [Level.subst_eq_self (hwf.lhasParamD_false hx hnp)]
      exact hx
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, (hinv _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denoteL_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have husz : u < st.lnodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.lchildren_lt u n hn
        have hde := denoteL_node hn hcl
        cases n with
        | zero =>
          dsimp only at hgo
          cases hgo
          have hx : st.denoteL u = some .zero := by rw [hde]; rfl
          have hcond : ∀ x, st.denoteL u = some x →
              st.denoteL u = some (Level.subst ks lus x) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Level.subst] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert husz hcond, hcond⟩
        | param p =>
          dsimp only at hgo
          have hx : st.denoteL u = some (.param p) := by rw [hde]; rfl
          split at hgo
          · rename_i v hv
            cases hgo
            have hcond : ∀ x, st.denoteL u = some x →
                st.denoteL v = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.subst] using (substLGo?_spec p hus).1 v hv
            exact ⟨hwf, Ext.refl st, hinv.insert husz hcond, hcond⟩
          · rename_i hvnone
            cases hgo
            have hcond : ∀ x, st.denoteL u = some x →
                st.denoteL u = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hx, Level.subst, (substLGo?_spec p hus).2 hvnone]
            exact ⟨hwf, Ext.refl st, hinv.insert husz hcond, hcond⟩
        | succ l =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl l (by simp [LNode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : substLIGo ks us st memo l with ⟨l', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.internL (.succ l') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard husz)
            have hx : st.denoteL u = some (.succ xl) := by
              rw [hde, denoteLNode, hl]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard hwf hus hinv h₁
            have hl₁ : st₁.denoteL l' = some (Level.subst ks lus xl) :=
              hden₁ xl hl
            have hstep := internL_step (n := .succ l') hwf₁
              (by simpa [LNode.children] using denoteL_lt_size hl₁)
              (a := .succ (Level.subst ks lus xl))
              (by rw [denoteLNode, hl₁]; rfl)
            rw [h₂] at hstep
            obtain ⟨hwf₂, hext₂, hden₂⟩ := hstep
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denoteL u = some x →
                st₂.denoteL ri = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.subst] using hden₂
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact ((hinv₁.mono hext₂).insert
              (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
              (condL_transport hextAll husz hcond))
        | max l r' =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl l (by simp [LNode.children]),
              hcl r' (by simp [LNode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : substLIGo ks us st memo l with ⟨l', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : substLIGo ks us st₁ memo₁ r' with ⟨r₂, st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.internL (.max l' r₂) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard.1 husz)
            obtain ⟨xr, hr⟩ := denoteL_total hwf r' (Nat.lt_trans hguard.2 husz)
            have hx : st.denoteL u = some (.max xl xr) := by
              rw [hde, denoteLNode, hl, hr]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard.1 hwf hus hinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih r' hguard.2 hwf₁ hus₁ hinv₁ h₂
            have hl₂ : st₂.denoteL l' = some (Level.subst ks lus xl) :=
              denoteL_mono hext₂ (hden₁ xl hl)
            have hr₂ : st₂.denoteL r₂ = some (Level.subst ks lus xr) :=
              hden₂ xr (denoteL_mono hext₁ hr)
            have hstep := internL_step (n := .max l' r₂) hwf₂
              (by
                simp only [LNode.children, List.mem_cons, List.not_mem_nil,
                  or_false]
                rintro c (rfl | rfl)
                · exact denoteL_lt_size hl₂
                · exact denoteL_lt_size hr₂)
              (a := .max (Level.subst ks lus xl) (Level.subst ks lus xr))
              (by rw [denoteLNode, hl₂, hr₂]; rfl)
            rw [h₃] at hstep
            obtain ⟨hwf₃, hext₃, hden₃⟩ := hstep
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denoteL u = some x →
                st₃.denoteL ri = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.subst] using hden₃
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact ((hinv₂.mono hext₃).insert
              (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
              (condL_transport hextAll husz hcond))
        | imax l r' =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl l (by simp [LNode.children]),
              hcl r' (by simp [LNode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : substLIGo ks us st memo l with ⟨l', st₁, memo₁⟩
            rw [h₁] at hgo
            rcases h₂ : substLIGo ks us st₁ memo₁ r' with ⟨r₂, st₂, memo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.internL (.imax l' r₂) with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xl, hl⟩ := denoteL_total hwf l (Nat.lt_trans hguard.1 husz)
            obtain ⟨xr, hr⟩ := denoteL_total hwf r' (Nat.lt_trans hguard.2 husz)
            have hx : st.denoteL u = some (.imax xl xr) := by
              rw [hde, denoteLNode, hl, hr]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih l hguard.1 hwf hus hinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih r' hguard.2 hwf₁ hus₁ hinv₁ h₂
            have hl₂ : st₂.denoteL l' = some (Level.subst ks lus xl) :=
              denoteL_mono hext₂ (hden₁ xl hl)
            have hr₂ : st₂.denoteL r₂ = some (Level.subst ks lus xr) :=
              hden₂ xr (denoteL_mono hext₁ hr)
            have hstep := internL_step (n := .imax l' r₂) hwf₂
              (by
                simp only [LNode.children, List.mem_cons, List.not_mem_nil,
                  or_false]
                rintro c (rfl | rfl)
                · exact denoteL_lt_size hl₂
                · exact denoteL_lt_size hr₂)
              (a := .imax (Level.subst ks lus xl) (Level.subst ks lus xr))
              (by rw [denoteLNode, hl₂, hr₂]; rfl)
            rw [h₃] at hstep
            obtain ⟨hwf₃, hext₃, hden₃⟩ := hstep
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denoteL u = some x →
                st₃.denoteL ri = some (Level.subst ks lus x) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Level.subst] using hden₃
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact ((hinv₂.mono hext₃).insert
              (Nat.lt_of_lt_of_le husz hextAll.lsize_le)
              (condL_transport hextAll husz hcond))

/-- `substLIList` commutes with the denotation. -/
theorem substLIList_spec {ks : List Name} {us : List LIdx} {lus : List Level} :
    ∀ (vs : List LIdx) {st : EStore} {memo : LMemo} {rs : List LIdx}
      {st' : EStore} {memo' : LMemo},
      st.WF → denoteLList st.denoteL us = some lus →
      LvlMemoInv st (Level.subst ks lus) memo →
      substLIList ks us st memo vs = (rs, st', memo') →
      st'.WF ∧ Ext st st' ∧
        LvlMemoInv st' (Level.subst ks lus) memo' ∧
        ∀ xs, denoteLList st.denoteL vs = some xs →
          denoteLList st'.denoteL rs = some (xs.map (Level.subst ks lus)) := by
  intro vs
  induction vs with
  | nil =>
    intro st memo rs st' memo' hwf hus hinv hgo
    cases hgo
    refine ⟨hwf, Ext.refl st, hinv, ?_⟩
    intro xs hxs
    cases hxs
    rfl
  | cons v vs ih =>
    intro st memo rs st' memo' hwf hus hinv hgo
    dsimp only [substLIList] at hgo
    rcases h₁ : substLIGo ks us st memo v with ⟨v', st₁, memo₁⟩
    rw [h₁] at hgo
    rcases h₂ : substLIList ks us st₁ memo₁ vs with ⟨vs', st₂, memo₂⟩
    rw [h₂] at hgo
    cases hgo
    obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := substLIGo_spec v hwf hus hinv h₁
    have hus₁ := denoteLList_mono hext₁ hus
    obtain ⟨hwf₂, hext₂, hinv₂, hden₂⟩ := ih hwf₁ hus₁ hinv₁ h₂
    refine ⟨hwf₂, hext₁.trans hext₂, hinv₂, ?_⟩
    intro xs hxs
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hxs
    obtain ⟨l, hl, ls, hls, rfl⟩ := hxs
    have hv' : st₂.denoteL v' = some (Level.subst ks lus l) :=
      denoteL_mono hext₂ (hden₁ l hl)
    have hvs' := hden₂ ls (denoteLList_mono hext₁ hls)
    simp [denoteLList, hv', hvs']

/-- `substLIBM` commutes with the denotation. -/
theorem substLIBM_spec {ks : List Name} {us : List LIdx} {lus : List Level}
    {m : IBinderMeta} {st : EStore} {memo : LMemo} {m' : IBinderMeta}
    {st' : EStore} {memo' : LMemo}
    (hwf : st.WF) (hus : denoteLList st.denoteL us = some lus)
    (hinv : LvlMemoInv st (Level.subst ks lus) memo)
    (hgo : substLIBM ks us st memo m = (m', st', memo')) :
    st'.WF ∧ Ext st st' ∧
      LvlMemoInv st' (Level.subst ks lus) memo' ∧
      ∀ bm, denoteBM st.denoteL m = some bm →
        denoteBM st'.denoteL m'
          = some ⟨bm.bi, bm.cod.map (Level.subst ks lus)⟩ := by
  obtain ⟨bi, (_ | u)⟩ := m
  · cases hgo
    refine ⟨hwf, Ext.refl st, hinv, ?_⟩
    intro bm hbm
    simp only [denoteBM, Option.some.injEq] at hbm
    subst hbm
    rfl
  · dsimp only [substLIBM] at hgo
    rcases h₁ : substLIGo ks us st memo u with ⟨u', st₁, memo₁⟩
    rw [h₁] at hgo
    cases hgo
    obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := substLIGo_spec u hwf hus hinv h₁
    refine ⟨hwf₁, hext₁, hinv₁, ?_⟩
    intro bm hbm
    simp only [denoteBM, Option.map_eq_some_iff] at hbm
    obtain ⟨l, hl, rfl⟩ := hbm
    simp [denoteBM, hden₁ l hl]

theorem instantiateLevelParamsIGo_spec {ks : List Name} {us : List LIdx}
    {lus : List Level} :
    ∀ (e : EIdx) {st : EStore} {memo : Memo0} {lmemo : LMemo} {r : EIdx}
      {st' : EStore} {memo' : Memo0} {lmemo' : LMemo},
      st.WF →
      denoteLList st.denoteL us = some lus →
      Memo0Inv st (Expr.instantiateLevelParams ks lus) memo →
      LvlMemoInv st (Level.subst ks lus) lmemo →
      instantiateLevelParamsIGo ks us st memo lmemo e = (r, st', memo', lmemo') →
      st'.WF ∧ Ext st st' ∧
        Memo0Inv st' (Expr.instantiateLevelParams ks lus) memo' ∧
        LvlMemoInv st' (Level.subst ks lus) lmemo' ∧
        ∀ x, st.denote e = some x →
          st'.denote r = some (x.instantiateLevelParams ks lus) := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro st memo lmemo r st' memo' lmemo' hwf hus hinv hlinv hgo
    unfold instantiateLevelParamsIGo at hgo
    split at hgo
    · -- level-param-free: identity (task #87)
      rename_i hnp
      cases hgo
      refine ⟨hwf, Ext.refl st, hinv, hlinv, ?_⟩
      intro x hx
      rw [Expr.instantiateLevelParams_eq_self (hwf.ehasParamD_false hx hnp)]
      exact hx
    split at hgo
    · rename_i hhit
      cases hgo
      exact ⟨hwf, Ext.refl st, hinv, hlinv, (hinv _ _ hhit).2⟩
    · split at hgo
      · rename_i hnone
        cases hgo
        refine ⟨hwf, Ext.refl st, hinv, hlinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiateLevelParams ks lus) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiateLevelParams] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hlinv, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl t (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo t
              with ⟨t', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.fvar idx nm t') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xt, hxt⟩ := denote_total hwf t (Nat.lt_trans hguard hesz)
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hwf.names_lt e _ hn nm (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nmv xt) := by
              rw [hde, denoteNode, hxt, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih t hguard hwf hus hinv hlinv h₁
            have ht₁ : st₁.denote t' = some (xt.instantiateLevelParams ks lus) :=
              hden₁ xt hxt
            have hcI : ∀ c ∈ (ENode.fvar idx nm t').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size ht₁
            have hwf₂ : (st₁.intern (.fvar idx nm t')).2.WF :=
              intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.fvar idx nm t')).2 := intern_ext _ _
            have hdI := intern_denote (n := .fvar idx nm t') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₁, denoteN_mono hext₁ hnm]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₂, hextAll, ?_, hlinv₁.mono hext₂, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | sort u =>
          dsimp only at hgo
          rcases h₁ : substLIGo ks us st lmemo u with ⟨u', st₁, lmemo₁⟩
          rw [h₁] at hgo
          rcases h₂ : st₁.intern (.sort u') with ⟨ri, st₂⟩
          rw [h₂] at hgo
          cases hgo
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          obtain ⟨hwf₁, hext₁, hlinv₁, hlden₁⟩ := substLIGo_spec u hwf hus hlinv h₁
          have hu₁ : st₁.denoteL u' = some (Level.subst ks lus lu) :=
            hlden₁ lu hlu
          have hwf₂ : (st₁.intern (.sort u')).2.WF :=
            intern_wf hwf₁ (by simp [ENode.children])
              (by simpa [ENode.levels] using denoteL_lt_size hu₁)
              (by simp [ENode.names])
          have hext₂ : Ext st₁ (st₁.intern (.sort u')).2 := intern_ext _ _
          have hdI := intern_denote (n := .sort u') hwf₁
            (by simp [ENode.children])
          rw [h₂] at hwf₂ hext₂ hdI
          have hextAll : Ext st st₂ := hext₁.trans hext₂
          have hcond : ∀ x, st.denote e = some x →
              st₂.denote ri = some (x.instantiateLevelParams ks lus) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            rw [hdI, denoteNode, hu₁]
            simp [Expr.instantiateLevelParams]
          refine ⟨hwf₂, hextAll, ?_, hlinv₁.mono hext₂, hcond⟩
          exact (hinv.mono hextAll hwf).insert
            (Nat.lt_of_lt_of_le hesz hextAll.size_le)
            (cond_transport hextAll hwf hesz hcond)
        | const nm vs =>
          dsimp only at hgo
          rcases h₁ : substLIList ks us st lmemo vs with ⟨vs', st₁, lmemo₁⟩
          rw [h₁] at hgo
          rcases h₂ : st₁.intern (.const nm vs') with ⟨ri, st₂⟩
          rw [h₂] at hgo
          cases hgo
          obtain ⟨lvs, hlvs⟩ := denoteLList_total hwf vs
            (fun u hu => hwf.levels_lt e _ hn u (by simp [ENode.levels, hu]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lvs) := by
            rw [hde, denoteNode, hlvs, hnm]; rfl
          obtain ⟨hwf₁, hext₁, hlinv₁, hlden₁⟩ :=
            substLIList_spec vs hwf hus hlinv h₁
          have hvs₁ : denoteLList st₁.denoteL vs'
              = some (lvs.map (Level.subst ks lus)) := hlden₁ lvs hlvs
          have hwf₂ : (st₁.intern (.const nm vs')).2.WF :=
            intern_wf hwf₁ (by simp [ENode.children])
              (by simpa [ENode.levels] using denoteLList_lt_size hvs₁)
              (fun p hp => Nat.lt_of_lt_of_le
                (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                hext₁.nsize_le)
          have hext₂ : Ext st₁ (st₁.intern (.const nm vs')).2 := intern_ext _ _
          have hdI := intern_denote (n := .const nm vs') hwf₁
            (by simp [ENode.children])
          rw [h₂] at hwf₂ hext₂ hdI
          have hextAll : Ext st st₂ := hext₁.trans hext₂
          have hcond : ∀ x, st.denote e = some x →
              st₂.denote ri = some (x.instantiateLevelParams ks lus) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            rw [hdI, denoteNode, hvs₁, denoteN_mono hext₁ hnm]
            simp [Expr.instantiateLevelParams]
          refine ⟨hwf₂, hextAll, ?_, hlinv₁.mono hext₂, hcond⟩
          exact (hinv.mono hextAll hwf).insert
            (Nat.lt_of_lt_of_le hesz hextAll.size_le)
            (cond_transport hextAll hwf hesz hcond)
        | lit l =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiateLevelParams ks lus) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiateLevelParams] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hlinv, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo f
              with ⟨f', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiateLevelParamsIGo ks us st₁ memo₁ lmemo₁ a
              with ⟨a', st₂, memo₂, lmemo₂⟩
            rw [h₂] at hgo
            rcases h₃ : st₂.intern (.app f' a') with ⟨ri, st₃⟩
            rw [h₃] at hgo
            cases hgo
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih f hguard.1 hwf hus hinv hlinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hlinv₂, hden₂⟩ :=
              ih a hguard.2 hwf₁ hus₁ hinv₁ hlinv₁ h₂
            have hf₂ : st₂.denote f' = some (xf.instantiateLevelParams ks lus) :=
              denote_mono hext₂ (hden₁ xf hf)
            have ha₂ : st₂.denote a' = some (xa.instantiateLevelParams ks lus) :=
              hden₂ xa (denote_mono hext₁ ha)
            have hcI : ∀ c ∈ (ENode.app f' a').children, c < st₂.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size hf₂
              · exact denote_lt_size ha₂
            have hwf₃ : (st₂.intern (.app f' a')).2.WF :=
              intern_wf hwf₂ hcI (by simp [ENode.levels])
                (by simp [ENode.names])
            have hext₃ : Ext st₂ (st₂.intern (.app f' a')).2 := intern_ext _ _
            have hdI := intern_denote (n := .app f' a') hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hf₂, ha₂]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₃, hextAll, ?_, hlinv₂.mono hext₃, hcond⟩
            exact (hinv₂.mono hext₃ hwf₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo ty
              with ⟨ty', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiateLevelParamsIGo ks us st₁ memo₁ lmemo₁ body
              with ⟨body', st₂, memo₂, lmemo₂⟩
            rw [h₂] at hgo
            rcases h₃ : substLIBM ks us st₂ lmemo₂ m with ⟨m', st₃, lmemo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.lam nm ty' body' m') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih ty hguard.1 hwf hus hinv hlinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hlinv₂, hden₂⟩ :=
              ih body hguard.2 hwf₁ hus₁ hinv₁ hlinv₁ h₂
            have hus₂ := denoteLList_mono hext₂ hus₁
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            obtain ⟨hwf₃, hext₃, hlinv₃, hbden₃⟩ :=
              substLIBM_spec hwf₂ hus₂ hlinv₂ h₃
            have hm₃ : denoteBM st₃.denoteL m'
                = some ⟨bm.bi, bm.cod.map (Level.subst ks lus)⟩ := hbden₃ bm hbm₂
            have ht₃ : st₃.denote ty' = some (xt.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hb₃ : st₃.denote body'
                = some (xb.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (hden₂ xb (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.lam nm ty' body' m').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.lam nm ty' body' m')).2.WF :=
              intern_wf hwf₃ hcI
                (by simpa [ENode.levels] using denoteBM_lt_size hm₃)
                (fun p hp => Nat.lt_of_lt_of_le
                  (hnms p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.lam nm ty' body' m')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hb₃, hm₃,
                denoteN_mono hext₃ hnm₂]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₄, hextAll, ?_, hlinv₃.mono hext₄, hcond⟩
            exact ((hinv₂.mono hext₃ hwf₂).mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo ty
              with ⟨ty', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiateLevelParamsIGo ks us st₁ memo₁ lmemo₁ body
              with ⟨body', st₂, memo₂, lmemo₂⟩
            rw [h₂] at hgo
            rcases h₃ : substLIBM ks us st₂ lmemo₂ m with ⟨m', st₃, lmemo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.forallE nm ty' body' m') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih ty hguard.1 hwf hus hinv hlinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hlinv₂, hden₂⟩ :=
              ih body hguard.2 hwf₁ hus₁ hinv₁ hlinv₁ h₂
            have hus₂ := denoteLList_mono hext₂ hus₁
            have hbm₂ : denoteBM st₂.denoteL m = some bm :=
              denoteBM_mono (hext₁.trans hext₂) hbm
            have hnm₂ : st₂.denoteN nm = some nmv :=
              denoteN_mono (hext₁.trans hext₂) hnm
            obtain ⟨hwf₃, hext₃, hlinv₃, hbden₃⟩ :=
              substLIBM_spec hwf₂ hus₂ hlinv₂ h₃
            have hm₃ : denoteBM st₃.denoteL m'
                = some ⟨bm.bi, bm.cod.map (Level.subst ks lus)⟩ := hbden₃ bm hbm₂
            have ht₃ : st₃.denote ty' = some (xt.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hb₃ : st₃.denote body'
                = some (xb.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (hden₂ xb (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.forallE nm ty' body' m').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.forallE nm ty' body' m')).2.WF :=
              intern_wf hwf₃ hcI
                (by simpa [ENode.levels] using denoteBM_lt_size hm₃)
                (fun p hp => Nat.lt_of_lt_of_le
                  (hnms p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.forallE nm ty' body' m')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hb₃, hm₃,
                denoteN_mono hext₃ hnm₂]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₄, hextAll, ?_, hlinv₃.mono hext₄, hcond⟩
            exact ((hinv₂.mono hext₃ hwf₂).mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo ty
              with ⟨ty', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : instantiateLevelParamsIGo ks us st₁ memo₁ lmemo₁ val
              with ⟨val', st₂, memo₂, lmemo₂⟩
            rw [h₂] at hgo
            rcases h₃ : instantiateLevelParamsIGo ks us st₂ memo₂ lmemo₂ body
              with ⟨body', st₃, memo₃, lmemo₃⟩
            rw [h₃] at hgo
            rcases h₄ : st₃.intern (.letE nm ty' val' body') with ⟨ri, st₄⟩
            rw [h₄] at hgo
            cases hgo
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih ty hguard.1 hwf hus hinv hlinv h₁
            have hus₁ := denoteLList_mono hext₁ hus
            obtain ⟨hwf₂, hext₂, hinv₂, hlinv₂, hden₂⟩ :=
              ih val hguard.2.1 hwf₁ hus₁ hinv₁ hlinv₁ h₂
            have hus₂ := denoteLList_mono hext₂ hus₁
            obtain ⟨hwf₃, hext₃, hinv₃, hlinv₃, hden₃⟩ :=
              ih body hguard.2.2 hwf₂ hus₂ hinv₂ hlinv₂ h₃
            have ht₃ : st₃.denote ty' = some (xt.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (denote_mono hext₂ (hden₁ xt ht))
            have hvv₃ : st₃.denote val'
                = some (xv.instantiateLevelParams ks lus) :=
              denote_mono hext₃ (hden₂ xv (denote_mono hext₁ hvv))
            have hb₃ : st₃.denote body'
                = some (xb.instantiateLevelParams ks lus) :=
              hden₃ xb (denote_mono hext₂ (denote_mono hext₁ hb))
            have hcI : ∀ c ∈ (ENode.letE nm ty' val' body').children,
                c < st₃.nodes.size := by
              simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
              rintro c (rfl | rfl | rfl)
              · exact denote_lt_size ht₃
              · exact denote_lt_size hvv₃
              · exact denote_lt_size hb₃
            have hwf₄ : (st₃.intern (.letE nm ty' val' body')).2.WF :=
              intern_wf hwf₃ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  (hext₁.trans (hext₂.trans hext₃)).nsize_le)
            have hext₄ : Ext st₃ (st₃.intern (.letE nm ty' val' body')).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .letE nm ty' val' body') hwf₃ hcI
            rw [h₄] at hwf₄ hext₄ hdI
            have hextAll : Ext st st₄ :=
              hext₁.trans (hext₂.trans (hext₃.trans hext₄))
            have hcond : ∀ x, st.denote e = some x →
                st₄.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃,
                denoteN_mono (hext₁.trans (hext₂.trans hext₃)) hnm]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₄, hextAll, ?_, hlinv₃.mono hext₄, hcond⟩
            exact (hinv₃.mono hext₄ hwf₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            rcases h₁ : instantiateLevelParamsIGo ks us st memo lmemo sub
              with ⟨sub', st₁, memo₁, lmemo₁⟩
            rw [h₁] at hgo
            rcases h₂ : st₁.intern (.proj s j sub') with ⟨ri, st₂⟩
            rw [h₂] at hgo
            cases hgo
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hlinv₁, hden₁⟩ :=
              ih sub hguard hwf hus hinv hlinv h₁
            have hs₁ : st₁.denote sub' = some (xs.instantiateLevelParams ks lus) :=
              hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF :=
              intern_wf hwf₁ hcI (by simp [ENode.levels]) (fun p hp =>
                Nat.lt_of_lt_of_le
                  (hwf.names_lt e _ hn p (by simpa [ENode.names] using hp))
                  hext₁.nsize_le)
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.instantiateLevelParams ks lus) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁, denoteN_mono hext₁ hnm]
              simp [Expr.instantiateLevelParams]
            refine ⟨hwf₂, hextAll, ?_, hlinv₁.mono hext₂, hcond⟩
            exact (hinv₁.mono hext₂ hwf₁).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hwf hesz hcond)

/-- `instantiateLevelParamsI` commutes with `denote` (the replacement
levels are interned indices, their denotations the substituted
levels). -/
theorem instantiateLevelParamsI_spec {st : EStore} {ks : List Name}
    {us : List LIdx} {lus : List Level} {e : EIdx} {a : Expr}
    (hwf : st.WF) (hus : denoteLList st.denoteL us = some lus)
    (he : st.denote e = some a) :
    (st.instantiateLevelParamsI ks us e).2.WF ∧
      Ext st (st.instantiateLevelParamsI ks us e).2 ∧
      (st.instantiateLevelParamsI ks us e).2.denote
          (st.instantiateLevelParamsI ks us e).1
        = some (a.instantiateLevelParams ks lus) := by
  rcases hgo : instantiateLevelParamsIGo ks us st {} {} e
    with ⟨r, st', memo', lmemo'⟩
  obtain ⟨hwf', hext', -, -, hcond⟩ :=
    instantiateLevelParamsIGo_spec e hwf hus Memo0Inv.empty LvlMemoInv.empty hgo
  simp only [instantiateLevelParamsI, hgo]
  exact ⟨hwf', hext', hcond a he⟩


/-! ## Pure queries agree with the `Expr` versions

The queries never change the store, so their memo invariants need
neither the range component nor extension transport. -/

/-- Memo invariant for a cursor-free query implementing `g`. -/
def QMemo0Inv {β : Type} (st : EStore) (g : Expr → β)
    (memo : Std.HashMap EIdx β) : Prop :=
  ∀ (e : EIdx) (r : β), memo[e]? = some r →
    ∀ x, st.denote e = some x → r = g x

theorem QMemo0Inv.empty {β : Type} {st : EStore} {g : Expr → β} :
    QMemo0Inv st g {} := by
  intro e r hr
  simp at hr

theorem QMemo0Inv.insert {β : Type} {st : EStore} {g : Expr → β}
    {memo : Std.HashMap EIdx β} {e : EIdx} {r : β}
    (h : QMemo0Inv st g memo)
    (hcond : ∀ x, st.denote e = some x → r = g x) :
    QMemo0Inv st g (memo.insert e r) := by
  intro e' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : e = e'
  · subst hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact hcond
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' r' hr'

/-- Memo invariant for a query with a `Nat` cursor implementing `g`. -/
def QMemoNInv {β : Type} (st : EStore) (g : Expr → Nat → β)
    (memo : Std.HashMap (EIdx × Nat) β) : Prop :=
  ∀ (e : EIdx) (c : Nat) (r : β), memo[(e, c)]? = some r →
    ∀ x, st.denote e = some x → r = g x c

theorem QMemoNInv.empty {β : Type} {st : EStore} {g : Expr → Nat → β} :
    QMemoNInv st g {} := by
  intro e c r hr
  simp at hr

theorem QMemoNInv.insert {β : Type} {st : EStore} {g : Expr → Nat → β}
    {memo : Std.HashMap (EIdx × Nat) β} {e : EIdx} {c : Nat} {r : β}
    (h : QMemoNInv st g memo)
    (hcond : ∀ x, st.denote e = some x → r = g x c) :
    QMemoNInv st g (memo.insert (e, c) r) := by
  intro e' c' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : (e, c) = (e', c')
  · obtain ⟨rfl, rfl⟩ := Prod.mk.injEq .. ▸ hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact hcond
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' c' r' hr'

/-- `hasFvarI` agrees with `Expr.hasFvar` — an `O(1)` consequence of
the eager range entry's exactness (task #87). -/
theorem hasFvarI_spec {st : EStore} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    st.hasFvarI e = a.hasFvar := by
  show (st.fvarRangeD e != 0) = a.hasFvar
  rw [hwf.fvarRangeD_exact e he, fvarRange_bne_zero]


theorem looseBVarsBoundedIGo_spec {st : EStore} (hwf : st.WF) :
    ∀ (e : EIdx) {memo : Std.HashMap (EIdx × Nat) Bool} {k : Nat} {r : Bool}
      {memo' : Std.HashMap (EIdx × Nat) Bool},
      QMemoNInv st (fun x c => x.looseBVarsBounded c) memo →
      looseBVarsBoundedIGo st memo k e = (r, memo') →
      QMemoNInv st (fun x c => x.looseBVarsBounded c) memo' ∧
        ∀ x, st.denote e = some x → r = x.looseBVarsBounded k := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo k r memo' hinv hgo
    unfold looseBVarsBoundedIGo at hgo
    split at hgo
    · rename_i hhit
      injection hgo with hgr hgm
      subst hgr
      subst hgm
      exact ⟨hinv, hinv _ _ _ hhit⟩
    · split at hgo
      · rename_i hnone
        injection hgo with hgr hgm
        subst hgr
        subst hgm
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              decide (i < k) = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨xt, hxt⟩ := denote_total hwf t
            (Nat.lt_trans (hcl t (by simp [ENode.children])) hesz)
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.fvar idx nmv xt) := by
            rw [hde, denoteNode, hxt, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              true = x.looseBVarsBounded k := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.looseBVarsBounded]
          exact ⟨hinv.insert hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            split at hgo
            · -- rf = true: continue with the argument
              rename_i hrf
              rcases h₂ : looseBVarsBoundedIGo st memo₁ k a with ⟨ra, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  ra = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [hrf] at h1
                simp [Expr.looseBVarsBounded, ← h1, ← hden₂ xa ha]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · -- rf = false: short-circuit false
              rename_i hrf
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [Bool.not_eq_true] at hrf
                rw [hrf] at h1
                simp [Expr.looseBVarsBounded, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : looseBVarsBoundedIGo st memo₁ (k + 1) body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : looseBVarsBoundedIGo st memo₁ (k + 1) body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : looseBVarsBoundedIGo st memo₁ k val with ⟨rv, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
              split at hgo
              · rename_i hrv
                rcases h₃ : looseBVarsBoundedIGo st memo₂ (k + 1) body with ⟨rb, memo₃⟩
                rw [h₃] at hgo
                try dsimp only at hgo
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
                have hcond : ∀ x, st.denote e = some x →
                    rb = x.looseBVarsBounded k := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h1 := hden₁ xt ht
                  have h2 := hden₂ xv hvv
                  rw [hrt] at h1
                  rw [hrv] at h2
                  simp [Expr.looseBVarsBounded, ← h1, ← h2, ← hden₃ xb hb]
                exact ⟨hinv₃.insert hcond, hcond⟩
              · rename_i hrv
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                have hcond : ∀ x, st.denote e = some x →
                    false = x.looseBVarsBounded k := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h2 := hden₂ xv hvv
                  rw [Bool.not_eq_true] at hrv
                  rw [hrv] at h2
                  simp [Expr.looseBVarsBounded, ← h2]
                exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.looseBVarsBounded k := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.looseBVarsBounded, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            rcases h₁ : looseBVarsBoundedIGo st memo k sub with ⟨rs, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                rs = x.looseBVarsBounded k := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.looseBVarsBounded] using hden₁ xs hs
            exact ⟨hinv₁.insert hcond, hcond⟩

/-- `looseBVarsBoundedI` agrees with `Expr.looseBVarsBounded`. -/
theorem looseBVarsBoundedI_spec {st : EStore} {k : Nat} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    st.looseBVarsBoundedI k e = a.looseBVarsBounded k := by
  rcases hgo : looseBVarsBoundedIGo st {} k e with ⟨r, memo'⟩
  obtain ⟨-, hcond⟩ := looseBVarsBoundedIGo_spec hwf e QMemoNInv.empty hgo
  simp only [looseBVarsBoundedI, hgo]
  exact hcond a he

theorem wscopedBIGo_spec {st : EStore} (hwf : st.WF) :
    ∀ (e : EIdx) {memo : Std.HashMap (EIdx × Nat) Bool} {d : Nat} {r : Bool}
      {memo' : Std.HashMap (EIdx × Nat) Bool},
      QMemoNInv st (fun x c => x.wscopedB c) memo →
      wscopedBIGo st memo d e = (r, memo') →
      QMemoNInv st (fun x c => x.wscopedB c) memo' ∧
        ∀ x, st.denote e = some x → r = x.wscopedB d := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo d r memo' hinv hgo
    unfold wscopedBIGo at hgo
    split at hgo
    · rename_i hhit
      injection hgo with hgr hgm
      subst hgr
      subst hgm
      exact ⟨hinv, hinv _ _ _ hhit⟩
    · split at hgo
      · rename_i hnone
        injection hgo with hgr hgm
        subst hgr
        subst hgm
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.wscopedB d := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.wscopedB]
          exact ⟨hinv.insert hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.wscopedB d := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.wscopedB]
          exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.wscopedB d := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.wscopedB]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.wscopedB d := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.wscopedB]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl t (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf t (Nat.lt_trans hguard hesz)
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hwf.names_lt e _ hn nm (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nmv xt) := by
              rw [hde, denoteNode, hxt, hnm]; rfl
            split at hgo
            · -- idx < d: recurse into the annotation at cutoff idx
              rename_i hlt
              rcases h₁ : wscopedBIGo st memo idx t with ⟨rt, memo₁⟩
              rw [h₁] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₁, hden₁⟩ := ih t hguard hinv h₁
              have hcond : ∀ x, st.denote e = some x → rt = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.wscopedB, hlt, ← hden₁ xt hxt]
              exact ⟨hinv₁.insert hcond, hcond⟩
            · rename_i hlt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.wscopedB, hlt]
              exact ⟨hinv.insert hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            rcases h₁ : wscopedBIGo st memo d f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            split at hgo
            · rename_i hrf
              rcases h₂ : wscopedBIGo st memo₁ d a with ⟨ra, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x → ra = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [hrf] at h1
                simp [Expr.wscopedB, ← h1, ← hden₂ xa ha]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrf
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [Bool.not_eq_true] at hrf
                rw [hrf] at h1
                simp [Expr.wscopedB, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : wscopedBIGo st memo d ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : wscopedBIGo st memo₁ d body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x → rb = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : wscopedBIGo st memo d ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : wscopedBIGo st memo₁ d body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x → rb = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            rcases h₁ : wscopedBIGo st memo d ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : wscopedBIGo st memo₁ d val with ⟨rv, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
              split at hgo
              · rename_i hrv
                rcases h₃ : wscopedBIGo st memo₂ d body with ⟨rb, memo₃⟩
                rw [h₃] at hgo
                try dsimp only at hgo
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
                have hcond : ∀ x, st.denote e = some x → rb = x.wscopedB d := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h1 := hden₁ xt ht
                  have h2 := hden₂ xv hvv
                  rw [hrt] at h1
                  rw [hrv] at h2
                  simp [Expr.wscopedB, ← h1, ← h2, ← hden₃ xb hb]
                exact ⟨hinv₃.insert hcond, hcond⟩
              · rename_i hrv
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h2 := hden₂ xv hvv
                  rw [Bool.not_eq_true] at hrv
                  rw [hrv] at h2
                  simp [Expr.wscopedB, ← h2]
                exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x → false = x.wscopedB d := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.wscopedB, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            rcases h₁ : wscopedBIGo st memo d sub with ⟨rs, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x → rs = x.wscopedB d := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.wscopedB] using hden₁ xs hs
            exact ⟨hinv₁.insert hcond, hcond⟩

/-- `wscopedBI` agrees with `Expr.wscopedB`. -/
theorem wscopedBI_spec {st : EStore} {d : Nat} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    st.wscopedBI d e = a.wscopedB d := by
  rcases hgo : wscopedBIGo st {} d e with ⟨r, memo'⟩
  obtain ⟨-, hcond⟩ := wscopedBIGo_spec hwf e QMemoNInv.empty hgo
  simp only [wscopedBI, hgo]
  exact hcond a he

theorem constsResolveIGo_spec {st : EStore} {env : Env} (hwf : st.WF) :
    ∀ (e : EIdx) {memo : Std.HashMap EIdx Bool} {r : Bool}
      {memo' : Std.HashMap EIdx Bool},
      QMemo0Inv st (fun x => x.constsResolve env) memo →
      constsResolveIGo st env memo e = (r, memo') →
      QMemo0Inv st (fun x => x.constsResolve env) memo' ∧
        ∀ x, st.denote e = some x → r = x.constsResolve env := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo r memo' hinv hgo
    unfold constsResolveIGo at hgo
    split at hgo
    · rename_i hhit
      injection hgo with hgr hgm
      subst hgr
      subst hgm
      exact ⟨hinv, hinv _ _ hhit⟩
    · split at hgo
      · rename_i hnone
        injection hgo with hgr hgm
        subst hgr
        subst hgm
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.constsResolve env := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.constsResolve]
          exact ⟨hinv.insert hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x → true = x.constsResolve env := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [Expr.constsResolve]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          cases l with
          | strVal sv =>
            dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            have hx : st.denote e = some (.lit (.strVal sv)) := by
              rw [hde]; rfl
            have hcond : ∀ x, st.denote e = some x →
                ((env.find? natName).isSome && (env.find? natZeroName).isSome &&
                  (env.find? natSuccName).isSome &&
                  (env.find? stringName).isSome &&
                  (env.find? stringOfListName).isSome &&
                  (env.find? listName).isSome &&
                  (env.find? listNilName).isSome &&
                  (env.find? listConsName).isSome &&
                  (env.find? charName).isSome &&
                  (env.find? charOfNatName).isSome) = x.constsResolve env := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simp [Expr.constsResolve]
            exact ⟨hinv.insert hcond, hcond⟩
          | natVal nv =>
            dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            have hx : st.denote e = some (.lit (.natVal nv)) := by
              rw [hde]; rfl
            have hcond : ∀ x, st.denote e = some x →
                ((env.find? natName).isSome &&
                  (env.find? natZeroName).isSome &&
                  (env.find? natSuccName).isSome) = x.constsResolve env := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simp [Expr.constsResolve]
            exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              (match st.readbackN nm with
               | some name => (env.find? name).isSome
               | none => false) = x.constsResolve env := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            rw [readbackN_eq_denoteN, hnm]
            simp [Expr.constsResolve]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl t (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf t (Nat.lt_trans hguard hesz)
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hwf.names_lt e _ hn nm (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nmv xt) := by
              rw [hde, denoteNode, hxt, hnm]; rfl
            rcases h₁ : constsResolveIGo st env memo t with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih t hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x → rt = x.constsResolve env := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              simpa [Expr.constsResolve] using hden₁ xt hxt
            exact ⟨hinv₁.insert hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            rcases h₁ : constsResolveIGo st env memo f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            split at hgo
            · rename_i hrf
              rcases h₂ : constsResolveIGo st env memo₁ a with ⟨ra, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  ra = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [hrf] at h1
                simp [Expr.constsResolve, ← h1, ← hden₂ xa ha]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrf
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xf hf
                rw [Bool.not_eq_true] at hrf
                rw [hrf] at h1
                simp [Expr.constsResolve, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : constsResolveIGo st env memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : constsResolveIGo st env memo₁ body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : constsResolveIGo st env memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : constsResolveIGo st env memo₁ body with ⟨rb, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
              have hcond : ∀ x, st.denote e = some x →
                  rb = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1, ← hden₂ xb hb]
              exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            rcases h₁ : constsResolveIGo st env memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            split at hgo
            · rename_i hrt
              rcases h₂ : constsResolveIGo st env memo₁ val with ⟨rv, memo₂⟩
              rw [h₂] at hgo
              try dsimp only at hgo
              obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
              split at hgo
              · rename_i hrv
                rcases h₃ : constsResolveIGo st env memo₂ body with ⟨rb, memo₃⟩
                rw [h₃] at hgo
                try dsimp only at hgo
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
                have hcond : ∀ x, st.denote e = some x →
                    rb = x.constsResolve env := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h1 := hden₁ xt ht
                  have h2 := hden₂ xv hvv
                  rw [hrt] at h1
                  rw [hrv] at h2
                  simp [Expr.constsResolve, ← h1, ← h2, ← hden₃ xb hb]
                exact ⟨hinv₃.insert hcond, hcond⟩
              · rename_i hrv
                injection hgo with hgr hgm
                subst hgr
                subst hgm
                have hcond : ∀ x, st.denote e = some x →
                    false = x.constsResolve env := by
                  intro x hxx
                  rw [hx] at hxx; cases hxx
                  have h2 := hden₂ xv hvv
                  rw [Bool.not_eq_true] at hrv
                  rw [hrv] at h2
                  simp [Expr.constsResolve, ← h2]
                exact ⟨hinv₂.insert hcond, hcond⟩
            · rename_i hrt
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                have h1 := hden₁ xt ht
                rw [Bool.not_eq_true] at hrt
                rw [hrt] at h1
                simp [Expr.constsResolve, ← h1]
              exact ⟨hinv₁.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            rw [readbackN_eq_denoteN, hnm] at hgo
            dsimp only at hgo
            split at hgo
            · -- struct name resolves: recurse
              rename_i hres
              rcases h₁ : constsResolveIGo st env memo sub with ⟨rs, memo₁⟩
              rw [h₁] at hgo
              try dsimp only at hgo
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
              have hcond : ∀ x, st.denote e = some x →
                  rs = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                simp [Expr.constsResolve, hres, ← hden₁ xs hs]
              exact ⟨hinv₁.insert hcond, hcond⟩
            · rename_i hres
              injection hgo with hgr hgm
              subst hgr
              subst hgm
              have hcond : ∀ x, st.denote e = some x →
                  false = x.constsResolve env := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [Bool.not_eq_true] at hres
                simp [Expr.constsResolve, hres]
              exact ⟨hinv.insert hcond, hcond⟩

/-- `constsResolveI` agrees with `Expr.constsResolve`. -/
theorem constsResolveI_spec {st : EStore} {env : Env} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    st.constsResolveI env e = a.constsResolve env := by
  rcases hgo : constsResolveIGo st env {} e with ⟨r, memo'⟩
  obtain ⟨-, hcond⟩ := constsResolveIGo_spec hwf e QMemo0Inv.empty hgo
  simp only [constsResolveI, hgo]
  exact hcond a he

/-! ### `fvarLeavesI`

The interned leaf list carries type *indices*; it agrees with
`Expr.fvarLeaves` after mapping the denotation over the type
component. -/

/-- Denotation image of an interned leaf list (name components
through the name denotation, task #88). -/
def leavesDen (st : EStore) (r : List (Nat × NIdx × EIdx)) :
    List (Nat × Option Name × Option Expr) :=
  r.map fun l => (l.1, st.denoteN l.2.1, st.denote l.2.2)

/-- The `Expr`-side leaf list in the same shape. -/
def leavesExp (x : Expr) : List (Nat × Option Name × Option Expr) :=
  x.fvarLeaves.map fun l => (l.1, some l.2.1, some l.2.2)

theorem leavesDen_append {st : EStore} {r₁ r₂ : List (Nat × NIdx × EIdx)} :
    leavesDen st (r₁ ++ r₂) = leavesDen st r₁ ++ leavesDen st r₂ :=
  List.map_append ..

/-- Memo invariant for the leaf-list traversal. -/
def LMemoInv (st : EStore)
    (memo : Std.HashMap EIdx (List (Nat × NIdx × EIdx))) : Prop :=
  ∀ (e : EIdx) (r : List (Nat × NIdx × EIdx)), memo[e]? = some r →
    ∀ x, st.denote e = some x → leavesDen st r = leavesExp x

theorem LMemoInv.empty {st : EStore} : LMemoInv st {} := by
  intro e r hr
  simp at hr

theorem LMemoInv.insert {st : EStore}
    {memo : Std.HashMap EIdx (List (Nat × NIdx × EIdx))} {e : EIdx}
    {r : List (Nat × NIdx × EIdx)} (h : LMemoInv st memo)
    (hcond : ∀ x, st.denote e = some x → leavesDen st r = leavesExp x) :
    LMemoInv st (memo.insert e r) := by
  intro e' r' hr'
  rw [Std.HashMap.getElem?_insert] at hr'
  by_cases hk : e = e'
  · subst hk
    rw [if_pos (by simp)] at hr'
    cases hr'
    exact hcond
  · rw [if_neg (by simpa using hk)] at hr'
    exact h e' r' hr'

theorem fvarLeavesIGo_spec {st : EStore} (hwf : st.WF) :
    ∀ (e : EIdx) {memo : Std.HashMap EIdx (List (Nat × NIdx × EIdx))}
      {r : List (Nat × NIdx × EIdx)}
      {memo' : Std.HashMap EIdx (List (Nat × NIdx × EIdx))},
      LMemoInv st memo →
      fvarLeavesIGo st memo e = (r, memo') →
      LMemoInv st memo' ∧
        ∀ x, st.denote e = some x → leavesDen st r = leavesExp x := by
  intro e
  induction e using Nat.strongRecOn with
  | _ e ih =>
    intro memo r memo' hinv hgo
    unfold fvarLeavesIGo at hgo
    split at hgo
    · rename_i hhit
      injection hgo with hgr hgm
      subst hgr
      subst hgm
      exact ⟨hinv, hinv _ _ hhit⟩
    · split at hgo
      · rename_i hnone
        injection hgo with hgr hgm
        subst hgr
        subst hgm
        refine ⟨hinv, ?_⟩
        intro x hx
        obtain ⟨n, hn, -, -⟩ := denote_some_inv hx
        rw [hn] at hnone
        cases hnone
      · rename_i n hn
        have hesz : e < st.nodes.size := (Array.getElem?_eq_some_iff.mp hn).1
        have hcl := hwf.children_lt e n hn
        have hde := denote_node hn hcl
        cases n with
        | bvar i =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.bvar i) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              leavesDen st [] = leavesExp x := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [leavesDen, leavesExp, Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lu, hlu⟩ := denoteL_total hwf u
            (hwf.levels_lt e _ hn u (by simp [ENode.levels]))
          have hx : st.denote e = some (.sort lu) := by
            rw [hde, denoteNode, hlu]; rfl
          have hcond : ∀ x, st.denote e = some x →
              leavesDen st [] = leavesExp x := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [leavesDen, leavesExp, Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          obtain ⟨lus, hlus⟩ := denoteLList_total hwf us
            (fun v hv => hwf.levels_lt e _ hn v (by simp [ENode.levels, hv]))
          obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
            (hwf.names_lt e _ hn nm (by simp [ENode.names]))
          have hx : st.denote e = some (.const nmv lus) := by
            rw [hde, denoteNode, hlus, hnm]; rfl
          have hcond : ∀ x, st.denote e = some x →
              leavesDen st [] = leavesExp x := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [leavesDen, leavesExp, Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | lit l =>
          dsimp only at hgo
          injection hgo with hgr hgm
          subst hgr
          subst hgm
          have hx : st.denote e = some (.lit l) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              leavesDen st [] = leavesExp x := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simp [leavesDen, leavesExp, Expr.fvarLeaves]
          exact ⟨hinv.insert hcond, hcond⟩
        | fvar idx nm t =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl t (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xt, hxt⟩ := denote_total hwf t (Nat.lt_trans hguard hesz)
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hwf.names_lt e _ hn nm (by simp [ENode.names]))
            have hx : st.denote e = some (.fvar idx nmv xt) := by
              rw [hde, denoteNode, hxt, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo t with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih t hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st ((idx, nm, t) :: rt) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              have := hden₁ xt hxt
              simp only [leavesDen, leavesExp, List.map_cons, Expr.fvarLeaves] at *
              simp [hxt, this, hnm]
            exact ⟨hinv₁.insert hcond, hcond⟩
        | app f a =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl f (by simp [ENode.children]),
              hcl a (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xf, hf⟩ := denote_total hwf f (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xa, ha⟩ := denote_total hwf a (Nat.lt_trans hguard.2 hesz)
            have hx : st.denote e = some (.app xf xa) := by
              rw [hde, denoteNode, hf, ha]; rfl
            rcases h₁ : fvarLeavesIGo st memo f with ⟨rf, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            rcases h₂ : fvarLeavesIGo st memo₁ a with ⟨ra, memo₂⟩
            rw [h₂] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih f hguard.1 hinv h₁
            obtain ⟨hinv₂, hden₂⟩ := ih a hguard.2 hinv₁ h₂
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st (rf ++ ra) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [leavesDen_append, hden₁ xf hf, hden₂ xa ha]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₂.insert hcond, hcond⟩
        | lam nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.lam nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            rcases h₂ : fvarLeavesIGo st memo₁ body with ⟨rb, memo₂⟩
            rw [h₂] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st (rt ++ rb) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [leavesDen_append, hden₁ xt ht, hden₂ xb hb]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₂.insert hcond, hcond⟩
        | forallE nm ty body m =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2 hesz)
            obtain ⟨bm, hbm⟩ := denoteBM_total hwf m
              (fun u hu => hwf.levels_lt e _ hn u
                (by simpa [ENode.levels] using hu))
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.forallE nmv xt xb bm) := by
              rw [hde, denoteNode, ht, hb, hbm, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            rcases h₂ : fvarLeavesIGo st memo₁ body with ⟨rb, memo₂⟩
            rw [h₂] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            obtain ⟨hinv₂, hden₂⟩ := ih body hguard.2 hinv₁ h₂
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st (rt ++ rb) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [leavesDen_append, hden₁ xt ht, hden₂ xb hb]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₂.insert hcond, hcond⟩
        | letE nm ty val body =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd ⟨hcl ty (by simp [ENode.children]),
              hcl val (by simp [ENode.children]),
              hcl body (by simp [ENode.children])⟩ hguard
          case isTrue hguard =>
            obtain ⟨xt, ht⟩ := denote_total hwf ty (Nat.lt_trans hguard.1 hesz)
            obtain ⟨xv, hvv⟩ := denote_total hwf val (Nat.lt_trans hguard.2.1 hesz)
            obtain ⟨xb, hb⟩ := denote_total hwf body (Nat.lt_trans hguard.2.2 hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf nm
              (hnms nm (by simp [ENode.names]))
            have hx : st.denote e = some (.letE nmv xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo ty with ⟨rt, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            rcases h₂ : fvarLeavesIGo st memo₁ val with ⟨rv, memo₂⟩
            rw [h₂] at hgo
            try dsimp only at hgo
            rcases h₃ : fvarLeavesIGo st memo₂ body with ⟨rb, memo₃⟩
            rw [h₃] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih ty hguard.1 hinv h₁
            obtain ⟨hinv₂, hden₂⟩ := ih val hguard.2.1 hinv₁ h₂
            obtain ⟨hinv₃, hden₃⟩ := ih body hguard.2.2 hinv₂ h₃
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st (rt ++ rv ++ rb) = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [leavesDen_append, leavesDen_append,
                hden₁ xt ht, hden₂ xv hvv, hden₃ xb hb]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₃.insert hcond, hcond⟩
        | proj s j sub =>
          dsimp only at hgo
          split at hgo
          case isFalse hguard =>
            exact absurd (hcl sub (by simp [ENode.children])) hguard
          case isTrue hguard =>
            obtain ⟨xs, hs⟩ := denote_total hwf sub (Nat.lt_trans hguard hesz)
            have hnms := hwf.names_lt e _ hn
            obtain ⟨nmv, hnm⟩ := denoteN_total hwf s
              (hnms s (by simp [ENode.names]))
            have hx : st.denote e = some (.proj nmv j xs) := by
              rw [hde, denoteNode, hs, hnm]; rfl
            rcases h₁ : fvarLeavesIGo st memo sub with ⟨rs, memo₁⟩
            rw [h₁] at hgo
            try dsimp only at hgo
            injection hgo with hgr hgm
            subst hgr
            subst hgm
            obtain ⟨hinv₁, hden₁⟩ := ih sub hguard hinv h₁
            have hcond : ∀ x, st.denote e = some x →
                leavesDen st rs = leavesExp x := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hden₁ xs hs]
              simp [leavesExp, Expr.fvarLeaves]
            exact ⟨hinv₁.insert hcond, hcond⟩

/-- `fvarLeavesI` agrees with `Expr.fvarLeaves` after denoting the type
components. -/
theorem fvarLeavesI_spec {st : EStore} {e : EIdx} {a : Expr}
    (hwf : st.WF) (he : st.denote e = some a) :
    leavesDen st (st.fvarLeavesI e) = leavesExp a := by
  rcases hgo : fvarLeavesIGo st {} e with ⟨r, memo'⟩
  obtain ⟨-, hcond⟩ := fvarLeavesIGo_spec hwf e LMemoInv.empty hgo
  simp only [fvarLeavesI, hgo]
  exact hcond a he


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
end EStore

end Setlec
