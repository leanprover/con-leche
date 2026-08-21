import Setlec.Kernel.IExpr

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
* [ ] `abstract1I`, `instantiateLevelParamsI` commute with `denote`
* [ ] pure queries (`hasFvarI`, `looseBVarsBoundedI`, `wscopedBI`,
      `fvarLeavesI`, `constsResolveI`) agree with the `Expr` versions
-/

namespace Setlec

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
indices: rebuild the `Expr` constructor over the children's values. -/
def denoteNode (den : EIdx → Option Expr) : ENode → Option Expr
  | .bvar i => some (.bvar i)
  | .fvar idx nm t => (den t).map (Expr.fvar idx nm)
  | .sort u => some (.sort u)
  | .const n us => some (.const n us)
  | .app f a => (den f).bind fun ef => (den a).map fun ea => .app ef ea
  | .lam n t b m => (den t).bind fun et => (den b).map fun eb => .lam n et eb m
  | .forallE n t b m =>
    (den t).bind fun et => (den b).map fun eb => .forallE n et eb m
  | .letE n t v b =>
    (den t).bind fun et => (den v).bind fun ev => (den b).map fun eb =>
      .letE n et ev eb
  | .lit l => some (.lit l)
  | .proj s j e => (den e).map (Expr.proj s j)

/-- Structural denotation of an index: read the node and denote its
children recursively.  Out-of-range indices and forward references
(children not strictly below their parent) denote `none`, which makes
the recursion well-founded on the index. -/
def denote (st : EStore) (i : EIdx) : Option Expr :=
  match st.nodes[i]? with
  | none => none
  | some n =>
    denoteNode (fun j => if _h : j < i then st.denote j else none) n
termination_by i

/-- `denoteNode` only looks at the children. -/
theorem denoteNode_congr {d₁ d₂ : EIdx → Option Expr} {n : ENode}
    (h : ∀ c ∈ n.children, d₁ c = d₂ c) : denoteNode d₁ n = denoteNode d₂ n := by
  cases n <;> simp_all [denoteNode, ENode.children]

/-- One-step unfolding of `denote` when the children are known to sit
below the index: the guards disappear. -/
theorem denote_node {st : EStore} {i : EIdx} {n : ENode}
    (hn : st.nodes[i]? = some n) (hc : ∀ c ∈ n.children, c < i) :
    st.denote i = denoteNode st.denote n := by
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
      denoteNode st.denote n = some a := by
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
      rw [denoteNode, Option.map_eq_some_iff] at h
      obtain ⟨t', ht, rfl⟩ := h
      obtain ⟨hlt, ht⟩ := dite_denote_some ht
      refine ⟨by simp [ENode.children, hlt], ?_⟩
      rw [denoteNode, ht]; rfl
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
      rw [Option.map_eq_some_iff] at h
      obtain ⟨eb, hb, rfl⟩ := h
      obtain ⟨hltt, ht⟩ := dite_denote_some ht
      obtain ⟨hltb, hb⟩ := dite_denote_some hb
      refine ⟨by simp [ENode.children, hltt, hltb], ?_⟩
      rw [denoteNode, ht, hb]; rfl
    | forallE nm t b m =>
      rw [denoteNode, Option.bind_eq_some_iff] at h
      obtain ⟨et, ht, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨eb, hb, rfl⟩ := h
      obtain ⟨hltt, ht⟩ := dite_denote_some ht
      obtain ⟨hltb, hb⟩ := dite_denote_some hb
      refine ⟨by simp [ENode.children, hltt, hltb], ?_⟩
      rw [denoteNode, ht, hb]; rfl
    | letE nm t v b =>
      rw [denoteNode, Option.bind_eq_some_iff] at h
      obtain ⟨et, ht, h⟩ := h
      rw [Option.bind_eq_some_iff] at h
      obtain ⟨ev, hv, h⟩ := h
      rw [Option.map_eq_some_iff] at h
      obtain ⟨eb, hb, rfl⟩ := h
      obtain ⟨hltt, ht⟩ := dite_denote_some ht
      obtain ⟨hltv, hv⟩ := dite_denote_some hv
      obtain ⟨hltb, hb⟩ := dite_denote_some hb
      refine ⟨by simp [ENode.children, hltt, hltv, hltb], ?_⟩
      rw [denoteNode, ht, hv, hb]; rfl
    | proj s j e' =>
      rw [denoteNode, Option.map_eq_some_iff] at h
      obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨hlt, hx⟩ := dite_denote_some hx
      refine ⟨by simp [ENode.children, hlt], ?_⟩
      rw [denoteNode, hx]; rfl

/-- A denoted node's children denote. -/
theorem denoteNode_children_some {den : EIdx → Option Expr} {n : ENode}
    {a : Expr} (h : denoteNode den n = some a) :
    ∀ c ∈ n.children, ∃ b, den c = some b := by
  cases n <;>
    simp_all [denoteNode, ENode.children, Option.map_eq_some_iff,
      Option.bind_eq_some_iff] <;>
    obtain ⟨x, hx, h⟩ := h <;>
    (try obtain ⟨y, hy, h⟩ := h) <;>
    (try obtain ⟨z, hz, h⟩ := h) <;>
    simp_all

/-- Successful denotation implies the index is in range. -/
theorem denote_lt_size {st : EStore} {i : EIdx} {a : Expr}
    (h : st.denote i = some a) : i < st.nodes.size := by
  obtain ⟨n, hn, -, -⟩ := denote_some_inv h
  exact (Array.getElem?_eq_some_iff.mp hn).1

/-- Store extension: every stored node is still stored, at the same
index.  `intern`/`internExpr` only push new nodes, so they extend. -/
def Ext (st st' : EStore) : Prop :=
  ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n → st'.nodes[i]? = some n

theorem Ext.refl (st : EStore) : Ext st st := fun _ _ h => h

theorem Ext.trans {st₁ st₂ st₃ : EStore} (h₁ : Ext st₁ st₂)
    (h₂ : Ext st₂ st₃) : Ext st₁ st₃ :=
  fun i n h => h₂ i n (h₁ i n h)

/-- Denotation is stable under store extension (monotonicity). -/
theorem denote_mono {st st' : EStore} (hext : Ext st st') :
    ∀ {i : EIdx} {a : Expr}, st.denote i = some a → st'.denote i = some a := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro a h
    obtain ⟨n, hn, hc, hd⟩ := denote_some_inv h
    rw [denote_node (hext i n hn) hc, ← hd]
    apply denoteNode_congr
    intro c hcin
    obtain ⟨b, hb⟩ := denoteNode_children_some hd c hcin
    rw [hb, ih c (hc c hcin) hb]

/-- Stores agreeing on the nodes below `k` denote all indices below `k`
identically (in particular, pushing nodes never changes the denotation
of old indices, not even `none` ones). -/
theorem denote_agree {st st' : EStore} {k : Nat}
    (hpre : ∀ j, j < k → st'.nodes[j]? = st.nodes[j]?) :
    ∀ i, i < k → st'.denote i = st.denote i := by
  intro i
  induction i using Nat.strongRecOn with
  | _ i ih =>
    intro hik
    rw [denote.eq_def, denote.eq_def, hpre i hik]
    cases st.nodes[i]? with
    | none => rfl
    | some n =>
      exact denoteNode_congr fun c _hc => by
        by_cases hci : c < i
        · simp only [dif_pos hci]
          exact ih c hci (Nat.lt_trans hci hik)
        · simp [dif_neg hci]

/-- The store invariant: every node's children are strictly below its
own index, and the cons-table is exactly the graph of the node table
(in particular no node is stored at two indices). -/
structure WF (st : EStore) : Prop where
  children_lt : ∀ (i : EIdx) (n : ENode), st.nodes[i]? = some n →
    ∀ c ∈ n.children, c < i
  cons_graph : ∀ (n : ENode) (i : EIdx), st.cons[n]? = some i ↔ st.nodes[i]? = some n

theorem empty_wf : WF EStore.empty := by
  constructor
  · intro i n h
    simp [EStore.empty] at h
  · intro n i
    simp [EStore.empty]

/-! ## `intern` -/

/-- `intern` with the store destructuring (an RC optimization)
eliminated. -/
theorem intern_eq (st : EStore) (n : ENode) :
    st.intern n = match st.cons[n]? with
      | some i => (i, st)
      | none =>
        (st.nodes.size, ⟨st.nodes.push n, st.cons.insert n st.nodes.size⟩) := by
  obtain ⟨nodes, cons⟩ := st
  rfl

theorem intern_ext (st : EStore) (n : ENode) : Ext st (st.intern n).2 := by
  intro i m h
  rw [intern_eq]
  split
  · exact h
  · have : i < st.nodes.size := (Array.getElem?_eq_some_iff.mp h).1
    rw [Array.getElem?_push, if_neg (Nat.ne_of_lt this)]
    exact h

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
already-stored indices. -/
theorem intern_wf {st : EStore} {n : ENode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nodes.size) : (st.intern n).2.WF := by
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

/-- Interning a node whose children are already stored: the result
denotes the node's denotation over the *old* store. -/
theorem intern_denote {st : EStore} {n : ENode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nodes.size) :
    (st.intern n).2.denote (st.intern n).1 = denoteNode st.denote n := by
  have hn := intern_node (n := n) hwf
  rw [intern_eq] at hn ⊢
  split at hn
  · rename_i i h
    rw [denote_node hn (hwf.children_lt _ _ hn)]
  · rename_i hmiss
    have hagree : ∀ j, j < st.nodes.size →
        (⟨st.nodes.push n, st.cons.insert n st.nodes.size⟩ : EStore).denote j
          = st.denote j := by
      apply denote_agree
      intro j hj
      simp [Array.getElem?_push, Nat.ne_of_lt hj]
    rw [denote_node hn hc]
    exact denoteNode_congr fun c hcin => hagree c (hc c hcin)

/-! ## `internExpr`: round-trip -/

/-- One interning step of the round-trip: interning a node whose
children are stored and denote the subterms gives the invariant, the
extension, and the node's denotation. -/
private theorem intern_step {st : EStore} {n : ENode} (hwf : st.WF)
    (hc : ∀ c ∈ n.children, c < st.nodes.size) {a : Expr}
    (hd : denoteNode st.denote n = some a) :
    (st.intern n).2.WF ∧ Ext st (st.intern n).2 ∧
      (st.intern n).2.denote (st.intern n).1 = some a :=
  ⟨intern_wf hwf hc, intern_ext st n, by rw [intern_denote hwf hc]; exact hd⟩

/-- `internExpr` preserves the invariant, extends the store, and its
result denotes the interned expression. -/
theorem internExpr_spec {st : EStore} (hwf : st.WF) (e : Expr) :
    (st.internExpr e).2.WF ∧ Ext st (st.internExpr e).2 ∧
      (st.internExpr e).2.denote (st.internExpr e).1 = some e := by
  induction e generalizing st with
  | bvar i => exact intern_step hwf (by simp [ENode.children]) rfl
  | sort u => exact intern_step hwf (by simp [ENode.children]) rfl
  | const n us => exact intern_step hwf (by simp [ENode.children]) rfl
  | lit l => exact intern_step hwf (by simp [ENode.children]) rfl
  | fvar idx nm ty ih =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ih hwf
    rcases hI : st.internExpr ty with ⟨t, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    have hstep := intern_step (n := .fvar idx nm t) hwf₁
      (by simpa [ENode.children] using denote_lt_size hden₁)
      (a := .fvar idx nm ty) (by rw [denoteNode, hden₁]; rfl)
    simp only [internExpr, hI]
    exact ⟨hstep.1, hext₁.trans hstep.2.1, hstep.2.2⟩
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
    have hden₁' := denote_mono hext₂ hden₁
    have hstep := intern_step (n := .lam n ti bi m) hwf₂
      (by
        simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denote_lt_size hden₁'
        · exact denote_lt_size hden₂)
      (a := .lam n ty body m) (by rw [denoteNode, hden₁', hden₂]; rfl)
    simp only [internExpr, hI₁, hI₂]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans hstep.2.1), hstep.2.2⟩
  | forallE n ty body m ihty ihbody =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ihty hwf
    rcases hI₁ : st.internExpr ty with ⟨ti, st₁⟩
    simp only [hI₁] at hwf₁ hext₁ hden₁
    obtain ⟨hwf₂, hext₂, hden₂⟩ := ihbody hwf₁
    rcases hI₂ : st₁.internExpr body with ⟨bi, st₂⟩
    simp only [hI₂] at hwf₂ hext₂ hden₂
    have hden₁' := denote_mono hext₂ hden₁
    have hstep := intern_step (n := .forallE n ti bi m) hwf₂
      (by
        simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl)
        · exact denote_lt_size hden₁'
        · exact denote_lt_size hden₂)
      (a := .forallE n ty body m) (by rw [denoteNode, hden₁', hden₂]; rfl)
    simp only [internExpr, hI₁, hI₂]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans hstep.2.1), hstep.2.2⟩
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
    have hden₁' := denote_mono hext₃ (denote_mono hext₂ hden₁)
    have hden₂' := denote_mono hext₃ hden₂
    have hstep := intern_step (n := .letE n ti vi bi) hwf₃
      (by
        simp only [ENode.children, List.mem_cons, List.not_mem_nil, or_false]
        rintro c (rfl | rfl | rfl)
        · exact denote_lt_size hden₁'
        · exact denote_lt_size hden₂'
        · exact denote_lt_size hden₃)
      (a := .letE n ty val body)
      (by rw [denoteNode, hden₁', hden₂', hden₃]; rfl)
    simp only [internExpr, hI₁, hI₂, hI₃]
    exact ⟨hstep.1, hext₁.trans (hext₂.trans (hext₃.trans hstep.2.1)), hstep.2.2⟩
  | proj s i e ih =>
    obtain ⟨hwf₁, hext₁, hden₁⟩ := ih hwf
    rcases hI : st.internExpr e with ⟨ei, st₁⟩
    simp only [hI] at hwf₁ hext₁ hden₁
    have hstep := intern_step (n := .proj s i ei) hwf₁
      (by simpa [ENode.children] using denote_lt_size hden₁)
      (a := .proj s i e) (by rw [denoteNode, hden₁]; rfl)
    simp only [internExpr, hI]
    exact ⟨hstep.1, hext₁.trans hstep.2.1, hstep.2.2⟩

/-! ## Canonicity: index equality is expression equality -/

/-- Inversion of `denoteNode` at each `Expr` head constructor. -/
theorem denoteNode_bvar_inv {den : EIdx → Option Expr} {n : ENode} {k : Nat}
    (h : denoteNode den n = some (.bvar k)) : n = .bvar k := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_fvar_inv {den : EIdx → Option Expr} {n : ENode}
    {idx : Nat} {nm : Name} {ty : Expr}
    (h : denoteNode den n = some (.fvar idx nm ty)) :
    ∃ t, n = .fvar idx nm t ∧ den t = some ty := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_sort_inv {den : EIdx → Option Expr} {n : ENode} {u : Level}
    (h : denoteNode den n = some (.sort u)) : n = .sort u := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_const_inv {den : EIdx → Option Expr} {n : ENode}
    {nm : Name} {us : List Level}
    (h : denoteNode den n = some (.const nm us)) : n = .const nm us := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_app_inv {den : EIdx → Option Expr} {n : ENode} {x y : Expr}
    (h : denoteNode den n = some (.app x y)) :
    ∃ f a, n = .app f a ∧ den f = some x ∧ den a = some y := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_lam_inv {den : EIdx → Option Expr} {n : ENode}
    {nm : Name} {ty body : Expr} {m : BinderMeta}
    (h : denoteNode den n = some (.lam nm ty body m)) :
    ∃ t b, n = .lam nm t b m ∧ den t = some ty ∧ den b = some body := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_forallE_inv {den : EIdx → Option Expr} {n : ENode}
    {nm : Name} {ty body : Expr} {m : BinderMeta}
    (h : denoteNode den n = some (.forallE nm ty body m)) :
    ∃ t b, n = .forallE nm t b m ∧ den t = some ty ∧ den b = some body := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_letE_inv {den : EIdx → Option Expr} {n : ENode}
    {nm : Name} {ty val body : Expr}
    (h : denoteNode den n = some (.letE nm ty val body)) :
    ∃ t v b, n = .letE nm t v b ∧ den t = some ty ∧ den v = some val ∧
      den b = some body := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_lit_inv {den : EIdx → Option Expr} {n : ENode} {l : Literal}
    (h : denoteNode den n = some (.lit l)) : n = .lit l := by
  cases n <;> simp_all [denoteNode, Option.map_eq_some_iff, Option.bind_eq_some_iff] <;> grind

theorem denoteNode_proj_inv {den : EIdx → Option Expr} {n : ENode}
    {s : Name} {j : Nat} {x : Expr}
    (h : denoteNode den n = some (.proj s j x)) :
    ∃ e, n = .proj s j e ∧ den e = some x := by
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
    obtain rfl := denoteNode_sort_inv hdn
    obtain rfl := denoteNode_sort_inv hdm
    exact index_unique hwf hn hm
  | const nm us =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain rfl := denoteNode_const_inv hdn
    obtain rfl := denoteNode_const_inv hdm
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
    obtain ⟨t, rfl, ht⟩ := denoteNode_fvar_inv hdn
    obtain ⟨t', rfl, ht'⟩ := denoteNode_fvar_inv hdm
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
    obtain ⟨t, b, rfl, ht, hb⟩ := denoteNode_lam_inv hdn
    obtain ⟨t', b', rfl, ht', hb'⟩ := denoteNode_lam_inv hdm
    obtain rfl := ihty ht ht'
    obtain rfl := ihbody hb hb'
    exact index_unique hwf hn hm
  | forallE nm ty body m ihty ihbody =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m', hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨t, b, rfl, ht, hb⟩ := denoteNode_forallE_inv hdn
    obtain ⟨t', b', rfl, ht', hb'⟩ := denoteNode_forallE_inv hdm
    obtain rfl := ihty ht ht'
    obtain rfl := ihbody hb hb'
    exact index_unique hwf hn hm
  | letE nm ty val body ihty ihval ihbody =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨t, v, b, rfl, ht, hv, hb⟩ := denoteNode_letE_inv hdn
    obtain ⟨t', v', b', rfl, ht', hv', hb'⟩ := denoteNode_letE_inv hdm
    obtain rfl := ihty ht ht'
    obtain rfl := ihval hv hv'
    obtain rfl := ihbody hb hb'
    exact index_unique hwf hn hm
  | proj s k x ih =>
    intro i j hi hj
    obtain ⟨n, hn, -, hdn⟩ := denote_some_inv hi
    obtain ⟨m, hm, -, hdm⟩ := denote_some_inv hj
    obtain ⟨e, rfl, he⟩ := denoteNode_proj_inv hdn
    obtain ⟨e', rfl, he'⟩ := denoteNode_proj_inv hdm
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
    rw [denote_node hn hc]
    have hcs : ∀ c ∈ (st.nodes[i]).children, ∃ x, st.denote c = some x :=
      fun c hcin => ih c (hc c hcin)
        (Nat.lt_trans (hc c hcin) hi)
    cases hnn : st.nodes[i] with
    | bvar k => exact ⟨_, rfl⟩
    | sort u => exact ⟨_, rfl⟩
    | const nm us => exact ⟨_, rfl⟩
    | lit l => exact ⟨_, rfl⟩
    | fvar idx nm t =>
      obtain ⟨x, hx⟩ := hcs t (by simp [hnn, ENode.children])
      exact ⟨_, by rw [denoteNode, hx]; rfl⟩
    | app f a =>
      obtain ⟨xf, hf⟩ := hcs f (by simp [hnn, ENode.children])
      obtain ⟨xa, ha⟩ := hcs a (by simp [hnn, ENode.children])
      exact ⟨_, by rw [denoteNode, hf, ha]; rfl⟩
    | lam nm t b m =>
      obtain ⟨xt, ht⟩ := hcs t (by simp [hnn, ENode.children])
      obtain ⟨xb, hb⟩ := hcs b (by simp [hnn, ENode.children])
      exact ⟨_, by rw [denoteNode, ht, hb]; rfl⟩
    | forallE nm t b m =>
      obtain ⟨xt, ht⟩ := hcs t (by simp [hnn, ENode.children])
      obtain ⟨xb, hb⟩ := hcs b (by simp [hnn, ENode.children])
      exact ⟨_, by rw [denoteNode, ht, hb]; rfl⟩
    | letE nm t vv b =>
      obtain ⟨xt, ht⟩ := hcs t (by simp [hnn, ENode.children])
      obtain ⟨xv, hv⟩ := hcs vv (by simp [hnn, ENode.children])
      obtain ⟨xb, hb⟩ := hcs b (by simp [hnn, ENode.children])
      exact ⟨_, by rw [denoteNode, ht, hv, hb]; rfl⟩
    | proj s j e' =>
      obtain ⟨x, hx⟩ := hcs e' (by simp [hnn, ENode.children])
      exact ⟨_, by rw [denoteNode, hx]; rfl⟩

/-- Extension never shrinks the node table. -/
theorem Ext.size_le {st st' : EStore} (hext : Ext st st') :
    st.nodes.size ≤ st'.nodes.size := by
  by_cases h0 : st.nodes.size = 0
  · omega
  · have hlast : st.nodes[st.nodes.size - 1]? = some st.nodes[st.nodes.size - 1] := by
      simp
    have := hext _ _ hlast
    have := (Array.getElem?_eq_some_iff.mp this).1
    omega

/-- Below the old size, an extension does not change the node table. -/
theorem Ext.nodes_eq_of_lt {st st' : EStore} (hext : Ext st st') {j : EIdx}
    (hj : j < st.nodes.size) : st'.nodes[j]? = st.nodes[j]? := by
  have hn : st.nodes[j]? = some st.nodes[j] := by
    simp [hj]
  rw [hn]
  exact hext _ _ hn

/-- Below the old size, an extension does not change the denotation
(not even `none` ones — the guards in `denote` are index-based). -/
theorem Ext.denote_eq_of_lt {st st' : EStore} (hext : Ext st st') {j : EIdx}
    (hj : j < st.nodes.size) : st'.denote j = st.denote j :=
  denote_agree (fun _ hi => hext.nodes_eq_of_lt hi) j hj

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
    {memo : Std.HashMap (EIdx × Nat) EIdx} (hext : Ext st st')
    (h : MemoNInv st g memo) : MemoNInv st' g memo := by
  intro e c r hr
  obtain ⟨hlt, hcond⟩ := h e c r hr
  refine ⟨Nat.lt_of_lt_of_le hlt hext.size_le, ?_⟩
  intro x hx
  rw [hext.denote_eq_of_lt hlt] at hx
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
theorem cond_transport {st st' : EStore} (hext : Ext st st') {e r : EIdx}
    (hesz : e < st.nodes.size) {g : Expr → Expr}
    (hcond : ∀ x, st.denote e = some x → st'.denote r = some (g x)) :
    ∀ x, st'.denote e = some x → st'.denote r = some (g x) := by
  intro x hx
  rw [hext.denote_eq_of_lt hesz] at hx
  exact hcond x hx

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
                intern_wf hwf (by simp [ENode.children])
              have hextI : Ext st (st.intern (.bvar (i - 1))).2 := intern_ext _ _
              have hdI : (st.intern (.bvar (i - 1))).2.denote
                    (st.intern (.bvar (i - 1))).1
                  = denoteNode st.denote (.bvar (i - 1)) :=
                intern_denote hwf (by simp [ENode.children])
              rw [hI] at hwfI hextI hdI
              have hcond : ∀ x, st.denote e = some x →
                  sti.denote ri = some (x.instantiate1 w d) := by
                intro x hxx
                rw [hx] at hxx; cases hxx
                rw [hdI]
                simp [Expr.instantiate1, denoteNode, hne, hgt]
              refine ⟨hwfI, hextI, ?_, hcond⟩
              exact (hinv.mono hextI).insert
                (Nat.lt_of_lt_of_le hesz hextI.size_le)
                (cond_transport hextI hesz hcond)
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
          have hx : st.denote e = some (.fvar idx nm xt) := by
            rw [hde, denoteNode, hxt]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | sort u =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.sort u) := by rw [hde]; rfl
          have hcond : ∀ x, st.denote e = some x →
              st.denote e = some (x.instantiate1 w d) := by
            intro x hxx
            rw [hx] at hxx; cases hxx
            simpa [Expr.instantiate1] using hx
          exact ⟨hwf, Ext.refl st, hinv.insert hesz hcond, hcond⟩
        | const nm us =>
          dsimp only at hgo
          cases hgo
          have hx : st.denote e = some (.const nm us) := by rw [hde]; rfl
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
            have hwf₃ : (st₂.intern (.app f' a')).2.WF := intern_wf hwf₂ hcI
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
            exact (hinv₂.mono hext₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hesz hcond)
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
            have hx : st.denote e = some (.lam nm xt xb m) := by
              rw [hde, denoteNode, ht, hb]; rfl
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
            have hwf₃ : (st₂.intern (.lam nm ty' body' m)).2.WF := intern_wf hwf₂ hcI
            have hext₃ : Ext st₂ (st₂.intern (.lam nm ty' body' m)).2 := intern_ext _ _
            have hdI := intern_denote (n := .lam nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂]
              simp [Expr.instantiate1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hesz hcond)
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
            have hx : st.denote e = some (.forallE nm xt xb m) := by
              rw [hde, denoteNode, ht, hb]; rfl
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
            have hwf₃ : (st₂.intern (.forallE nm ty' body' m)).2.WF :=
              intern_wf hwf₂ hcI
            have hext₃ : Ext st₂ (st₂.intern (.forallE nm ty' body' m)).2 :=
              intern_ext _ _
            have hdI := intern_denote (n := .forallE nm ty' body' m) hwf₂ hcI
            rw [h₃] at hwf₃ hext₃ hdI
            have hextAll : Ext st st₃ := hext₁.trans (hext₂.trans hext₃)
            have hcond : ∀ x, st.denote e = some x →
                st₃.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, ht₂, hb₂]
              simp [Expr.instantiate1]
            refine ⟨hwf₃, hextAll, ?_, hcond⟩
            exact (hinv₂.mono hext₃).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hesz hcond)
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
            have hx : st.denote e = some (.letE nm xt xv xb) := by
              rw [hde, denoteNode, ht, hvv, hb]; rfl
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
              intern_wf hwf₃ hcI
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
              rw [hdI, denoteNode, ht₃, hvv₃, hb₃]
              simp [Expr.instantiate1]
            refine ⟨hwf₄, hextAll, ?_, hcond⟩
            exact (hinv₃.mono hext₄).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hesz hcond)
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
            have hx : st.denote e = some (.proj s j xs) := by
              rw [hde, denoteNode, hs]; rfl
            obtain ⟨hwf₁, hext₁, hinv₁, hden₁⟩ := ih sub hguard hwf hv hinv h₁
            have hs₁ : st₁.denote sub' = some (xs.instantiate1 w d) := hden₁ xs hs
            have hcI : ∀ c ∈ (ENode.proj s j sub').children,
                c < st₁.nodes.size := by
              simpa [ENode.children] using denote_lt_size hs₁
            have hwf₂ : (st₁.intern (.proj s j sub')).2.WF := intern_wf hwf₁ hcI
            have hext₂ : Ext st₁ (st₁.intern (.proj s j sub')).2 := intern_ext _ _
            have hdI := intern_denote (n := .proj s j sub') hwf₁ hcI
            rw [h₂] at hwf₂ hext₂ hdI
            have hextAll : Ext st st₂ := hext₁.trans hext₂
            have hcond : ∀ x, st.denote e = some x →
                st₂.denote ri = some (x.instantiate1 w d) := by
              intro x hxx
              rw [hx] at hxx; cases hxx
              rw [hdI, denoteNode, hs₁]
              simp [Expr.instantiate1]
            refine ⟨hwf₂, hextAll, ?_, hcond⟩
            exact (hinv₁.mono hext₂).insert
              (Nat.lt_of_lt_of_le hesz hextAll.size_le)
              (cond_transport hextAll hesz hcond)

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

end EStore

end Setlec
