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
* [ ] `instantiate1I` commutes with `denote`
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

end EStore

end Setlec
