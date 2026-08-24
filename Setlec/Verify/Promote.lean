import Setlec.Kernel.Promote
import Setlec.Kernel.ArenaWF

/-!
# Snapshot promotion preserves denotation (task #64)

`EStore.promoteE` re-interns the sub-DAG of a snapshot's stored
tier-two output into the retained flag-off store.  This module proves
the promotion faithful: the promoted index denotes, in the extended
retained store, exactly the tier-aware denotation the index had in the
snapshot store.

The theorems are stated against an abstract retained store `st0`
related to the snapshot store `stP` by the harvest-time facts (in
practice `st0 = stP.truncateTierTwo`): `stP.TWF`, `st0.WF`, and
transport of the snapshot's tier-one/level/name denotations into the
retained store — hypotheses the truncation identity lemmas discharge
downstream.  Level and name indices referenced by tier-two nodes are
below the harvest-time table sizes (`TWF.t_levels_lt` /
`TWF.t_names_lt`), so `promoteLGo` / `promoteNGo` are identities on
them; only the expression walk does real work.
-/

namespace Setlec

open EStore

/-! ## Level, name and binder-meta promotion below the base is the
identity

`promoteLGo` / `promoteNGo` test the base bound before anything else,
so shared (below-base) indices come back unchanged with the store and
memo untouched — regardless of the harvest tables and the memo
contents. -/

theorem promoteLGo_lt {h : Harvest} {lbase : Nat} {st : EStore}
    {memo : Std.HashMap LIdx LIdx} {u : LIdx} (hu : u < lbase) :
    promoteLGo h lbase st memo u = (u, st, memo) := by
  rw [promoteLGo.eq_def, if_pos hu]

theorem promoteNGo_lt {h : Harvest} {nbase : Nat} {st : EStore}
    {memo : Std.HashMap NIdx NIdx} {q : NIdx} (hq : q < nbase) :
    promoteNGo h nbase st memo q = (q, st, memo) := by
  rw [promoteNGo.eq_def, if_pos hq]

theorem PromoteSt.level_lt {p : PromoteSt} {h : Harvest} {lbase : Nat}
    {u : LIdx} (hu : u < lbase) : p.level h lbase u = (u, p) := by
  obtain ⟨st, mE, mL, mN⟩ := p
  simp [PromoteSt.level, promoteLGo_lt hu]

theorem PromoteSt.name_lt {p : PromoteSt} {h : Harvest} {nbase : Nat}
    {q : NIdx} (hq : q < nbase) : p.name h nbase q = (q, p) := by
  obtain ⟨st, mE, mL, mN⟩ := p
  simp [PromoteSt.name, promoteNGo_lt hq]

theorem PromoteSt.levels_lt {h : Harvest} {lbase : Nat} :
    ∀ {us : List LIdx} {p : PromoteSt}, (∀ u ∈ us, u < lbase) →
      p.levels h lbase us = (us, p) := by
  intro us
  induction us with
  | nil => intro p _; rfl
  | cons u us ih =>
    intro p hus
    have hrec : PromoteSt.levels p h lbase us = (us, p) :=
      ih fun v hv => hus v (by simp [hv])
    simp only [PromoteSt.levels, List.foldr_cons] at hrec ⊢
    rw [hrec, PromoteSt.level_lt (hus u (by simp))]

theorem PromoteSt.bm_lt {p : PromoteSt} {h : Harvest} {lbase : Nat}
    {m : IBinderMeta} (hm : ∀ u ∈ m.cod.toList, u < lbase) :
    p.bm h lbase m = (m, p) := by
  obtain ⟨bi, (_ | u)⟩ := m
  · rfl
  · simp [PromoteSt.bm, PromoteSt.level_lt (hm u (by simp))]

/-! ## Denotation-transport helpers

The snapshot-to-retained leg of the level/name transports is
element-wise (`hlden` / `hnden` below), so the list and binder-meta
denotations need the element-wise congruence forms (the `Ext`-based
`_mono` lemmas cover the retained-to-current leg). -/

theorem denoteLList_transport {d₁ d₂ : LIdx → Option Level}
    (h : ∀ u l, d₁ u = some l → d₂ u = some l) :
    ∀ {us : List LIdx} {ls : List Level},
      denoteLList d₁ us = some ls → denoteLList d₂ us = some ls := by
  intro us
  induction us with
  | nil => intro ls hls; exact hls
  | cons u us ih =>
    intro ls hls
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at hls ⊢
    obtain ⟨l, hl, ls', hls', rfl⟩ := hls
    exact ⟨l, h u l hl, ls', ih hls', rfl⟩

theorem denoteBM_transport {d₁ d₂ : LIdx → Option Level}
    (h : ∀ u l, d₁ u = some l → d₂ u = some l) {m : IBinderMeta}
    {bm : BinderMeta} (hm : denoteBM d₁ m = some bm) :
    denoteBM d₂ m = some bm := by
  obtain ⟨bi, (_ | u)⟩ := m
  · exact hm
  · simp only [denoteBM, Option.map_eq_some_iff] at hm ⊢
    obtain ⟨l, hl, rfl⟩ := hm
    exact ⟨l, h u l hl, rfl⟩

/-! ## Level/name reference bounds from a successful denotation

`intern_wf` wants the interned node's level and name references in
range; a component-wise denotation certifies exactly that. -/

theorem denoteLList_lt_size {st : EStore} :
    ∀ {us : List LIdx} {ls : List Level},
      denoteLList st.denoteL us = some ls →
      ∀ u ∈ us, u < st.lnodes.size := by
  intro us
  induction us with
  | nil => intro ls _ u hu; simp at hu
  | cons v us ih =>
    intro ls h u hu
    simp only [denoteLList, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨l, hl, ls', hls', rfl⟩ := h
    rcases List.mem_cons.mp hu with rfl | hu'
    · exact denoteL_lt_size hl
    · exact ih hls' u hu'

theorem denoteBM_lt_size {st : EStore} {m : IBinderMeta}
    {bm : BinderMeta} (h : denoteBM st.denoteL m = some bm) :
    ∀ u ∈ m.cod.toList, u < st.lnodes.size := by
  obtain ⟨bi, (_ | u)⟩ := m
  · simp
  · simp only [denoteBM, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, -⟩ := h
    simpa using denoteL_lt_size hl

/-- A denoted node's level references are in range. -/
theorem denoteNode_levels_lt {st : EStore} {den : EIdx → Option Expr}
    {denN : NIdx → Option Name} {n : ENode} {a : Expr}
    (h : denoteNode den st.denoteL denN n = some a) :
    ∀ u ∈ n.levels, u < st.lnodes.size := by
  cases n with
  | sort u =>
    simp only [denoteNode, Option.map_eq_some_iff] at h
    obtain ⟨l, hl, -⟩ := h
    simpa [ENode.levels] using denoteL_lt_size hl
  | const nm us =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨ls, hls, -⟩ := h
    simpa [ENode.levels] using denoteLList_lt_size hls
  | lam nm t b m =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨xt, -, xb, -, bm, hbm, -⟩ := h
    simpa [ENode.levels] using denoteBM_lt_size hbm
  | forallE nm t b m =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨xt, -, xb, -, bm, hbm, -⟩ := h
    simpa [ENode.levels] using denoteBM_lt_size hbm
  | bvar i => simp [ENode.levels]
  | fvar idx nm t => simp [ENode.levels]
  | app f a' => simp [ENode.levels]
  | letE nm t v b => simp [ENode.levels]
  | lit l => simp [ENode.levels]
  | proj s j e => simp [ENode.levels]

/-- A denoted node's name references are in range. -/
theorem denoteNode_names_lt {st : EStore} {den : EIdx → Option Expr}
    {denL : LIdx → Option Level} {n : ENode} {a : Expr}
    (h : denoteNode den denL st.denoteN n = some a) :
    ∀ q ∈ n.names, q < st.nnodes.size := by
  cases n with
  | fvar idx nm t =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨xt, -, name, hname, -⟩ := h
    simpa [ENode.names] using denoteN_lt_size hname
  | const nm us =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨ls, -, name, hname, -⟩ := h
    simpa [ENode.names] using denoteN_lt_size hname
  | lam nm t b m =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨xt, -, xb, -, bm, -, name, hname, -⟩ := h
    simpa [ENode.names] using denoteN_lt_size hname
  | forallE nm t b m =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨xt, -, xb, -, bm, -, name, hname, -⟩ := h
    simpa [ENode.names] using denoteN_lt_size hname
  | letE nm t v b =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨xt, -, xv, -, xb, -, name, hname, -⟩ := h
    simpa [ENode.names] using denoteN_lt_size hname
  | proj s j e =>
    simp only [denoteNode, Option.bind_eq_some_iff,
      Option.map_eq_some_iff] at h
    obtain ⟨x, -, name, hname, -⟩ := h
    simpa [ENode.names] using denoteN_lt_size hname
  | bvar i => simp [ENode.names]
  | sort u => simp [ENode.names]
  | app f a' => simp [ENode.names]
  | lit l => simp [ENode.names]

/-! ## The promotion invariant and the `promoteEGo` step pieces -/

/-- The state invariant of the expression-promotion walk: the working
store is well-formed and extends the retained store, and every memo
entry's target denotes what the memoized snapshot position denotes
tier-aware. -/
def PromoteInv (stP st0 : EStore) (p : PromoteSt) : Prop :=
  p.st.WF ∧ Ext st0 p.st ∧
    ∀ (j : Nat) (r : EIdx), p.memoE[j]? = some r →
      ∀ w, stP.denoteT (j + j + 1) = some w → p.st.denote r = some w

/-- The child promotion step of `promoteEGo` (the local `sub`), lifted
to a top-level definition so the per-constructor unfolding lemmas can
speak about it. -/
def promoteSub (h : Harvest) (lbase nbase j : Nat) (p : PromoteSt)
    (c : EIdx) : EIdx × PromoteSt :=
  if etier c = 0 then (c, p)
  else if _h : epos c < j then promoteEGo h lbase nbase p (epos c)
  else (c, p)

/-- The intern-and-memoize tail of `promoteEGo`. -/
def promoteFin (p : PromoteSt) (j : Nat) (n' : ENode) :
    EIdx × PromoteSt :=
  ((p.st.intern n').1,
    ⟨(p.st.intern n').2, p.memoE.insert j (p.st.intern n').1,
      p.memoL, p.memoN⟩)

/-! ### Per-case unfolding of `promoteEGo`

Each lemma restates one branch of `promoteEGo`'s big match as a
composition of `promoteSub`, the identity-checked level/name
promotions, and `promoteFin` — definitional equalities (structure and
pair eta), packaged so the main induction can rewrite the walk without
fighting the destructuring lets. -/

section Unfold

variable {h : Harvest} {lbase nbase : Nat} {p : PromoteSt} {j : Nat}

theorem promoteEGo_memo {r : EIdx} (hm : p.memoE[j]? = some r) :
    promoteEGo h lbase nbase p j = (r, p) := by
  rw [promoteEGo.eq_def, hm]

theorem promoteEGo_none (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = none) :
    promoteEGo h lbase nbase p j = (j + j + 1, p) := by
  rw [promoteEGo.eq_def, hm, ht]

theorem promoteEGo_bvar {i : Nat} (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.bvar i)) :
    promoteEGo h lbase nbase p j = promoteFin p j (.bvar i) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_lit {l : Literal} (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.lit l)) :
    promoteEGo h lbase nbase p j = promoteFin p j (.lit l) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_sort {u : LIdx} (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.sort u)) :
    promoteEGo h lbase nbase p j =
      promoteFin (p.level h lbase u).2 j
        (.sort (p.level h lbase u).1) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_const {nm : NIdx} {us : List LIdx}
    (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.const nm us)) :
    promoteEGo h lbase nbase p j =
      promoteFin ((p.levels h lbase us).2.name h nbase nm).2 j
        (.const ((p.levels h lbase us).2.name h nbase nm).1
          (p.levels h lbase us).1) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_fvar {idx : Nat} {nm : NIdx} {t : EIdx}
    (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.fvar idx nm t)) :
    promoteEGo h lbase nbase p j =
      promoteFin
        ((promoteSub h lbase nbase j p t).2.name h nbase nm).2 j
        (.fvar idx
          ((promoteSub h lbase nbase j p t).2.name h nbase nm).1
          (promoteSub h lbase nbase j p t).1) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_app {f a : EIdx} (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.app f a)) :
    promoteEGo h lbase nbase p j =
      promoteFin
        (promoteSub h lbase nbase j
          (promoteSub h lbase nbase j p f).2 a).2 j
        (.app (promoteSub h lbase nbase j p f).1
          (promoteSub h lbase nbase j
            (promoteSub h lbase nbase j p f).2 a).1) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_lam {nm : NIdx} {t b : EIdx} {m : IBinderMeta}
    (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.lam nm t b m)) :
    promoteEGo h lbase nbase p j =
      promoteFin
        ((((promoteSub h lbase nbase j
              (promoteSub h lbase nbase j p t).2 b).2.bm h lbase
            m).2.name h nbase nm).2) j
        (.lam
          ((((promoteSub h lbase nbase j
                (promoteSub h lbase nbase j p t).2 b).2.bm h lbase
              m).2.name h nbase nm).1)
          (promoteSub h lbase nbase j p t).1
          (promoteSub h lbase nbase j
            (promoteSub h lbase nbase j p t).2 b).1
          (((promoteSub h lbase nbase j
              (promoteSub h lbase nbase j p t).2 b).2.bm h lbase
            m).1)) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_forallE {nm : NIdx} {t b : EIdx} {m : IBinderMeta}
    (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.forallE nm t b m)) :
    promoteEGo h lbase nbase p j =
      promoteFin
        ((((promoteSub h lbase nbase j
              (promoteSub h lbase nbase j p t).2 b).2.bm h lbase
            m).2.name h nbase nm).2) j
        (.forallE
          ((((promoteSub h lbase nbase j
                (promoteSub h lbase nbase j p t).2 b).2.bm h lbase
              m).2.name h nbase nm).1)
          (promoteSub h lbase nbase j p t).1
          (promoteSub h lbase nbase j
            (promoteSub h lbase nbase j p t).2 b).1
          (((promoteSub h lbase nbase j
              (promoteSub h lbase nbase j p t).2 b).2.bm h lbase
            m).1)) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_letE {nm : NIdx} {t v b : EIdx}
    (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.letE nm t v b)) :
    promoteEGo h lbase nbase p j =
      promoteFin
        (((promoteSub h lbase nbase j
            (promoteSub h lbase nbase j
              (promoteSub h lbase nbase j p t).2 v).2 b).2.name
          h nbase nm).2) j
        (.letE
          (((promoteSub h lbase nbase j
              (promoteSub h lbase nbase j
                (promoteSub h lbase nbase j p t).2 v).2 b).2.name
            h nbase nm).1)
          (promoteSub h lbase nbase j p t).1
          (promoteSub h lbase nbase j
            (promoteSub h lbase nbase j p t).2 v).1
          (promoteSub h lbase nbase j
            (promoteSub h lbase nbase j
              (promoteSub h lbase nbase j p t).2 v).2 b).1) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

theorem promoteEGo_proj {s : NIdx} {i : Nat} {e : EIdx}
    (hm : p.memoE[j]? = none)
    (ht : h.tnodes[j]? = some (.proj s i e)) :
    promoteEGo h lbase nbase p j =
      promoteFin
        ((promoteSub h lbase nbase j p e).2.name h nbase s).2 j
        (.proj
          ((promoteSub h lbase nbase j p e).2.name h nbase s).1 i
          (promoteSub h lbase nbase j p e).1) := by
  rw [promoteEGo.eq_def, hm, ht]
  rfl

end Unfold

/-! ## The step specifications -/

/-- The intern-and-memoize tail preserves the invariant, extends the
working store, and its result denotes the assembled node's denotation
(the memo entry it adds is justified by `hjw`: the snapshot position
`j` can only denote the value being stored). -/
theorem promoteFin_spec {stP st0 : EStore} {p : PromoteSt}
    (hp : PromoteInv stP st0 p) {j : Nat} {n' : ENode} {w : Expr}
    (hd : denoteNode p.st.denote p.st.denoteL p.st.denoteN n' = some w)
    (hjw : ∀ w', stP.denoteT (j + j + 1) = some w' → w' = w) :
    PromoteInv stP st0 (promoteFin p j n').2 ∧
      Ext p.st (promoteFin p j n').2.st ∧
      (promoteFin p j n').2.st.denote (promoteFin p j n').1 = some w := by
  obtain ⟨hwf, hext0, hmemo⟩ := hp
  have hc : ∀ c ∈ n'.children, p.st.Valid1 c := by
    intro c hcin
    obtain ⟨b, hb⟩ := denoteNode_children_some hd c hcin
    exact denote_valid1 hb
  have hwf' := intern_wf hwf hc (denoteNode_levels_lt hd)
    (denoteNode_names_lt hd)
  have hextI := intern_ext p.st n'
  have hden' : (p.st.intern n').2.denote (p.st.intern n').1 = some w := by
    rw [intern_denote hwf hc]
    exact hd
  refine ⟨⟨hwf', hext0.trans hextI, ?_⟩, hextI, hden'⟩
  intro j₂ r₂ hr₂ w₂ hw₂
  simp only [promoteFin] at hr₂
  rw [Std.HashMap.getElem?_insert] at hr₂
  by_cases hk : j == j₂
  · rw [if_pos hk] at hr₂
    cases hr₂
    have hjj : j = j₂ := eq_of_beq hk
    subst hjj
    rw [hjw w₂ hw₂]
    exact hden'
  · rw [if_neg hk] at hr₂
    exact denote_mono hextI (hmemo j₂ r₂ hr₂ w₂ hw₂)

/-- The child promotion step: an even (tier-one) child is kept and its
snapshot denotation transports through the retained store; an odd
child recurses (the induction hypothesis `ih` is `promoteEGo`'s
specification below position `j`). -/
theorem promoteSub_spec {stP st0 : EStore} (hpre : stP.TWF)
    (hden1 : ∀ i w, stP.denote i = some w → st0.denote i = some w)
    {H : Harvest} {lbase nbase j : Nat}
    (ih : ∀ m, m < j → ∀ p : PromoteSt, PromoteInv stP st0 p →
      ∀ w, stP.denoteT (m + m + 1) = some w →
        PromoteInv stP st0 (promoteEGo H lbase nbase p m).2 ∧
          Ext p.st (promoteEGo H lbase nbase p m).2.st ∧
          (promoteEGo H lbase nbase p m).2.st.denote
            (promoteEGo H lbase nbase p m).1 = some w)
    {p : PromoteSt} (hp : PromoteInv stP st0 p) {c : EIdx}
    (hc : stP.Valid1 c ∨ (etier c = 1 ∧ epos c < j))
    {x : Expr} (hx : stP.denoteT c = some x) :
    PromoteInv stP st0 (promoteSub H lbase nbase j p c).2 ∧
      Ext p.st (promoteSub H lbase nbase j p c).2.st ∧
      (promoteSub H lbase nbase j p c).2.st.denote
        (promoteSub H lbase nbase j p c).1 = some x := by
  rcases etier_cases c with ht | ht
  · simp only [promoteSub]
    rw [if_pos ht]
    exact ⟨hp, Ext.refl _,
      denote_mono hp.2.1 (hden1 c x (denote_of_denoteT_even hpre ht hx))⟩
  · rcases hc with ⟨ht0, -⟩ | ⟨-, hcj⟩
    · omega
    · simp only [promoteSub]
      rw [if_neg (by omega), dif_pos hcj]
      exact ih (epos c) hcj p hp x (by rwa [odd_encode ht])

/-- Prepend an earlier extension to a step's conclusions (the shape
every multi-child case of the main induction ends in). -/
private theorem promote_step {stP st0 : EStore} {p q : PromoteSt}
    {res : EIdx × PromoteSt} {w : Expr} (hext : Ext p.st q.st)
    (h : PromoteInv stP st0 res.2 ∧ Ext q.st res.2.st ∧
      res.2.st.denote res.1 = some w) :
    PromoteInv stP st0 res.2 ∧ Ext p.st res.2.st ∧
      res.2.st.denote res.1 = some w :=
  ⟨h.1, hext.trans h.2.1, h.2.2⟩

/-! ## The main induction -/

/-- `promoteEGo` preserves the promotion invariant, extends the
working store, and its result denotes what the promoted snapshot
position denotes tier-aware.  Stated against an abstract harvest `H`
carrying the snapshot's tier-two node table, with the level/name bases
at least the snapshot table sizes (in practice equal: the level/name
tables never shrink under the flag). -/
theorem promoteEGo_spec {stP st0 : EStore} (hpre : stP.TWF)
    (hden1 : ∀ i w, stP.denote i = some w → st0.denote i = some w)
    (hlden : ∀ u l, stP.denoteL u = some l → st0.denoteL u = some l)
    (hnden : ∀ q nm, stP.denoteN q = some nm → st0.denoteN q = some nm)
    {H : Harvest} (hH : H.tnodes = stP.tnodes) {lbase nbase : Nat}
    (hlb : stP.lnodes.size ≤ lbase) (hnb : stP.nnodes.size ≤ nbase) :
    ∀ (j : Nat) (p : PromoteSt), PromoteInv stP st0 p →
      ∀ w, stP.denoteT (j + j + 1) = some w →
        PromoteInv stP st0 (promoteEGo H lbase nbase p j).2 ∧
          Ext p.st (promoteEGo H lbase nbase p j).2.st ∧
          (promoteEGo H lbase nbase p j).2.st.denote
            (promoteEGo H lbase nbase p j).1 = some w := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro p hp w hw
    cases hm : p.memoE[j]? with
    | some r =>
      rw [promoteEGo_memo hm]
      exact ⟨hp, Ext.refl _, hp.2.2 j r hm w hw⟩
    | none =>
      obtain ⟨n, hgn, -, hdn⟩ := denoteT_some_inv hw
      have heq : stP.tnodes[j]? = some n := by
        rcases getNode_eq_some.mp hgn with ⟨ht, -⟩ | ⟨-, hj⟩
        · simp at ht
        · simpa using hj
      have hH' : H.tnodes[j]? = some n := by rw [hH]; exact heq
      have hchild := hpre.t_children_lt j n heq
      have hlvl := hpre.t_levels_lt j n heq
      have hnms := hpre.t_names_lt j n heq
      have hjw : ∀ w', stP.denoteT (j + j + 1) = some w' → w' = w :=
        fun w' hw' => (Option.some.inj (hw.symm.trans hw')).symm
      cases n with
      | bvar i =>
        rw [promoteEGo_bvar hm hH']
        simp only [denoteNode] at hdn
        cases hdn
        refine promoteFin_spec hp ?_ hjw
        simp [denoteNode]
      | lit l =>
        rw [promoteEGo_lit hm hH']
        simp only [denoteNode] at hdn
        cases hdn
        refine promoteFin_spec hp ?_ hjw
        simp [denoteNode]
      | sort u =>
        simp only [denoteNode, Option.map_eq_some_iff] at hdn
        obtain ⟨l, hlu, rfl⟩ := hdn
        rw [promoteEGo_sort hm hH', PromoteSt.level_lt
          (Nat.lt_of_lt_of_le (hlvl u (by simp [ENode.levels])) hlb)]
        have hlp : p.st.denoteL u = some l :=
          denoteL_mono hp.2.1 (hlden u l hlu)
        refine promoteFin_spec hp ?_ hjw
        simp [denoteNode, hlp]
      | const nm us =>
        simp only [denoteNode, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hdn
        obtain ⟨ls, hls, name, hname, rfl⟩ := hdn
        rw [promoteEGo_const hm hH', PromoteSt.levels_lt
          (fun u hu => Nat.lt_of_lt_of_le
            (hlvl u (by simpa [ENode.levels] using hu)) hlb),
          PromoteSt.name_lt
            (Nat.lt_of_lt_of_le (hnms nm (by simp [ENode.names])) hnb)]
        have hlsp : denoteLList p.st.denoteL us = some ls :=
          denoteLList_mono hp.2.1 (denoteLList_transport hlden hls)
        have hnmp : p.st.denoteN nm = some name :=
          denoteN_mono hp.2.1 (hnden nm name hname)
        refine promoteFin_spec hp ?_ hjw
        simp [denoteNode, hlsp, hnmp]
      | fvar idx nm t =>
        simp only [denoteNode, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hdn
        obtain ⟨xt, hxt, name, hname, rfl⟩ := hdn
        rw [promoteEGo_fvar hm hH']
        obtain ⟨hp₁, hext₁, hden₁⟩ := promoteSub_spec hpre hden1 ih hp
          (hchild t (by simp [ENode.children])) hxt
        rw [PromoteSt.name_lt
          (Nat.lt_of_lt_of_le (hnms nm (by simp [ENode.names])) hnb)]
        have hnmp := denoteN_mono hp₁.2.1 (hnden nm name hname)
        refine promote_step hext₁ (promoteFin_spec hp₁ ?_ hjw)
        simp [denoteNode, hden₁, hnmp]
      | app f a =>
        simp only [denoteNode, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hdn
        obtain ⟨xf, hxf, xa, hxa, rfl⟩ := hdn
        rw [promoteEGo_app hm hH']
        obtain ⟨hp₁, hext₁, hden₁⟩ := promoteSub_spec hpre hden1 ih hp
          (hchild f (by simp [ENode.children])) hxf
        obtain ⟨hp₂, hext₂, hden₂⟩ := promoteSub_spec hpre hden1 ih hp₁
          (hchild a (by simp [ENode.children])) hxa
        have hdf := denote_mono hext₂ hden₁
        refine promote_step (hext₁.trans hext₂) (promoteFin_spec hp₂ ?_ hjw)
        simp [denoteNode, hdf, hden₂]
      | lam nm t b m =>
        simp only [denoteNode, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hdn
        obtain ⟨xt, hxt, xb, hxb, bm, hbm, name, hname, rfl⟩ := hdn
        rw [promoteEGo_lam hm hH']
        obtain ⟨hp₁, hext₁, hden₁⟩ := promoteSub_spec hpre hden1 ih hp
          (hchild t (by simp [ENode.children])) hxt
        obtain ⟨hp₂, hext₂, hden₂⟩ := promoteSub_spec hpre hden1 ih hp₁
          (hchild b (by simp [ENode.children])) hxb
        rw [PromoteSt.bm_lt
          (fun u hu => Nat.lt_of_lt_of_le
            (hlvl u (by simpa [ENode.levels] using hu)) hlb),
          PromoteSt.name_lt
            (Nat.lt_of_lt_of_le (hnms nm (by simp [ENode.names])) hnb)]
        have hdf := denote_mono hext₂ hden₁
        have hbmp : denoteBM (promoteSub H lbase nbase j
              (promoteSub H lbase nbase j p t).2 b).2.st.denoteL m
            = some bm :=
          denoteBM_mono hp₂.2.1 (denoteBM_transport hlden hbm)
        have hnmp := denoteN_mono hp₂.2.1 (hnden nm name hname)
        refine promote_step (hext₁.trans hext₂) (promoteFin_spec hp₂ ?_ hjw)
        simp [denoteNode, hdf, hden₂, hbmp, hnmp]
      | forallE nm t b m =>
        simp only [denoteNode, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hdn
        obtain ⟨xt, hxt, xb, hxb, bm, hbm, name, hname, rfl⟩ := hdn
        rw [promoteEGo_forallE hm hH']
        obtain ⟨hp₁, hext₁, hden₁⟩ := promoteSub_spec hpre hden1 ih hp
          (hchild t (by simp [ENode.children])) hxt
        obtain ⟨hp₂, hext₂, hden₂⟩ := promoteSub_spec hpre hden1 ih hp₁
          (hchild b (by simp [ENode.children])) hxb
        rw [PromoteSt.bm_lt
          (fun u hu => Nat.lt_of_lt_of_le
            (hlvl u (by simpa [ENode.levels] using hu)) hlb),
          PromoteSt.name_lt
            (Nat.lt_of_lt_of_le (hnms nm (by simp [ENode.names])) hnb)]
        have hdf := denote_mono hext₂ hden₁
        have hbmp : denoteBM (promoteSub H lbase nbase j
              (promoteSub H lbase nbase j p t).2 b).2.st.denoteL m
            = some bm :=
          denoteBM_mono hp₂.2.1 (denoteBM_transport hlden hbm)
        have hnmp := denoteN_mono hp₂.2.1 (hnden nm name hname)
        refine promote_step (hext₁.trans hext₂) (promoteFin_spec hp₂ ?_ hjw)
        simp [denoteNode, hdf, hden₂, hbmp, hnmp]
      | letE nm t v b =>
        simp only [denoteNode, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hdn
        obtain ⟨xt, hxt, xv, hxv, xb, hxb, name, hname, rfl⟩ := hdn
        rw [promoteEGo_letE hm hH']
        obtain ⟨hp₁, hext₁, hden₁⟩ := promoteSub_spec hpre hden1 ih hp
          (hchild t (by simp [ENode.children])) hxt
        obtain ⟨hp₂, hext₂, hden₂⟩ := promoteSub_spec hpre hden1 ih hp₁
          (hchild v (by simp [ENode.children])) hxv
        obtain ⟨hp₃, hext₃, hden₃⟩ := promoteSub_spec hpre hden1 ih hp₂
          (hchild b (by simp [ENode.children])) hxb
        rw [PromoteSt.name_lt
          (Nat.lt_of_lt_of_le (hnms nm (by simp [ENode.names])) hnb)]
        have hdt := denote_mono hext₃ (denote_mono hext₂ hden₁)
        have hdv := denote_mono hext₃ hden₂
        have hnmp := denoteN_mono hp₃.2.1 (hnden nm name hname)
        refine promote_step ((hext₁.trans hext₂).trans hext₃)
          (promoteFin_spec hp₃ ?_ hjw)
        simp [denoteNode, hdt, hdv, hden₃, hnmp]
      | proj s i e =>
        simp only [denoteNode, Option.bind_eq_some_iff,
          Option.map_eq_some_iff] at hdn
        obtain ⟨x, hx, name, hname, rfl⟩ := hdn
        rw [promoteEGo_proj hm hH']
        obtain ⟨hp₁, hext₁, hden₁⟩ := promoteSub_spec hpre hden1 ih hp
          (hchild e (by simp [ENode.children])) hx
        rw [PromoteSt.name_lt
          (Nat.lt_of_lt_of_le (hnms s (by simp [ENode.names])) hnb)]
        have hnmp := denoteN_mono hp₁.2.1 (hnden s name hname)
        refine promote_step hext₁ (promoteFin_spec hp₁ ?_ hjw)
        simp [denoteNode, hden₁, hnmp]

/-! ## The interface theorem -/

/-- Snapshot promotion preserves denotation: promoting a snapshot
index whose tier-aware denotation is `w` into the retained store
yields a well-formed extension of the retained store in which the
promoted index denotes `w`.  With `st0 := stP.truncateTierTwo` the
transport hypotheses are the truncation identity lemmas. -/
theorem promoteE_spec {stP st0 : EStore} (hpre : stP.TWF) (hwf0 : st0.WF)
    (hden1 : ∀ i w, stP.denote i = some w → st0.denote i = some w)
    (hlden : ∀ u l, stP.denoteL u = some l → st0.denoteL u = some l)
    (hnden : ∀ q nm, stP.denoteN q = some nm → st0.denoteN q = some nm)
    {hl : Array LNode} {hn : Array NNode} {e : EIdx} {w : Expr}
    (hw : stP.denoteT e = some w) :
    (st0.promoteE ⟨stP.tnodes, hl, hn⟩ stP.lnodes.size
        stP.nnodes.size e).2.WF ∧
      Ext st0 (st0.promoteE ⟨stP.tnodes, hl, hn⟩ stP.lnodes.size
        stP.nnodes.size e).2 ∧
      (st0.promoteE ⟨stP.tnodes, hl, hn⟩ stP.lnodes.size
          stP.nnodes.size e).2.denote
        (st0.promoteE ⟨stP.tnodes, hl, hn⟩ stP.lnodes.size
          stP.nnodes.size e).1 = some w := by
  rcases etier_cases e with ht | ht
  · have hE : st0.promoteE ⟨stP.tnodes, hl, hn⟩ stP.lnodes.size
        stP.nnodes.size e = (e, st0) := by
      unfold EStore.promoteE
      rw [if_pos ht]
    rw [hE]
    exact ⟨hwf0, Ext.refl st0,
      hden1 e w (denote_of_denoteT_even hpre ht hw)⟩
  · have h0 : PromoteInv stP st0 ⟨st0, {}, {}, {}⟩ :=
      ⟨hwf0, Ext.refl st0, fun j r hr => by simp at hr⟩
    have hspec := promoteEGo_spec hpre hden1 hlden hnden
      (H := ⟨stP.tnodes, hl, hn⟩) rfl (Nat.le_refl _) (Nat.le_refl _)
      (epos e) ⟨st0, {}, {}, {}⟩ h0 w (by rwa [odd_encode ht])
    have hE : st0.promoteE ⟨stP.tnodes, hl, hn⟩ stP.lnodes.size
        stP.nnodes.size e =
        ((promoteEGo ⟨stP.tnodes, hl, hn⟩ stP.lnodes.size
            stP.nnodes.size ⟨st0, {}, {}, {}⟩ (epos e)).1,
          (promoteEGo ⟨stP.tnodes, hl, hn⟩ stP.lnodes.size
            stP.nnodes.size ⟨st0, {}, {}, {}⟩ (epos e)).2.st) := by
      unfold EStore.promoteE
      rw [if_neg (by omega)]
    rw [hE]
    exact ⟨hspec.1.1, hspec.1.2.1, hspec.2.2⟩

end Setlec
