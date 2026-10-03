module

public import Fragment.Univ

@[expose] public section

/-!
# The library for inductive types

What the environment section uses of set theory beyond the universes
(`Lib.lean`, `Univ.lean`), again as laws only: **n-ary tuples**
(injective, universe-closed) and **tagged values** (injective,
universe-closed, never the point).  A constructor application denotes
a tagged tuple — the constructor's number, then its fields.  The
operations are abstract, so their closure laws cannot be derived from
the universe laws and stay laws.

**Nothing here is about size.**  That a fibre of an inductive family
is a *member* of the universe — a type, not a proper class — is the
strength of the universes, and it is a theorem: the block's operator
is accessible, an accessible operator has a closed family in the
universe (`closed_of_acc`, `Access.lean`), and the family is the least
fixed point inside the set theory (`lfpFamSet`, `LfpSet.lean`).

**Least fixed points on predicates** (`Lfp`, below) are kept for one
consumer: the **recursion theorem** (`IndSem.lean`), where the
recursor's graph is a least fixed point on *predicates* — the ambient
logic's `Prop` is impredicative, so that is a definition (the
intersection of all closed predicates), total by induction over the
family and single-valued by induction over the graph, and the
recursor's set is the `graph` of the resulting function; nothing
set-theoretic is consumed there.

Con-leche: the tuple and tag laws mirror
`ConLeche/SetModel/TupleTower.lean` (`mkTower`, `mkTower_inj`) and
`ConLeche/SetModel/TaggedSum.lean` (`inj`, `inj_inj`); the recursion
theorem is the graph's uniqueness (`GraphRecKit.exu`,
`ConLeche/SetModel/GraphRec.lean`).
-/

namespace Fragment
open SetLib UnivLib

universe u

/-- **The library for inductive types**: the universes with tuples and
tags. -/
class IndLib (V : Type u) extends UnivLib V where
  /-- The n-ary tuple of a list of sets. -/
  tuple : List V → V
  /-- Tuples are injective. -/
  tuple_inj : ∀ {xs ys : List V}, tuple xs = tuple ys → xs = ys
  /-- A tuple of members of a positive universe is a member of it. -/
  tuple_mem_univ : ∀ {n : Nat} {xs : List V}, n ≠ 0 →
    (∀ x ∈ xs, Mem x (univ n)) → Mem (tuple xs) (univ n)
  /-- A value tagged with a number. -/
  tag : Nat → V → V
  /-- Tags are injective. -/
  tag_inj : ∀ {i j : Nat} {x y : V}, tag i x = tag j y → i = j ∧ x = y
  /-- A tagged member of a positive universe is a member of it. -/
  tag_mem_univ : ∀ {n i : Nat} {x : V}, n ≠ 0 → Mem x (univ n) → Mem (tag i x) (univ n)
  /-- A tagged value is never the point. -/
  tag_ne_pt : ∀ {i : Nat} {x : V}, tag i x ≠ pt

namespace IndLib

variable {V : Type u} [IndLib V]

/-- A universe is a member of every higher one (the chain and
cumulativity). -/
theorem univ_mem_univ {m n : Nat} (h : m < n) : (univ m : V) ∈ˢ univ n :=
  univ_mono h (univ_mem_succ m)

/-- A member of a universe below `n` is a member of `univ n` (`n`
positive) — cumulativity together with transitivity, the form the
universe bound on constructor fields is used in. -/
theorem mem_univ_of_mem_of_mem_univ {n k : Nat} {A x : V} (hn : n ≠ 0) (hk : k ≤ n)
    (hA : A ∈ˢ univ k) (hx : x ∈ˢ A) : x ∈ˢ (univ n : V) :=
  univ_trans hn (univ_mono hk hA) hx

/-- The function space is monotone in its fibres. -/
theorem piSet_mono {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x ⊆ˢ B' x) :
    piSet A B ⊆ˢ piSet A B' := by
  intro f hf
  rw [← graph_app_eq hf]
  exact graph_mem_piSet fun x hx => h x hx _ (app_mem_piSet hf hx)

/-- The two-regime product is monotone in its fibres; at a proposition
the larger fibres must be truth values. -/
theorem piR_mono {p : Bool} {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x ⊆ˢ B' x)
    (hB' : p = true → ∀ x, x ∈ˢ A → B' x ∈ˢ univ 0) :
    piR p A B ⊆ˢ piR p A B' := by
  cases p
  · exact piSet_mono h
  · intro f hf
    obtain ⟨rfl, hi⟩ := mem_truthVal.mp hf
    refine pt_mem_truthVal fun x hx => eq_one_of_mem_univ_zero (hB' rfl x hx) (h x hx pt ?_)
    rw [hi x hx]; exact mem_one.mpr rfl

end IndLib

/-! ## Least fixed points of monotone operators on predicates

Kept for the recursor's graph (`IndSem.lean`, `rstepT`): the graph of
the recursor is the least fixed point of a monotone operator on
predicates, which the ambient logic's impredicative `Prop` provides
outright.  The *family* of a block is not this: it is `lfpFamSet`
(`LfpSet.lean`), a least fixed point whose fibres are members of the
universe. -/

/-- A monotone operator on predicates over `α`. -/
def Mono {α : Sort _} (Φ : (α → Prop) → (α → Prop)) : Prop :=
  ∀ P Q : α → Prop, (∀ a, P a → Q a) → ∀ a, Φ P a → Φ Q a

/-- **The least fixed point** of an operator on predicates: the
intersection of every predicate closed under it. -/
def Lfp {α : Sort _} (Φ : (α → Prop) → (α → Prop)) : α → Prop :=
  fun a => ∀ P : α → Prop, (∀ b, Φ P b → P b) → P a

namespace Lfp

variable {α : Sort _} {Φ : (α → Prop) → (α → Prop)}

/-- The least fixed point is below every closed predicate. -/
theorem least {P : α → Prop} (h : ∀ b, Φ P b → P b) {a : α} (ha : Lfp Φ a) : P a :=
  ha P h

/-- The least fixed point is closed. -/
theorem closed (hm : Mono Φ) {a : α} (h : Φ (Lfp Φ) a) : Lfp Φ a :=
  fun P hP => hP a (hm _ _ (fun _ hb => hb P hP) a h)

/-- The least fixed point is a fixed point: a member is a step from
members. -/
theorem unfold (hm : Mono Φ) {a : α} (h : Lfp Φ a) : Φ (Lfp Φ) a :=
  h (fun b => Φ (Lfp Φ) b) fun b hb => hm _ _ (fun _ hc => closed hm hc) b hb

/-- **Induction**: a property that holds at every step from members
that have it (and are members) holds on the least fixed point. -/
theorem induction (hm : Mono Φ) {P : α → Prop}
    (h : ∀ b, Φ (fun c => Lfp Φ c ∧ P c) b → P b) {a : α} (ha : Lfp Φ a) : P a :=
  (least (P := fun c => Lfp Φ c ∧ P c)
    (fun b hb => ⟨closed hm (hm _ _ (fun _ hc => hc.1) b hb), h b hb⟩) ha).2

end Lfp

end Fragment
