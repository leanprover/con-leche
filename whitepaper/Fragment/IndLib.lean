module

public import Fragment.Lib

@[expose] public section

/-!
# The library for inductive types

What the environment section uses of set theory beyond `SetLib`
(`Lib.lean`), again as laws only: **separation** (the members of a set
satisfying a property form a set, and a separated part of a member of
a positive universe is a member), **transitivity** of the positive
universes, **n-ary tuples** (injective, universe-closed) and **tagged
values** (injective, universe-closed, never the point).  A constructor
application denotes a tagged tuple — the constructor's number, then
its fields — and the family is separated from the universe by the
least-fixed-point predicate below.

**Least fixed points are theorems, not laws.**  The family of an
inductive block is the least fixed point of a monotone operator on
*predicates*; the ambient logic's `Prop` is impredicative, so that
least fixed point is a definition (`Lfp`: the intersection of all
closed predicates), and the fixed-point equation and the induction
principle are proved below the class — nothing set-theoretic is
consumed.  Separation then turns the predicate into a set, one fibre
at a time.  Likewise the **recursion theorem** (the recursor as a
function on the fixed point, one step per constructor with the
recursive calls supplied) is a theorem of the environment section
(`IndSem.lean`): the recursor's graph is itself a least fixed point,
total by induction over the family and single-valued by induction
over the graph, and the recursor's set is the `graph` of the resulting
function.

Con-leche works inside the set theory instead — `lfpSet`/`lfpFamSet`
(`ConLeche/SetTheory/Derive/Lfp.lean`, `LfpFam.lean`) are separations
over a chosen closed member of the universe, the recursion theorem is
`recGraph` (`ConLeche/SetModel/RecGraph.lean`), and the closed member
a reflexive block needs is exhibited by the container theorem
(`ConLeche/SetModel/Container.lean`).  The tuple and tag laws mirror
`ConLeche/SetModel/TupleTower.lean` (`mkTower`, `mkTower_inj`) and
`ConLeche/SetModel/TaggedSum.lean` (`inj`, `inj_inj`).
-/

namespace Fragment
open SetLib

universe u

/-- **The library for inductive types**: `SetLib` with separation,
transitivity, tuples and tags. -/
class IndLib (V : Type u) extends SetLib V where
  /-- Separation: the members of `A` that satisfy `P`. -/
  sep : V → (V → Prop) → V
  /-- The members of a separation. -/
  mem_sep : ∀ {A : V} {P : V → Prop} {x : V}, Mem x (sep A P) ↔ Mem x A ∧ P x
  /-- A separated part of a member of a positive universe is a member of
  it. -/
  sep_mem_univ : ∀ {n : Nat} {A : V} {P : V → Prop}, n ≠ 0 →
    Mem A (univ n) → Mem (sep A P) (univ n)
  /-- The positive universes are transitive: a member of a member is a
  member. -/
  univ_trans : ∀ {n : Nat} {A x : V}, n ≠ 0 → Mem A (univ n) → Mem x A → Mem x (univ n)
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

namespace SetLib

variable {V : Type u} [SetLib V]

/-- Inclusion. -/
def Sub (A B : V) : Prop := ∀ x, x ∈ˢ A → x ∈ˢ B

@[inherit_doc] scoped infix:50 " ⊆ˢ " => Sub

theorem Sub.refl (A : V) : A ⊆ˢ A := fun _ h => h

theorem Sub.trans {A B C : V} (h₁ : A ⊆ˢ B) (h₂ : B ⊆ˢ C) : A ⊆ˢ C := fun x hx => h₂ x (h₁ x hx)

end SetLib

namespace IndLib

variable {V : Type u} [IndLib V]

theorem mem_sep_of {A : V} {P : V → Prop} {x : V} (hx : x ∈ˢ A) (hp : P x) : x ∈ˢ sep A P :=
  mem_sep.mpr ⟨hx, hp⟩

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

/-- The two-regime product is monotone in its fibres. -/
theorem piR_mono {p : Bool} {A : V} {B B' : V → V} (h : ∀ x, x ∈ˢ A → B x ⊆ˢ B' x) :
    piR p A B ⊆ˢ piR p A B' := by
  cases p
  · exact piSet_mono h
  · intro f hf
    obtain ⟨rfl, hi⟩ := mem_truthVal.mp hf
    exact pt_mem_truthVal fun x hx => (hi x hx).imp fun y hy => h x hx y hy

end IndLib

/-! ## Least fixed points of monotone operators on predicates -/

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
