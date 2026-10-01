module

public import Fragment.Lib

@[expose] public section

/-!
# The library for inductive types

What the environment section uses of set theory beyond `SetLib`
(`Lib.lean`), again as laws only: that **separation** (a law of
`SetLib`) stays inside the positive universes — a separated part of a
member of one is a member —, **transitivity** of the positive
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
consumed.  Likewise the **recursion theorem** (the recursor as a
function on the fixed point, one step per constructor with the
recursive calls supplied) is a theorem of the environment section
(`IndSem.lean`): the recursor's graph is itself a least fixed point,
total by induction over the family and single-valued by induction
over the graph, and the recursor's set is the `graph` of the resulting
function.

**One law is about size.**  A fibre of the family is a *subset* of
the universe; that it is a *member* — a type, not a proper class — is
the strength of the universes (an inaccessible cardinal), and the
class states it once, as **inductive closure**: for any list of
constructor telescopes (`TeleX`: ordinary fields with domains
depending on the earlier ordinary fields, recursive fields at an
index, reflexive fields — functions from a telescope of sets into the
family — after which nothing depends on the value) some family of
members is closed under every *bounded instance* of every constructor
(every domain met along the fields a member of the universe).  The
family the block defines is separated from that member, so its fibres
are members, and its constructor values lie in it because every
instance the checker's universe bound admits is bounded.

Con-leche works inside the set theory instead — `lfpFamSet`/`lfpTuple`
(`ConLeche/SetTheory/Derive/LfpFam.lean`, `LfpTuple.lean`) are
separations over a chosen closed member of the universe, the recursion
theorem is the graph's uniqueness (`GraphRecKit.exu`,
`ConLeche/SetModel/GraphRec.lean`), and the closed member comes not
from a container theorem but from the operator's accessibility, read
off the positivity check's run (`Semantics/Inductives/HoleAcc.lean`,
`closed_of_acc` in `SetModel/Access.lean`).  The tuple and tag laws mirror
`ConLeche/SetModel/TupleTower.lean` (`mkTower`, `mkTower_inj`) and
`ConLeche/SetModel/TaggedSum.lean` (`inj`, `inj_inj`).
-/

namespace Fragment
open SetLib

universe u

/-! ## Telescopes of sets and constructor telescopes -/

/-- A dependent telescope of sets, outermost first: each set may
depend on the values of the earlier ones. -/
inductive TeleS (V : Type u) : Type u where
  /-- The empty telescope. -/
  | nil : TeleS V
  /-- A set, then a telescope depending on a member of it. -/
  | cons (A : V) (B : V → TeleS V) : TeleS V

namespace TeleS

variable {V : Type u} [SetLib V]

/-- Values fitting a telescope (outermost first). -/
def Fits : TeleS V → List V → Prop
  | nil, [] => True
  | cons A B, v :: vs => v ∈ˢ A ∧ Fits (B v) vs
  | _, _ => False

/-- The nested function space over a telescope, into fibres indexed by
the values. -/
def pi : TeleS V → (List V → V) → V
  | nil, F => F []
  | cons A B, F => piSet A fun v => pi (B v) fun vs => F (v :: vs)

/-- Every set met along fitting values is a member of `univ n`. -/
def Bounded (n : Nat) : TeleS V → Prop
  | nil => True
  | cons A B => A ∈ˢ univ n ∧ ∀ v, v ∈ˢ A → Bounded n (B v)

end TeleS

/-- **A constructor telescope** relative to a family over an index
type `ι`, outermost first: an *ordinary* field with a domain, the rest
depending on its value; a *recursive* field at an index; a *reflexive*
field — a function from a telescope of sets into the family at
targets depending on the arguments.  After a recursive or reflexive
field the rest does not depend on the value (con-leche's
`structUsedLater` guard run by `nestCtors`, `Positivity.lean:1247`). -/
inductive TeleX (ι : Type u) (V : Type u) : Type u where
  /-- No more fields. -/
  | nil : TeleX ι V
  /-- An ordinary field. -/
  | ord (A : V) (rest : V → TeleX ι V) : TeleX ι V
  /-- A recursive field, in the family at `i`. -/
  | recur (i : ι) (rest : TeleX ι V) : TeleX ι V
  /-- A reflexive field: a function over `tele` into the family at
  `tgt` of the arguments. -/
  | refl (tele : TeleS V) (tgt : List V → ι) (rest : TeleX ι V) : TeleX ι V

namespace TeleX

variable {ι : Type u} {V : Type u} [SetLib V]

/-- **A bounded instance** of a constructor telescope relative to a
family `W`: values (outermost first) fitting it, every domain met a
member of `univ n`, recursive values in `W` at their index, reflexive
values in the function space into `W` at the targets. -/
def FitsB (n : Nat) (W : ι → V) : TeleX ι V → List V → Prop
  | nil, [] => True
  | ord A rest, v :: vs => A ∈ˢ univ n ∧ v ∈ˢ A ∧ FitsB n W (rest v) vs
  | recur i rest, v :: vs => v ∈ˢ W i ∧ FitsB n W rest vs
  | refl tele tgt rest, v :: vs =>
    tele.Bounded n ∧ v ∈ˢ tele.pi (fun ys => W (tgt ys)) ∧ FitsB n W rest vs
  | _, _ => False

end TeleX

/-- **The library for inductive types**: `SetLib` with separation
inside the universes, transitivity, tuples, tags and inductive
closure. -/
class IndLib (V : Type u) extends SetLib V where
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
  /-- **Inductive closure** of the positive universes: for every list
  of constructor telescopes with their target indices, some family of
  members of `univ n` is closed under every bounded instance of every
  constructor — the tagged tuple of the instance's values is a member
  of the family at the constructor's target. -/
  inductive_closure : ∀ {ι : Type u} {n : Nat}, n ≠ 0 →
    ∀ cs : List (TeleX ι V × (List V → ι)),
      ∃ W : ι → V, (∀ i, Mem (W i) (univ n)) ∧
        ∀ (j : Nat) (c : TeleX ι V × (List V → ι)) (fs : List V), cs[j]? = some c →
          TeleX.FitsB n W c.1 fs → Mem (tag j (tuple fs)) (W (c.2 fs))

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
