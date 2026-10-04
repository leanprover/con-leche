module

public import Fragment.Lib

@[expose] public section

/-!
# The positive universes are Grothendieck universes

`SetLib` (`Lib.lean`) states what the typing part of the proof uses of
set theory.  The inductive part needs more of the universes: that each
positive universe `univ n` (`n ≥ 1`) is a **Grothendieck universe** —
a transitive set closed under pairing, union, power set and
replacement (SGA 4, Exp. I, Appendix) — and that it contains `ω`.
This class adds the four operators with their membership laws, the
numerals with `ω`, and the closure laws of the positive universes,
stated once.  Everything the family construction needs of the
universes (`LfpSet.lean`, `Access.lean`) is derived below the class:
a subset of a member is a member (so a separation is), the empty set,
singletons, binary and indexed unions, and the countable union.

Con-leche's core (`ConLeche/SetTheory/Core.lean`) states universehood
as the matrix of Tarski's Axiom A with a transitivity clause
(`IsTGUniverse`) and derives these closure laws and infinity from it
(`ConLeche/SetTheory/Derive/Universe.lean`, `Univ.lean`,
`Omega.lean`); the fragment takes the derived laws as its interface,
as `SetLib` does for the rest.

**Infinity is not a convenience.**  `V_ω`, the hereditarily finite
sets, is transitive and closed under pairing, union, power set and
replacement, and the least fixed point of `X ↦ {∅} ∪ {x ∪ {x} | x ∈ X}`
— accessible with a one-element bound — is `ω ∉ V_ω`.  So the theorem
`closed_of_acc` (`Access.lean`) needs `ω ∈ univ n`, and uses it
exactly once: the set of finite paths over the bound is a countable
union (`natUnion`).
-/

namespace Fragment
open SetLib

universe u

/-- **The positive universes are Grothendieck universes.**  `SetLib`
with pairing, union, power set and replacement (the image of a set
under any function of the ambient logic), the numerals and `ω`, and
the laws: every `univ n` with `n ≠ 0` is transitive and closed under
the four operations, and contains `ω`. -/
class UnivLib (V : Type u) extends SetLib V where
  /-- The unordered pair. -/
  upair : V → V → V
  /-- The members of a pair. -/
  mem_upair : ∀ {z a b : V}, Mem z (upair a b) ↔ z = a ∨ z = b
  /-- The union of the members. -/
  sUnion : V → V
  /-- The members of a union. -/
  mem_sUnion : ∀ {z x : V}, Mem z (sUnion x) ↔ ∃ y, Mem y x ∧ Mem z y
  /-- The power set. -/
  power : V → V
  /-- The members of a power set: the subsets. -/
  mem_power : ∀ {z x : V}, Mem z (power x) ↔ ∀ w, Mem w z → Mem w x
  /-- Replacement: the image of a set under a function. -/
  image : (V → V) → V → V
  /-- The members of an image. -/
  mem_image : ∀ {f : V → V} {A z : V}, Mem z (image f A) ↔ ∃ w, Mem w A ∧ z = f w
  /-- The numerals. -/
  nat : Nat → V
  /-- Distinct numbers have distinct numerals. -/
  nat_inj : ∀ {k l : Nat}, nat k = nat l → k = l
  /-- `ω`: the set of numerals. -/
  omega : V
  /-- The members of `ω`. -/
  mem_omega : ∀ {z : V}, Mem z omega ↔ ∃ k, z = nat k
  /-- A positive universe is transitive: a member of a member is a
  member. -/
  univ_trans : ∀ {n : Nat} {A x : V}, n ≠ 0 → Mem A (univ n) → Mem x A → Mem x (univ n)
  /-- A positive universe is closed under pairing. -/
  upair_mem_univ : ∀ {n : Nat} {a b : V}, n ≠ 0 →
    Mem a (univ n) → Mem b (univ n) → Mem (upair a b) (univ n)
  /-- A positive universe is closed under union. -/
  sUnion_mem_univ : ∀ {n : Nat} {x : V}, n ≠ 0 → Mem x (univ n) → Mem (sUnion x) (univ n)
  /-- A positive universe is closed under power set. -/
  power_mem_univ : ∀ {n : Nat} {x : V}, n ≠ 0 → Mem x (univ n) → Mem (power x) (univ n)
  /-- A positive universe is closed under replacement: the image of a
  member under a function into the universe is a member. -/
  image_mem_univ : ∀ {n : Nat} {f : V → V} {A : V}, n ≠ 0 → Mem A (univ n) →
    (∀ a, Mem a A → Mem (f a) (univ n)) → Mem (image f A) (univ n)
  /-- A positive universe contains `ω`. -/
  omega_mem_univ : ∀ {n : Nat}, n ≠ 0 → Mem omega (univ n)

namespace SetLib

variable {V : Type u} [SetLib V]

/-- Inclusion. -/
def Sub (A B : V) : Prop := ∀ x, x ∈ˢ A → x ∈ˢ B

@[inherit_doc] scoped infix:50 " ⊆ˢ " => Sub

theorem Sub.refl (A : V) : A ⊆ˢ A := fun _ h => h

theorem Sub.trans {A B C : V} (h₁ : A ⊆ˢ B) (h₂ : B ⊆ˢ C) : A ⊆ˢ C := fun x hx => h₂ x (h₁ x hx)

theorem Sub.antisymm {A B : V} (h₁ : A ⊆ˢ B) (h₂ : B ⊆ˢ A) : A = B := ext fun z => ⟨h₁ z, h₂ z⟩

theorem sep_sub {A : V} {P : V → Prop} : sep A P ⊆ˢ A := fun _ h => (mem_sep.mp h).1

end SetLib

namespace UnivLib

variable {V : Type u} [UnivLib V]

/-! ## Subsets of members, separation, the empty set -/

/-- A subset of a member of a universe is a member: at a positive
universe it is a member of the power set, which is a member; at
`univ 0` it is a subset of `{pt}`.  Con-leche:
`univ_mem_of_subset_mem`, `ConLeche/SetTheory/Derive/Universe.lean`. -/
theorem mem_univ_of_sub {n : Nat} {A B : V} (hA : A ∈ˢ univ n) (h : B ⊆ˢ A) :
    B ∈ˢ (univ n : V) := by
  cases n with
  | zero => exact mem_univ_zero.mpr fun z hz => mem_univ_zero.mp hA z (h z hz)
  | succ n =>
    exact univ_trans (Nat.succ_ne_zero n) (power_mem_univ (Nat.succ_ne_zero n) hA)
      (mem_power.mpr h)

/-- A separated part of a member of a universe is a member.
Con-leche: `univ_sep_mem`, `ConLeche/SetTheory/Derive/Lfp.lean`. -/
theorem sep_mem_univ {n : Nat} {A : V} {P : V → Prop} (hA : A ∈ˢ univ n) :
    sep A P ∈ˢ (univ n : V) := mem_univ_of_sub hA sep_sub

/-- `{pt}` is a member of every universe. -/
theorem one_mem_univ (n : Nat) : (one : V) ∈ˢ univ n := univ_mono (Nat.zero_le n) one_mem_univ_zero

/-- The empty set: the members of `{pt}` that are not. -/
def empty : V := sep one fun _ => False

theorem not_mem_empty (z : V) : ¬ z ∈ˢ (empty : V) := fun h => (mem_sep.mp h).2

theorem empty_sub (A : V) : (empty : V) ⊆ˢ A := fun z hz => absurd hz (not_mem_empty z)

theorem empty_mem_univ (n : Nat) : (empty : V) ∈ˢ univ n :=
  univ_mono (Nat.zero_le n) (mem_univ_zero.mpr fun z hz => absurd hz (not_mem_empty z))

/-! ## Singletons and unions -/

/-- The singleton. -/
def sing (a : V) : V := upair a a

theorem mem_sing {z a : V} : z ∈ˢ sing a ↔ z = a := by
  unfold sing; rw [mem_upair, or_self]

theorem sing_mem_univ {n : Nat} {a : V} (hn : n ≠ 0) (ha : a ∈ˢ univ n) :
    sing a ∈ˢ (univ n : V) := upair_mem_univ hn ha ha

/-- Binary union. -/
def binUnion (x y : V) : V := sUnion (upair x y)

theorem mem_binUnion {z x y : V} : z ∈ˢ binUnion x y ↔ z ∈ˢ x ∨ z ∈ˢ y := by
  unfold binUnion
  rw [mem_sUnion]
  constructor
  · rintro ⟨w, hw, hz⟩
    rcases mem_upair.mp hw with rfl | rfl
    · exact Or.inl hz
    · exact Or.inr hz
  · rintro (h | h)
    · exact ⟨x, mem_upair.mpr (Or.inl rfl), h⟩
    · exact ⟨y, mem_upair.mpr (Or.inr rfl), h⟩

theorem binUnion_mem_univ {n : Nat} {x y : V} (hn : n ≠ 0) (hx : x ∈ˢ univ n) (hy : y ∈ˢ univ n) :
    binUnion x y ∈ˢ (univ n : V) := sUnion_mem_univ hn (upair_mem_univ hn hx hy)

theorem image_congr {A : V} {f g : V → V} (h : ∀ a, a ∈ˢ A → f a = g a) :
    image f A = image g A :=
  ext fun z => by
    rw [mem_image, mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, h a ha⟩
    · rintro ⟨a, ha, rfl⟩; exact ⟨a, ha, (h a ha).symm⟩

/-- **The union of an indexed family** `⋃ a ∈ A, F a`: replacement,
then union.  Con-leche: `IsTGUniverse.famUnion_mem`,
`ConLeche/SetTheory/Derive/Universe.lean`. -/
def famUnion (A : V) (F : V → V) : V := sUnion (image F A)

theorem mem_famUnion {A z : V} {F : V → V} : z ∈ˢ famUnion A F ↔ ∃ a, a ∈ˢ A ∧ z ∈ˢ F a := by
  unfold famUnion
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hz⟩
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hy
    exact ⟨a, ha, hz⟩
  · rintro ⟨a, ha, hz⟩
    exact ⟨F a, mem_image.mpr ⟨a, ha, rfl⟩, hz⟩

theorem famUnion_mem_univ {n : Nat} {A : V} {F : V → V} (hn : n ≠ 0) (hA : A ∈ˢ univ n)
    (hF : ∀ a, a ∈ˢ A → F a ∈ˢ univ n) : famUnion A F ∈ˢ (univ n : V) :=
  sUnion_mem_univ hn (image_mem_univ hn hA hF)

theorem famUnion_congr {A : V} {F G : V → V} (h : ∀ a, a ∈ˢ A → F a = G a) :
    famUnion A F = famUnion A G := by
  unfold famUnion; rw [image_congr h]

/-! ## The countable union -/

open Classical in
/-- The number of a numeral (`0` off the numerals). -/
noncomputable def idx (z : V) : Nat := if h : ∃ k, nat k = z then Classical.choose h else 0

theorem idx_nat (k : Nat) : idx (nat k : V) = k := by
  unfold idx
  have h : ∃ l, (nat l : V) = nat k := ⟨k, rfl⟩
  rw [dite_eq_left h]
  exact nat_inj (Classical.choose_spec h)

/-- **The countable union** `F 0 ∪ F 1 ∪ …`: the union over `ω`, each
numeral read back as its number.  Con-leche: `Tower.natUnion`,
`ConLeche/SetModel/Iter.lean`. -/
noncomputable def natUnion (F : Nat → V) : V := famUnion omega fun z => F (idx z)

theorem mem_natUnion {F : Nat → V} {z : V} : z ∈ˢ natUnion F ↔ ∃ k, z ∈ˢ F k := by
  unfold natUnion
  rw [mem_famUnion]
  constructor
  · rintro ⟨w, -, hz⟩
    exact ⟨idx w, hz⟩
  · rintro ⟨k, hk⟩
    exact ⟨nat k, mem_omega.mpr ⟨k, rfl⟩, by rw [idx_nat]; exact hk⟩

/-- A countable union of members of a positive universe is a member —
the one use of `ω`.  Con-leche: `Tower.natUnion_mem_univ_pos`,
`ConLeche/SetModel/Iter.lean`. -/
theorem natUnion_mem_univ {n : Nat} {F : Nat → V} (hn : n ≠ 0) (h : ∀ k, F k ∈ˢ univ n) :
    natUnion F ∈ˢ (univ n : V) :=
  famUnion_mem_univ hn (omega_mem_univ hn) fun _ _ => h _

end UnivLib

end Fragment
