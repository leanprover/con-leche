import Setlec.SetTheory.Derive.Pi
import Setlec.SetTheory.Derive.Omega

/-!
# The universe tower

`univ 0` is the set of truth values (`univZero`, Carneiro's `U₀`);
`univ (n+1)` is a Grothendieck universe containing both `univ n` and
the inductive universe `guniv ∅` — the second component is what puts
`ω` inside every positive level (a bare universe need not contain
`ω`; `V_ω` is one).  Cumulativity holds because positive levels are
transitive and each level is a member of the next.
-/

namespace Setlec.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- The universe tower interpreting `Sort n`. -/
noncomputable def univ : Nat → V
  | 0 => univZero
  | n + 1 => guniv (upair (univ n) (guniv empty))

theorem univ_zero : (univ 0 : V) = univZero := rfl

/-- Positive levels are Grothendieck universes. -/
theorem univ_isTGUniverse {n : Nat} (hn : n ≠ 0) :
    IsTGUniverse (Mem (V := V)) (univ n) := by
  match n, hn with
  | m + 1, _ => exact guniv_isTGUniverse _

theorem guniv_empty_mem_univ_succ (n : Nat) :
    guniv (empty : V) ∈ˢ univ (n + 1) :=
  (guniv_isTGUniverse _).transitive (mem_guniv _) (mem_upair_right _ _)

theorem univ_mem_univ (n : Nat) : (univ n : V) ∈ˢ univ (n + 1) :=
  (guniv_isTGUniverse _).transitive (mem_guniv _) (mem_upair_left _ _)

theorem univ_subset_succ (n : Nat) : (univ n : V) ⊆ˢ univ (n + 1) :=
  (univ_isTGUniverse (Nat.succ_ne_zero n)).subset_of_mem (univ_mem_univ n)

theorem univ_mono {m n : Nat} (h : m ≤ n) : (univ m : V) ⊆ˢ univ n := by
  induction n with
  | zero => cases Nat.le_zero.mp h; exact Subset.refl _
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le h) with h' | rfl
    · exact (ih (Nat.lt_succ_iff.mp h')).trans (univ_subset_succ n)
    · exact Subset.refl _

theorem omega_mem_univ_succ (n : Nat) : (omega : V) ∈ˢ univ (n + 1) :=
  (univ_isTGUniverse (Nat.succ_ne_zero n)).omega_mem (guniv_empty_mem_univ_succ n)

theorem empty_mem_univ : ∀ n : Nat, (empty : V) ∈ˢ univ n
  | 0 => mem_univZero.mpr (empty_subset _)
  | n + 1 =>
    (univ_isTGUniverse (Nat.succ_ne_zero n)).empty_mem (guniv_empty_mem_univ_succ n)

theorem unitSet_mem_univ : ∀ n : Nat, (unitSet : V) ∈ˢ univ n
  | 0 => mem_univZero.mpr (Subset.refl _)
  | n + 1 =>
    (univ_isTGUniverse (Nat.succ_ne_zero n)).unitSet_mem (guniv_empty_mem_univ_succ n)

/-- Formation for `pi` along the tower, with the `imax`-style level. -/
theorem pi_mem_univ {u v : Nat} {A : V} {B : V → V}
    (hA : A ∈ˢ (univ u : V)) (hB : ∀ x, x ∈ˢ A → B x ∈ˢ (univ v : V)) :
    pi v A B ∈ˢ (univ (if v = 0 then 0 else Nat.max u v) : V) := by
  rcases Nat.eq_zero_or_pos v with rfl | hv
  · rw [if_pos rfl, univ_zero]
    exact pi_zero_mem_univZero
  · have hv' : v ≠ 0 := Nat.pos_iff_ne_zero.mp hv
    rw [if_neg hv']
    have hw : (Nat.max u v : Nat) ≠ 0 :=
      fun h => hv' (Nat.le_zero.mp (h ▸ Nat.le_max_right u v))
    exact (univ_isTGUniverse hw).pi_mem hv'
      (univ_mono (Nat.le_max_left u v) A hA)
      (fun x hx => univ_mono (Nat.le_max_right u v) _ (hB x hx))

/- Compiler stub (see `Derive/Empty.lean`): never executed, no logical
content. -/
private unsafe def univImpl {V : Type u} [SetTheory V] (_n : Nat) : V := unsafeCast ()

attribute [implemented_by univImpl] univ

/- Opaque interface operator (see `Derive/Empty.lean`). -/
attribute [irreducible] univ

end Setlec.SetTheory
