import Setlec.SetTheory.Core

/-!
# The empty set, derived

nanodatg's `derived/empty` route (kernel README §1, "The empty set"):
the transitivity clause added to Tarski's Axiom A makes this cheap —
a universe is nonempty and transitive, so regularity's `∈`-minimal
member of it has no members at all.

Also here: the small consequences of regularity everything downstream
wants — `x ∉ x` and the impossibility of membership 2-cycles.
-/

namespace Setlec.TG

universe u

variable {V : Type u} [TG V]

theorem empty_exists : ∃ e : V, ∀ z, ¬ z ∈ᵗ e := by
  obtain ⟨x⟩ := TG.nonempty (V := V)
  obtain ⟨uu, hx, htrans, -, -, -⟩ := tarski x
  obtain ⟨y, hy, hmin⟩ := regularity uu ⟨x, hx⟩
  exact ⟨y, fun z hz => hmin ⟨z, hz, htrans y z hy hz⟩⟩

/-- The empty set. -/
noncomputable def empty : V := Classical.choose empty_exists

theorem not_mem_empty (z : V) : ¬ z ∈ᵗ (empty : V) :=
  Classical.choose_spec empty_exists z

theorem eq_empty {x : V} (h : ∀ z, ¬ z ∈ᵗ x) : x = empty :=
  ext fun z => ⟨fun hz => absurd hz (h z), fun hz => absurd hz (not_mem_empty z)⟩

theorem eq_empty_iff {x : V} : x = empty ↔ ∀ z, ¬ z ∈ᵗ x :=
  ⟨fun h z => h ▸ not_mem_empty z, eq_empty⟩

theorem ne_empty_of_mem {x z : V} (h : z ∈ᵗ x) : x ≠ empty :=
  fun he => not_mem_empty z (he ▸ h)

theorem nonempty_of_ne_empty {x : V} (h : x ≠ empty) : ∃ z, z ∈ᵗ x :=
  Classical.byContradiction fun hn => h (eq_empty fun z hz => hn ⟨z, hz⟩)

theorem empty_subset (x : V) : (empty : V) ⊆ᵗ x :=
  fun z hz => absurd hz (not_mem_empty z)

/-- No set is a member of itself (regularity at `{x}`). -/
theorem not_mem_self (x : V) : ¬ x ∈ᵗ x := by
  intro hx
  obtain ⟨y, hy, hmin⟩ := regularity (upair x x) ⟨x, mem_upair.mpr (Or.inl rfl)⟩
  have hyx : y = x := by rcases mem_upair.mp hy with h | h <;> exact h
  subst hyx
  exact hmin ⟨y, hx, mem_upair.mpr (Or.inl rfl)⟩

/-- No membership 2-cycles (regularity at `{a, b}`). -/
theorem no_two_cycle {a b : V} (hab : a ∈ᵗ b) (hba : b ∈ᵗ a) : False := by
  obtain ⟨y, hy, hmin⟩ := regularity (upair a b) ⟨a, mem_upair.mpr (Or.inl rfl)⟩
  rcases mem_upair.mp hy with h | h <;> subst h
  · exact hmin ⟨b, hba, mem_upair.mpr (Or.inr rfl)⟩
  · exact hmin ⟨a, hab, mem_upair.mpr (Or.inl rfl)⟩

end Setlec.TG
