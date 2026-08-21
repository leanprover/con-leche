import Setlec.SetTheory.Derive.Graphs

/-!
# Choice: the global selector, and the eighth axiom as a theorem

nanodatg asserts `ax_choice` because a first-order development cannot
reach the meta-level.  Here the meta-logic is Lean with
`Classical.choice`, so choice over `V` is *derived*, per the selection
rule "assert what we have not yet derived" (kernel README §1):

* `schoice : V → V` — a global selector, `schoice A ∈ A` whenever `A`
  is inhabited (Lean-level choice on the membership predicate);
* `set_choice` — the Jech-form statement (*Set Theory*, §1): every
  family has a *set* choice function, obtained as the replacement
  graph of `schoice`.  This is the exact content of nanodatg's
  `ax_choice`, with the set function spelled through `kpair` as there.
-/

namespace Setlec.TG

universe u

variable {V : Type u} [TG V]

open Classical in
/-- Global choice: a uniform selection from nonempty sets.  On sets
without members (and only there) it returns the set itself. -/
noncomputable def schoice (A : V) : V :=
  if h : ∃ x, x ∈ᵗ A then Classical.choose h else A

theorem schoice_mem {A x : V} (hx : x ∈ᵗ A) : schoice A ∈ᵗ A := by
  unfold schoice
  rw [dif_pos ⟨x, hx⟩]
  exact Classical.choose_spec (⟨x, hx⟩ : ∃ x, x ∈ᵗ A)

/-- The axiom of choice, Jech-form, as a theorem: every family `X` has
a set-level choice function — a single-valued set of pairs, total on
`X`, selecting a member from every inhabited `A ∈ X`. -/
theorem set_choice (X : V) :
    ∃ f : V,
      (∀ A c, kpair A c ∈ᵗ f → A ∈ᵗ X) ∧
      (∀ A, A ∈ᵗ X → ∃ c, kpair A c ∈ᵗ f ∧ ∀ c', kpair A c' ∈ᵗ f → c' = c) ∧
      (∀ A c, kpair A c ∈ᵗ f → (∃ x, x ∈ᵗ A) → c ∈ᵗ A) := by
  refine ⟨graph schoice X, ?_, ?_, ?_⟩
  · intro A c hp
    obtain ⟨A', hA', hp'⟩ := mem_graph.mp hp
    obtain ⟨rfl, -⟩ := kpair_inj hp'
    exact hA'
  · intro A hA
    refine ⟨schoice A, mem_graph.mpr ⟨A, hA, rfl⟩, ?_⟩
    intro c' hc'
    obtain ⟨A', -, hp'⟩ := mem_graph.mp hc'
    obtain ⟨rfl, rfl⟩ := kpair_inj hp'
    rfl
  · intro A c hp ⟨x, hx⟩
    obtain ⟨A', -, hp'⟩ := mem_graph.mp hp
    obtain ⟨rfl, rfl⟩ := kpair_inj hp'
    exact schoice_mem hx

end Setlec.TG
