import Setlec.SetTheory.Derive.Pair

/-!
# Grothendieck universes: the diagonal argument and the closure laws

The engine room, following nanodatg's `derived/src/cantor.rs` and
`derived/src/universe/*`.  Tarski's inaccessibility clause offers, for
any subset `S ⊆ u`, the disjunction `S ≈ u ∨ S ∈ u`; the single lemma
`covered_mem` ("regularity" in nanodatg's terminology,
`image_in_universe` there) turns it into a closure property by refuting
the first disjunct with Cantor's diagonal whenever `S` is covered by a
function from a *member* of `u`.  Everything else — pairing, power,
binary union, replacement images, `⋃` of a member — reduces to it
(`⋃` via the two-step surjection of `derived/src/universe/union.rs`,
ending in a membership 2-cycle).

`guniv x` fixes, by choice, a Grothendieck universe containing `x`.
-/

namespace Setlec.TG

universe u

variable {V : Type u} [TG V]

section IsTGUniverse

variable {U : V} (hU : IsTGUniverse (Mem (V := V)) U)

include hU

theorem _root_.Setlec.IsTGUniverse.transitive : ∀ {y z : V}, y ∈ᵗ U → z ∈ᵗ y → z ∈ᵗ U :=
  fun {y z} hy hz => hU.1 y z hy hz

theorem _root_.Setlec.IsTGUniverse.mem_of_subset_mem : ∀ {y z : V}, y ∈ᵗ U → z ⊆ᵗ y → z ∈ᵗ U :=
  fun {y z} hy hz => hU.2.1 y z hy hz

theorem _root_.Setlec.IsTGUniverse.subset_of_mem {y : V} (hy : y ∈ᵗ U) : y ⊆ᵗ U :=
  fun _ hz => hU.transitive hy hz

theorem _root_.Setlec.IsTGUniverse.power_mem {y : V} (hy : y ∈ᵗ U) : power y ∈ᵗ U := by
  obtain ⟨p, hp, hsub⟩ := hU.2.2.1 y hy
  exact hU.mem_of_subset_mem hp fun z hz => hsub z (mem_power.mp hz)

/-- Cantor's diagonal, in the form everything downstream uses
(nanodatg `cantor::image_in_universe`): a subset of `U` covered by the
image of a *member* of `U` is itself a member.  The equinumerosity
disjunct is refuted by diagonalizing the covering composed with the
would-be surjection onto `U`. -/
theorem _root_.Setlec.IsTGUniverse.covered_mem {I S : V} {F : V → V}
    (hI : I ∈ᵗ U) (hS : S ⊆ᵗ U)
    (hcov : ∀ b, b ∈ᵗ S → ∃ x, x ∈ᵗ I ∧ F x = b) : S ∈ᵗ U := by
  rcases hU.2.2.2 S hS with ⟨f, -, -, hsurj⟩ | hmem
  · -- `f : S ↠ U`; diagonalize `x ↦ f (F x) : I ↠ U` at
    -- `D := {x ∈ I : x ∉ f (F x)}`.
    exfalso
    have hDU : sep I (fun x => ¬ x ∈ᵗ f (F x)) ∈ᵗ U :=
      hU.mem_of_subset_mem hI sep_subset
    obtain ⟨b, hbS, hfb⟩ := hsurj _ hDU
    obtain ⟨j, hjI, hFj⟩ := hcov b hbS
    have hGj : f (F j) = sep I (fun x => ¬ x ∈ᵗ f (F x)) := by rw [hFj, hfb]
    have hiff : j ∈ᵗ sep I (fun x => ¬ x ∈ᵗ f (F x)) ↔
        ¬ j ∈ᵗ sep I (fun x => ¬ x ∈ᵗ f (F x)) := by
      constructor
      · intro hj
        have := (mem_sep.mp hj).2
        rwa [hGj] at this
      · intro hn
        exact mem_sep.mpr ⟨hjI, by rwa [hGj]⟩
    rcases Classical.em (j ∈ᵗ sep I (fun x => ¬ x ∈ᵗ f (F x))) with hj | hj
    · exact hiff.mp hj hj
    · exact hj (hiff.mpr hj)
  · exact hmem

/-- Replacement closure: the image of a member under a fibre-wise
member-valued function is a member. -/
theorem _root_.Setlec.IsTGUniverse.image_mem {A : V} {F : V → V}
    (hA : A ∈ᵗ U) (hF : ∀ x, x ∈ᵗ A → F x ∈ᵗ U) : image F A ∈ᵗ U :=
  hU.covered_mem hA
    (fun z hz => by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hz
      exact hF w hw)
    (fun b hb => by
      obtain ⟨w, hw, rfl⟩ := mem_image.mp hb
      exact ⟨w, hw, rfl⟩)

theorem _root_.Setlec.IsTGUniverse.empty_mem {y : V} (hy : y ∈ᵗ U) : (empty : V) ∈ᵗ U :=
  hU.mem_of_subset_mem hy (empty_subset y)

open Classical in
/-- Pairing closure, via `covered_mem` from the two-element member
`power (power ∅) = {∅, {∅}}`. -/
theorem _root_.Setlec.IsTGUniverse.upair_mem {a b y : V} (hy : y ∈ᵗ U)
    (ha : a ∈ᵗ U) (hb : b ∈ᵗ U) : upair a b ∈ᵗ U := by
  have h2 : power (power (empty : V)) ∈ᵗ U :=
    (hU.empty_mem hy |> hU.power_mem) |> hU.power_mem
  refine hU.covered_mem (F := fun x => if x = empty then a else b) h2 ?_ ?_
  · intro z hz
    rcases mem_upair.mp hz with h | h <;> subst h <;> assumption
  · intro z hz
    rcases mem_upair.mp hz with h | h <;> subst h
    · exact ⟨empty, mem_power.mpr (empty_subset _), by simp⟩
    · refine ⟨power empty, mem_power.mpr (Subset.refl _), ?_⟩
      have hne : power (empty : V) ≠ empty :=
        ne_empty_of_mem (mem_power.mpr (Subset.refl _))
      simp [hne]

theorem _root_.Setlec.IsTGUniverse.sing_mem {a y : V} (hy : y ∈ᵗ U) (ha : a ∈ᵗ U) :
    sing a ∈ᵗ U := hU.upair_mem hy ha ha

/-- `⋃` closure: nanodatg `universe/union.rs`.  A surjection
`f : ⋃s ↠ U` would make `U` the union of the member
`S = {f-image of w : w ∈ s}`, putting `S ∈ U ⊆ ⋃S` — a 2-cycle. -/
theorem _root_.Setlec.IsTGUniverse.sUnion_mem {s : V} (hs : s ∈ᵗ U) : sUnion s ∈ᵗ U := by
  have hsub : sUnion s ⊆ᵗ U := fun z hz => by
    obtain ⟨y, hy, hzy⟩ := mem_sUnion.mp hz
    exact hU.transitive (hU.transitive hs hy) hzy
  rcases hU.2.2.2 (sUnion s) hsub with ⟨f, hinto, -, hsurj⟩ | hmem
  · exfalso
    -- For each `w ∈ s`, the `f`-image of `w` is a member of `U` …
    have himg : ∀ w, w ∈ᵗ s → image f w ∈ᵗ U := fun w hw =>
      hU.image_mem (hU.transitive hs hw) fun x hx =>
        hinto x (mem_sUnion.mpr ⟨w, hw, hx⟩)
    -- … so the set of all these images is a member too …
    have hS : image (fun w => image f w) s ∈ᵗ U :=
      hU.image_mem hs fun w hw => himg w hw
    -- … but `U ⊆ ⋃(that set)`, giving `S ∈ U ⊆ ⋃S`: a 2-cycle.
    obtain ⟨x, hx, hfx⟩ := hsurj _ hS
    obtain ⟨w, hw, hxw⟩ := mem_sUnion.mp hx
    have : image (fun w => image f w) s ∈ᵗ image f w :=
      hfx ▸ mem_image.mpr ⟨x, hxw, rfl⟩
    exact no_two_cycle this (mem_image.mpr ⟨w, hw, rfl⟩)
  · exact hmem

theorem _root_.Setlec.IsTGUniverse.binUnion_mem {a b y : V} (hy : y ∈ᵗ U)
    (ha : a ∈ᵗ U) (hb : b ∈ᵗ U) : binUnion a b ∈ᵗ U :=
  hU.sUnion_mem (hU.upair_mem hy ha hb)

theorem _root_.Setlec.IsTGUniverse.kpair_mem {a b y : V} (hy : y ∈ᵗ U)
    (ha : a ∈ᵗ U) (hb : b ∈ᵗ U) : kpair a b ∈ᵗ U :=
  hU.upair_mem hy (hU.sing_mem hy ha) (hU.upair_mem hy ha hb)

theorem _root_.Setlec.IsTGUniverse.sep_mem {a : V} {p : V → Prop} (ha : a ∈ᵗ U) :
    sep a p ∈ᵗ U :=
  hU.mem_of_subset_mem ha sep_subset

/-- Union of a member-indexed family of members. -/
theorem _root_.Setlec.IsTGUniverse.famUnion_mem {A : V} {F : V → V}
    (hA : A ∈ᵗ U) (hF : ∀ x, x ∈ᵗ A → F x ∈ᵗ U) :
    sUnion (image F A) ∈ᵗ U :=
  hU.sUnion_mem (hU.image_mem hA hF)

end IsTGUniverse

/-- A fixed Grothendieck universe containing `x`, by choice from
Tarski's Axiom A. -/
noncomputable def guniv (x : V) : V := Classical.choose (tarski x)

theorem mem_guniv (x : V) : x ∈ᵗ guniv x :=
  (Classical.choose_spec (tarski x)).1

theorem guniv_isTGUniverse (x : V) : IsTGUniverse (Mem (V := V)) (guniv x) :=
  (Classical.choose_spec (tarski x)).2

end Setlec.TG
