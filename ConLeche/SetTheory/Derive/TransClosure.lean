module

public import ConLeche.SetTheory.Derive.Omega

@[expose] public section

/-!
# The transitive closure of a set, and ∈-induction (falsifier F5)

The GLOBAL subterm relation of the maintainer's formulation of nested
inductives: `x ⊏ y := x ∈ˢ tc y`, where

    tc y = y ∪ ⋃ y ∪ ⋃⋃ y ∪ …

is the (strict) transitive closure — the ω-union of the finite
`sUnion`-iterates `sunIter n y`, a set by union and replacement alone
(no universe, no bound).  A member of `tc y` is exactly the bottom of
a finite ∈-chain `x ∈ a₁ ∈ … ∈ aₙ ∈ y` (`mem_tc_iff_chain`).

The payoff is `tc_induction`: **∈-induction from regularity**, in the
transitive-closure form, and its pullback `tc_induction_map` along an
arbitrary `f : V → V` — the form a *tagged* recursion index needs,
where the relation compares the tagged values' payloads.  With it, a
recursion whose predecessors are the ∈-smaller elements of an index
set is well founded FOR FREE, with no fixed-point structure on that
index set at all (`ConLeche/SetModel/WfRec.lean`): this is what
replaces the simultaneous lfp induction of `unionAcc_all`.

Regularity enters once, in `mem_induction` (the ordinary ∈-form): the
set of hereditary counterexamples below a would-be counterexample is
nonempty, so it has an ∈-minimal member, whose members all satisfy the
motive.  The transitive-closure form follows by an inner induction on
`Q y := ∀ x ∈ tc y, P x` (`tc_induction`), using the one-step
decomposition `mem_tc_step`.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## The finite union iterates -/

/-- The `n`-fold union of `y`: `sunIter 0 y = y`, `sunIter (n+1) y = ⋃ (sunIter n y)`. -/
noncomputable def sunIter : Nat → V → V
  | 0, y => y
  | n + 1, y => sUnion (sunIter n y)

@[simp] theorem sunIter_zero (y : V) : sunIter 0 y = y := rfl

@[simp] theorem sunIter_succ (n : Nat) (y : V) : sunIter (n + 1) y = sUnion (sunIter n y) := rfl

/-- The union iterates are monotone in the set. -/
theorem sunIter_mono : ∀ (n : Nat) {x y : V}, x ⊆ˢ y → sunIter n x ⊆ˢ sunIter n y
  | 0, _, _, h => h
  | n + 1, x, y, h => by
    intro z hz
    obtain ⟨a, ha, hza⟩ := mem_sUnion.mp hz
    exact mem_sUnion.mpr ⟨a, sunIter_mono n h a ha, hza⟩

open Classical in
/-- The stage selector over `ω`: `sunIter n y` at `vnat n`, junk off
the numerals (never consulted there — every member of `ω` is a unique
numeral). -/
noncomputable def sunFibre (y k : V) : V :=
  if h : ∃ n, k = vnat n then sunIter (Classical.choose h) y else empty

theorem sunFibre_vnat (y : V) (n : Nat) : sunFibre y (vnat n) = sunIter n y := by
  unfold sunFibre
  rw [dif_pos ⟨n, rfl⟩]
  congr 1
  exact (vnat_inj (Classical.choose_spec (⟨n, rfl⟩ : ∃ n', (vnat n : V) = vnat n'))).symm

/-! ## The transitive closure -/

/-- **The (strict) transitive closure**: the union of the finite union
iterates — members, members of members, and so on. -/
noncomputable def tc (y : V) : V := sUnion (image (sunFibre y) omega)

/-- Membership in the transitive closure is membership in a finite
union iterate: `x ∈ˢ tc y` iff `x` sits at the bottom of an ∈-chain of
some finite length up to `y` (the chain itself: `mem_tc_iff_chain`). -/
theorem mem_tc {x y : V} : x ∈ˢ tc y ↔ ∃ n, x ∈ˢ sunIter n y := by
  unfold tc
  rw [mem_sUnion]
  constructor
  · rintro ⟨s, hs, hxs⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hs
    obtain ⟨n, rfl⟩ := mem_omega_iff.mp hk
    rw [sunFibre_vnat] at hxs
    exact ⟨n, hxs⟩
  · rintro ⟨n, hn⟩
    exact ⟨sunFibre y (vnat n), mem_image.mpr ⟨vnat n, vnat_mem_omega n, rfl⟩,
      by rw [sunFibre_vnat]; exact hn⟩

/-- A member is a subterm. -/
theorem mem_tc_of_mem {x y : V} (h : x ∈ˢ y) : x ∈ˢ tc y := mem_tc.mpr ⟨0, h⟩

/-- **The transitive closure is a transitive set**: a member of a
subterm is a subterm. -/
theorem mem_tc_of_mem_tc {w x y : V} (hw : w ∈ˢ x) (hx : x ∈ˢ tc y) : w ∈ˢ tc y := by
  obtain ⟨n, hn⟩ := mem_tc.mp hx
  exact mem_tc.mpr ⟨n + 1, mem_sUnion.mpr ⟨x, hn, hw⟩⟩

/-- **Transitivity of the subterm relation.** -/
theorem tc_trans {x y z : V} (hxy : x ∈ˢ tc y) (hyz : y ∈ˢ tc z) : x ∈ˢ tc z := by
  obtain ⟨n, hn⟩ := mem_tc.mp hxy
  clear hxy
  induction n generalizing x with
  | zero => exact mem_tc_of_mem_tc hn hyz
  | succ n ih =>
    obtain ⟨a, ha, hxa⟩ := mem_sUnion.mp hn
    exact mem_tc_of_mem_tc hxa (ih ha)

/-- The subterms of `y` are `y`'s members and their subterms — the one
step the ∈-induction is built on. -/
theorem mem_tc_step {x y : V} : x ∈ˢ tc y ↔ ∃ a, a ∈ˢ y ∧ (x = a ∨ x ∈ˢ tc a) := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_tc.mp hx
    clear hx
    induction n generalizing x with
    | zero => exact ⟨x, hn, Or.inl rfl⟩
    | succ n ih =>
      obtain ⟨a, ha, hxa⟩ := mem_sUnion.mp hn
      obtain ⟨b, hb, hcase⟩ := ih ha
      refine ⟨b, hb, Or.inr ?_⟩
      rcases hcase with rfl | hab
      · exact mem_tc_of_mem hxa
      · exact mem_tc_of_mem_tc hxa hab
  · rintro ⟨a, ha, rfl | hxa⟩
    · exact mem_tc_of_mem ha
    · exact tc_trans hxa (mem_tc_of_mem ha)

/-! ## The ∈-chain characterisation -/

/-- `MemChain x l y`: the ∈-chain `x ∈ˢ a₁ ∈ˢ … ∈ˢ aₙ ∈ˢ y`, with `l =
[a₁, …, aₙ]` the intermediate sets listed from `x` upward. -/
def MemChain : V → List V → V → Prop
  | x, [], y => x ∈ˢ y
  | x, a :: l, y => x ∈ˢ a ∧ MemChain a l y

/-- **`tc` IS the finite-∈-chain relation.** -/
theorem mem_tc_iff_chain {x y : V} : x ∈ˢ tc y ↔ ∃ l : List V, MemChain x l y := by
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := mem_tc.mp hx
    clear hx
    induction n generalizing x with
    | zero => exact ⟨[], hn⟩
    | succ n ih =>
      obtain ⟨a, ha, hxa⟩ := mem_sUnion.mp hn
      obtain ⟨l, hl⟩ := ih ha
      exact ⟨a :: l, hxa, hl⟩
  · rintro ⟨l, hl⟩
    induction l generalizing x with
    | nil => exact mem_tc_of_mem hl
    | cons a l ih => exact mem_tc_of_mem_tc hl.1 (ih hl.2)

/-! ## ∈-induction -/

/-- **∈-induction, from regularity**: a motive closed under "all
members satisfy it" holds everywhere.  The set of counterexamples
hereditarily below a would-be counterexample is nonempty, hence has an
∈-minimal member, all of whose members satisfy the motive. -/
theorem mem_induction {P : V → Prop} (h : ∀ y, (∀ x, x ∈ˢ y → P x) → P y) (y : V) : P y := by
  refine Classical.byContradiction fun hy => ?_
  have hmem : y ∈ˢ binUnion (sing y) (tc y) := mem_binUnion.mpr (Or.inl (mem_sing.mpr rfl))
  obtain ⟨m, hmS, hmin⟩ :=
    regularity (sep (binUnion (sing y) (tc y)) (fun z => ¬ P z)) ⟨y, mem_sep.mpr ⟨hmem, hy⟩⟩
  obtain ⟨hmU, hmP⟩ := mem_sep.mp hmS
  refine hmP (h m fun x hx => Classical.byContradiction fun hxP =>
    hmin ⟨x, hx, mem_sep.mpr ⟨mem_binUnion.mpr (Or.inr ?_), hxP⟩⟩)
  rcases mem_binUnion.mp hmU with hm1 | hm2
  · rw [mem_sing.mp hm1] at hx
    exact mem_tc_of_mem hx
  · exact mem_tc_of_mem_tc hx hm2

/-- **∈-induction in the transitive-closure form**: a motive closed
under "all SUBTERMS satisfy it" holds everywhere.  This is the
well-foundedness of `x ⊏ y := x ∈ˢ tc y`, stated as an induction
principle. -/
theorem tc_induction {P : V → Prop} (h : ∀ y, (∀ x, x ∈ˢ tc y → P x) → P y) (y : V) : P y := by
  have key : ∀ z : V, ∀ x, x ∈ˢ tc z → P x := by
    refine mem_induction (P := fun z => ∀ x, x ∈ˢ tc z → P x) ?_
    intro z ih x hx
    obtain ⟨a, ha, hcase⟩ := mem_tc_step.mp hx
    rcases hcase with rfl | hxa
    · exact h x (ih x ha)
    · exact ih a ha x hxa
  exact h y (key y)

/-- **∈-induction along a pullback**: well-foundedness of `u ≺ v :=
f u ∈ˢ tc (f v)` for an arbitrary `f`.  This is the form a TAGGED
recursion index needs — the index is `⟨class, index, value⟩` and the
relation compares the VALUES. -/
theorem tc_induction_map {f : V → V} {P : V → Prop}
    (h : ∀ u, (∀ v, f v ∈ˢ tc (f u) → P v) → P u) (u : V) : P u := by
  have key : ∀ y : V, ∀ u, f u = y → P u := by
    refine tc_induction (P := fun y => ∀ u, f u = y → P u) ?_
    intro y ih u hu
    exact h u fun v hv => ih (f v) (by rw [← hu]; exact hv) v rfl
  exact key (f u) u rfl

end ConLeche.SetTheory
