import Lech.SetModel.TaggedSum

/-!
# The ω-iterate of a set functor (task #188)

The one place iteration survives in the recursive-type model: the
carrier is the Knaster–Tarski least pre-fixed point
(`Lech/SetTheory/Derive/Lfp.lean`), and every law about it assumes a
CLOSED MEMBER of the universe exists.  For a *finitary* tower functor
that witness is the ω-iterate

    iterF Φ 0 = ∅,   iterF Φ (n+1) = Φ (iterF Φ n),   iterU Φ = ⋃ₙ iterF Φ n

— a countable union of members of `univ w`, hence a member (`ω ∈ univ
w` at `w ≥ 1`, `omega_mem_univ_succ`; at `w = 0` truth values), and
closed under `Φ` whenever every member of `Φ (iterU Φ)` already lies in
some `Φ (iterF Φ n)` (`iterU_closed_of` — the finitary condition,
discharged for the tower functor in `Lech/Semantics/Tower/FixLeaf.lean`
by bounding the ranks of a tuple's finitely many recursive fields).
The union is also where the recursor's semantic fixed point is built
by rank recursion.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace Lech.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

/-- The finite iterates of a set functor from the empty set. -/
noncomputable def iterF (Φ : V → V) : Nat → V
  | 0 => empty
  | n + 1 => Φ (iterF Φ n)

@[simp] theorem iterF_zero (Φ : V → V) : iterF Φ 0 = empty := rfl
@[simp] theorem iterF_succ (Φ : V → V) (n : Nat) : iterF Φ (n + 1) = Φ (iterF Φ n) := rfl

/-- The ω-iterate: the union of the finite iterates. -/
noncomputable def iterU (Φ : V → V) : V :=
  sUnion (image (natFibre (iterF Φ)) omega)

theorem mem_iterU {Φ : V → V} {x : V} : x ∈ˢ iterU Φ ↔ ∃ n, x ∈ˢ iterF Φ n := by
  unfold iterU
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
    obtain ⟨n, rfl, hfib⟩ := natFibre_of_mem (iterF Φ) hk
    rw [hfib] at hxy
    exact ⟨n, hxy⟩
  · rintro ⟨n, hn⟩
    exact ⟨natFibre (iterF Φ) (vnat n), mem_image.mpr ⟨vnat n, vnat_mem_omega n, rfl⟩,
      by rw [natFibre_vnat]; exact hn⟩

theorem iterF_subset_iterU (Φ : V → V) (n : Nat) : iterF Φ n ⊆ˢ iterU Φ :=
  fun _ hx => mem_iterU.mpr ⟨n, hx⟩

/-- Cumulativity, from monotonicity. -/
theorem iterF_mono {Φ : V → V} (hmono : ∀ X Y : V, X ⊆ˢ Y → Φ X ⊆ˢ Φ Y) :
    ∀ {m n : Nat}, m ≤ n → iterF Φ m ⊆ˢ iterF Φ n := by
  intro m n hmn
  induction n with
  | zero =>
    have : m = 0 := Nat.le_zero.mp hmn
    subst this; exact Subset.refl _
  | succ n ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.mp (Nat.lt_succ_of_le hmn) with h | rfl
    · refine Subset.trans (ih (Nat.le_of_lt_succ h)) ?_
      -- `iterF n ⊆ iterF (n+1)`: by induction on `n`
      clear ih h hmn
      induction n with
      | zero => exact empty_subset _
      | succ n ih => exact hmono _ _ ih
    · exact Subset.refl _

/-- **Formation** (graph regime): a countable union of members of a
positive level is a member. -/
theorem iterU_mem_univ_pos {w : Nat} (hw : w ≠ 0) {Φ : V → V}
    (h : ∀ n, iterF Φ n ∈ˢ (univ w : V)) : iterU Φ ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  unfold iterU
  refine (univ_isTGUniverse (Nat.succ_ne_zero w')).famUnion_mem (omega_mem_univ_succ w') ?_
  intro k hk
  obtain ⟨n, rfl, hfib⟩ := natFibre_of_mem (iterF Φ) hk
  rw [hfib]
  exact h n

/-- **Formation** (squash regime): a union of truth values is a truth
value. -/
theorem iterU_mem_univZero {Φ : V → V} (h : ∀ n, iterF Φ n ∈ˢ (univZero : V)) :
    iterU Φ ∈ˢ (univZero : V) := by
  rw [mem_univZero]
  intro x hx
  obtain ⟨n, hn⟩ := mem_iterU.mp hx
  exact (mem_univZero.mp (h n)) x hn

/-- Formation, both regimes. -/
theorem iterU_mem_univ {w : Nat} {Φ : V → V} (h : ∀ n, iterF Φ n ∈ˢ (univ w : V)) :
    iterU Φ ∈ˢ (univ w : V) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [univ_zero] at h ⊢; exact iterU_mem_univZero h
  · exact iterU_mem_univ_pos (Nat.pos_iff_ne_zero.mp hw) h

/-- **Closure** under a finitary functor: if every member of
`Φ (iterU Φ)` lies in some finite stage's image, the ω-iterate is
closed. -/
theorem iterU_closed_of {Φ : V → V}
    (hfin : ∀ x, x ∈ˢ Φ (iterU Φ) → ∃ n, x ∈ˢ Φ (iterF Φ n)) :
    Φ (iterU Φ) ⊆ˢ iterU Φ := by
  intro x hx
  obtain ⟨n, hn⟩ := hfin x hx
  exact mem_iterU.mpr ⟨n + 1, hn⟩

end Lech.SetTheory.Tower
