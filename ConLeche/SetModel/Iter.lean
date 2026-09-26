module

public import ConLeche.SetModel.TaggedSum

@[expose] public section

/-!
# Finite iterates and countable unions (task #188)

The finite iterates of a set functor from the empty set,

    iterF Φ 0 = ∅,   iterF Φ (n+1) = Φ (iterF Φ n),

and the countable union `natUnion f = ⋃ₙ f n`, a member of `univ w` at
`w ≥ 1` when every `f n` is (`ω ∈ univ w`, `omega_mem_univ_succ`).
(The ω-iterate `iterU` and its closure lemma, the closed-member witness
of the retired single-set `lfpSet`, are retired with it — lane DMASTER.)

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

/-- The finite iterates of a set functor from the empty set. -/
noncomputable def iterF (Φ : V → V) : Nat → V
  | 0 => empty
  | n + 1 => Φ (iterF Φ n)

@[simp] theorem iterF_zero (Φ : V → V) : iterF Φ 0 = empty := rfl
@[simp] theorem iterF_succ (Φ : V → V) (n : Nat) : iterF Φ (n + 1) = Φ (iterF Φ n) := rfl

/-- The union of a countable family `f 0 ∪ f 1 ∪ …` (the ω-indexed union
through the tag fibre). -/
noncomputable def natUnion (f : Nat → V) : V :=
  sUnion (image (natFibre f) omega)

theorem mem_natUnion {f : Nat → V} {x : V} : x ∈ˢ natUnion f ↔ ∃ n, x ∈ˢ f n := by
  unfold natUnion
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
    obtain ⟨n, rfl, hfib⟩ := natFibre_of_mem f hk
    rw [hfib] at hxy
    exact ⟨n, hxy⟩
  · rintro ⟨n, hn⟩
    exact ⟨natFibre f (vnat n), mem_image.mpr ⟨vnat n, vnat_mem_omega n, rfl⟩,
      by rw [natFibre_vnat]; exact hn⟩

/-- **Formation** (graph regime): a countable union of members of a
positive level is a member. -/
theorem natUnion_mem_univ_pos {w : Nat} (hw : w ≠ 0) {f : Nat → V}
    (h : ∀ n, f n ∈ˢ (univ w : V)) : natUnion f ∈ˢ (univ w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  unfold natUnion
  refine (univ_isTGUniverse (Nat.succ_ne_zero w')).famUnion_mem (omega_mem_univ_succ w') ?_
  intro k hk
  obtain ⟨n, rfl, hfib⟩ := natFibre_of_mem f hk
  rw [hfib]
  exact h n

end ConLeche.SetTheory.Tower
