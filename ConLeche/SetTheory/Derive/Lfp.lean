module

public import ConLeche.SetTheory.Derive.Univ

@[expose] public section

/-!
# Universe helpers for the least-fixed-point constructions

A subset of a member of `univ w` is a member, and separation stays
inside every level: the two facts the least pre-fixed families and
tuples (`Derive/LfpFam.lean`, `Derive/LfpTuple.lean`) take their
carriers' formation from.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Universe helpers -/

/-- A subset of a member of `univ w` is a member: at `w = 0` members of
`univZero` are the subsets of `unitSet`; above, the Grothendieck
clause. -/
theorem univ_mem_of_subset_mem {w : Nat} {y z : V} (hy : y ∈ˢ (univ w : V)) (hz : z ⊆ˢ y) :
    z ∈ˢ (univ w : V) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [univ_zero] at hy ⊢
    rw [mem_univZero] at hy ⊢
    exact hz.trans hy
  · exact (univ_isTGUniverse (Nat.pos_iff_ne_zero.mp hw)).mem_of_subset_mem hy hz

/-- Separation stays inside every level. -/
theorem univ_sep_mem {w : Nat} {a : V} {p : V → Prop} (ha : a ∈ˢ (univ w : V)) :
    sep a p ∈ˢ (univ w : V) :=
  univ_mem_of_subset_mem ha sep_subset

end ConLeche.SetTheory
