module

public import ConLeche.SetTheory.Derive.Tg

@[expose] public section

/-!
# Level helpers for the least-fixed-point constructions

A subset of a member of the axiomatic level `tg w` is a member, and
separation stays inside every level: the size bounds the least
pre-fixed families and tuples (`Derive/LfpFam.lean`,
`Derive/LfpTuple.lean`) take their carriers' formation from.  They are
stated at `tg`, not at `univ`: a subset of a type need not be a type
(task #342; the fibre space's own closure is `DropClosed`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Level helpers -/

/-- A subset of a member of `tg w` is a member: at `w = 0` members of
`univZero` are the subsets of `unitSet`; above, the Grothendieck
clause. -/
theorem tg_mem_of_subset_mem {w : Nat} {y z : V} (hy : y ∈ˢ (tg w : V)) (hz : z ⊆ˢ y) :
    z ∈ˢ (tg w : V) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · rw [tg_zero] at hy ⊢
    rw [mem_univZero] at hy ⊢
    exact hz.trans hy
  · exact (tg_isGrothendieck (Nat.pos_iff_ne_zero.mp hw)).mem_of_subset_mem hy hz

theorem tg_sep_mem {w : Nat} {a : V} {p : V → Prop}
    (ha : a ∈ˢ (tg w : V)) (h : HasSep a p) : sep a p h ∈ˢ (tg w : V) :=
  tg_mem_of_subset_mem ha sep_subset

end ConLeche.SetTheory
