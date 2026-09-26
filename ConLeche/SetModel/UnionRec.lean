module

public import ConLeche.SetModel.RecGraph
public import ConLeche.SetTheory.Derive.LfpTuple
public import ConLeche.SetModel.TaggedSum
@[expose] public section

/-!
# The disjoint union of a block's values (task #315)

A block of `k` families has ONE recursion: its recursors are the
components of a single function on the **disjoint union of the
block's values**, `unionSet k Is L = { ⟨c, i, x⟩ | c < k, i ∈ Is c,
x ∈ app (L c) i }`.  This module holds that union and its tagged
elements (`tagged`, `unionSet`, `mem_unionSet`); the recursion over it
is `SetModel/GraphRec.lean`'s graph route.

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

open Tower (natFibre natFibre_vnat)

universe u

variable {V : Type u} [SetTheory V]

/-! ## The disjoint union of a tuple's values -/

/-- A value of the union: class `c`, index tuple `i`, value `x`. -/
noncomputable def tagged (c : Nat) (i x : V) : V := kpair (vnat c) (kpair i x)

theorem tagged_inj {c c' : Nat} {i x i' x' : V} (h : tagged c i x = tagged c' i' x') :
    c = c' ∧ i = i' ∧ x = x' := by
  unfold tagged at h
  obtain ⟨h1, h2⟩ := kpair_inj h
  obtain ⟨h3, h4⟩ := kpair_inj h2
  exact ⟨vnat_inj h1, h3, h4⟩

/-- **The disjoint union** of the values of the first `k` components of
a tuple of families. -/
noncomputable def unionSet (k : Nat) (Is : Nat → V) (X : Nat → V) : V :=
  sigmaPairs (sep omega fun c => ∃ n, n < k ∧ c = vnat n)
    (natFibre fun c => sigmaPairs (Is c) fun i => app (X c) i)

theorem mem_unionSet {k : Nat} {Is X : Nat → V} {u : V} :
    u ∈ˢ unionSet k Is X ↔
      ∃ c, c < k ∧ ∃ i, i ∈ˢ Is c ∧ ∃ x, x ∈ˢ app (X c) i ∧ u = tagged c i x := by
  unfold unionSet
  rw [mem_sigmaPairs]
  constructor
  · rintro ⟨t, ht, p, hp, rfl⟩
    obtain ⟨-, n, hn, rfl⟩ := mem_sep.mp ht
    rw [natFibre_vnat] at hp
    obtain ⟨i, hi, x, hx, rfl⟩ := mem_sigmaPairs.mp hp
    exact ⟨n, hn, i, hi, x, hx, rfl⟩
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    refine ⟨vnat c, mem_sep.mpr ⟨vnat_mem_omega c, c, hc, rfl⟩, kpair i x, ?_, rfl⟩
    rw [natFibre_vnat]
    exact mem_sigmaPairs.mpr ⟨i, hi, x, hx, rfl⟩

theorem tagged_mem_unionSet {k : Nat} {Is X : Nat → V} {c : Nat} (hc : c < k) {i x : V}
    (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (X c) i) : tagged c i x ∈ˢ unionSet k Is X :=
  mem_unionSet.mpr ⟨c, hc, i, hi, x, hx, rfl⟩

end ConLeche.SetTheory
