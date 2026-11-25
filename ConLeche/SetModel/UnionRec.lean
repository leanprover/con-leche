module

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

open Tower (boundFibre boundFibre_vnat_lt hasSigmaPairs_boundFibre)

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

theorem DefFun.tagged_apply {p : Nat} (c : Nat) {I X : (Fin p → V) → V}
    (hI : DefFun p I) (hX : DefFun p X) :
    DefFun p fun env => tagged c (I env) (X env) :=
  DefFun.kpair_apply (DefFun.const (vnat c)) (DefFun.kpair_apply hI hX)

theorem hasSep_unionDom (k : Nat) :
    HasSep (omega : V) fun c => ∃ n, n < k ∧ c = vnat n :=
  hasSep_of_defPred <|
    DefRel.finExists_lt fun n _ => DefRel.eq_apply (DefFun.proj 0) (DefFun.const (vnat n))

theorem hasSigmaPairs_app (A X : V) : HasSigmaPairs A (fun i => app X i) :=
  hasSigmaPairs_of_defFun1 (DefFun.app_apply (DefFun.const X) (DefFun.proj 0))

/-- **The disjoint union** of the values of the first `k` components of
a tuple of families. -/
noncomputable def unionSet (k : Nat) (Is : Nat → V) (X : Nat → V) : V :=
  sigmaPairs (sep omega (fun c => ∃ n, n < k ∧ c = vnat n) (hasSep_unionDom k))
    (boundFibre k fun c => sigmaPairs (Is c) (fun i => app (X c) i) (hasSigmaPairs_app (Is c) (X c)))
    (hasSigmaPairs_boundFibre _ k _)

theorem mem_unionSet {k : Nat} {Is X : Nat → V} {u : V} :
    u ∈ˢ unionSet k Is X ↔
      ∃ c, c < k ∧ ∃ i, i ∈ˢ Is c ∧ ∃ x, x ∈ˢ app (X c) i ∧ u = tagged c i x := by
  unfold unionSet
  rw [mem_sigmaPairs]
  constructor
  · rintro ⟨t, ht, p, hp, rfl⟩
    obtain ⟨-, n, hn, rfl⟩ := mem_sep.mp ht
    rw [boundFibre_vnat_lt _ hn] at hp
    obtain ⟨i, hi, x, hx, rfl⟩ := mem_sigmaPairs.mp hp
    exact ⟨n, hn, i, hi, x, hx, rfl⟩
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    refine ⟨vnat c, mem_sep.mpr ⟨vnat_mem_omega c, c, hc, rfl⟩, kpair i x, ?_, rfl⟩
    rw [boundFibre_vnat_lt _ hc]
    exact mem_sigmaPairs.mpr ⟨i, hi, x, hx, rfl⟩

theorem tagged_mem_unionSet {k : Nat} {Is X : Nat → V} {c : Nat} (hc : c < k) {i x : V}
    (hi : i ∈ˢ Is c) (hx : x ∈ˢ app (X c) i) : tagged c i x ∈ˢ unionSet k Is X :=
  mem_unionSet.mpr ⟨c, hc, i, hi, x, hx, rfl⟩

theorem unionSet_congr {k : Nat} {Is Is' X X' : Nat → V}
    (hIs : ∀ c, c < k → Is c = Is' c) (hX : ∀ c, c < k → X c = X' c) :
    unionSet k Is X = unionSet k Is' X' := by
  apply ext fun u => ?_
  rw [mem_unionSet, mem_unionSet]
  constructor
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    exact ⟨c, hc, i, hIs c hc ▸ hi, x, hX c hc ▸ hx, rfl⟩
  · rintro ⟨c, hc, i, hi, x, hx, rfl⟩
    exact ⟨c, hc, i, (hIs c hc).symm ▸ hi, x, (hX c hc).symm ▸ hx, rfl⟩

theorem DefFun.unionSet_apply {p : Nat} (k : Nat) {Is X : Nat → (Fin p → V) → V}
    (hIs : ∀ c, c < k → DefFun p (Is c)) (hX : ∀ c, c < k → DefFun p (X c)) :
    DefFun p fun env => unionSet k (fun c => Is c env) (fun c => X c env) := by
  unfold unionSet
  refine DefFun.sigmaPairs_apply_curry
    (DefFun.const (sep omega (fun c => ∃ n, n < k ∧ c = vnat n) (hasSep_unionDom k))) ?_
  exact DefFun.boundFibre_apply k
    (fun c hc => DefFun.sigmaPairs_apply_curry (hIs c hc).weaken
      (DefFun.app_apply (hX c hc).weaken.weaken (DefFun.proj 0)))
    (DefFun.proj 0)

theorem DefFun.unionSet_const {p : Nat} (k : Nat) (Is X : Nat → V) :
    DefFun p fun _ => unionSet k Is X :=
  DefFun.const _

end ConLeche.SetTheory
