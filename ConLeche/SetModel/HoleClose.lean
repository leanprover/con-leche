module

public import ConLeche.SetTheory.Derive.LfpTuple
@[expose] public section

/-!
# Closing the holes: the least tuple below a bound, on a group

The set-level half of the CONTAINER case of "positivity ⇒ monotone"
(charter items 2–4, 8).  A container instance `C (t[X])` is read, by
`C`'s lfp clause, as a component of the least pre-fixed tuple of `C`'s
operator at the parameter frame `⟦t[X]⟧`.  Its monotonicity in the
outer holes `X` is NOT a property of `C` (charter item 4): it is
positivity at the instantiation (the term-level supplier is
`Semantics/Inductives/HoleMono.lean`) plus leastness.

* `tupleLe_of_fibre` — two tuples compare as soon as their components'
  fibre laws' fit relations do;
* `lfpTuple_le_on` — the least tuple lies below `B` on a group `G` of
  its components as soon as the operator, at the least tuple with its
  `G`-components replaced by `B`'s, does: a container frame abstracts
  only the reached part of its group, the rest is read concretely.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

section Fibre

variable {k : Nat} {Is : Nat → V}

/-- **Operators compared through their fibre laws.**  Two tuples whose
components' fibres are the injections of the spines satisfying `fits₁`,
resp. `fits₂`, compare as soon as the fit relations do.  This is how a
positivity fact about the constructors' field readings (a fit relation
growing) becomes a comparison of operator values — at two tuples (the
operator's own monotonicity) or at two parameter frames (a container's
instance). -/
theorem tupleLe_of_fibre {A B : Nat → V} {fits₁ fits₂ : V → Nat → Nat → List V → Prop}
    {inj : Nat → Nat → List V → V}
    (h₁ : ∀ c, c < k → ∀ t, t ∈ˢ Is c → ∀ x,
      x ∈ˢ app (A c) t ↔ ∃ j fs, fits₁ t c j fs ∧ x = inj c j fs)
    (h₂ : ∀ c, c < k → ∀ t, t ∈ˢ Is c → ∀ x,
      x ∈ˢ app (B c) t ↔ ∃ j fs, fits₂ t c j fs ∧ x = inj c j fs)
    (hfits : ∀ c, c < k → ∀ t, t ∈ˢ Is c → ∀ j fs, fits₁ t c j fs → fits₂ t c j fs) :
    TupleLe k Is A B := by
  intro c hc t ht x hx
  obtain ⟨j, fs, hf, rfl⟩ := (h₁ c hc t ht x).mp hx
  exact (h₂ c hc t ht _).mpr ⟨j, fs, hfits c hc t ht j fs hf, rfl⟩

end Fibre

section OnGroup

variable {w k : Nat} {Is : Nat → V} {Φ : (Nat → V) → Nat → V}

open Classical in
/-- **The least tuple lies below `B` on a group `G` of components**
(a container frame abstracts only the reached part `G` of its group;
the other components are held at the least tuple itself): if the operator, at the least tuple with its
`G`-components replaced by `B`'s, lies below `B` on `G`, then so does
the least tuple.  By induction (`lfpTuple_induction`) at the separation
"on `G`, inside `B`": no Bekić needed. -/
theorem lfpTuple_le_on (h : ∃ L, IsClosedTuple w k Is Φ L) (hmono : MonoTuple w k Is Φ)
    (G : Nat → Prop) {B : Nat → V} (hB : InTupleSpace w k Is B)
    (hZ : ∀ g, g < k → G g →
      FamLe (Is g) (Φ (fun x => if G x then B x else lfpTuple w k Is Φ x) g) (B g)) :
    ∀ g, g < k → G g → FamLe (Is g) (lfpTuple w k Is Φ g) (B g) := by
  let P : Nat → V → V → Prop := fun m i x => G m → x ∈ˢ app (B m) i
  have hZmem : InTupleSpace w k Is (fun x => if G x then B x else lfpTuple w k Is Φ x) := by
    intro m hm
    by_cases hg : G m
    · simp only [ite_eq_left hg]; exact hB m hm
    · simp only [ite_eq_right hg]; exact lfpTuple_mem w k Is Φ m hm
  have hSZ : TupleLe k Is (sepTuple w k Is Φ P)
      (fun x => if G x then B x else lfpTuple w k Is Φ x) := by
    intro m hm i hi y hy
    have hy' := hy
    unfold sepTuple at hy'
    rw [app_graph hi, mem_sep] at hy'
    by_cases hg : G m
    · simp only [ite_eq_left hg]; exact hy'.2 hg
    · simp only [ite_eq_right hg]; exact hy'.1
  have hind := lfpTuple_induction h hmono P fun m hm i hi x hx hg => by
    have hx' := hmono _ _ (sepTuple_mem w k Is Φ P) hZmem hSZ m hm i hi x hx
    exact hZ m hm hg i hi x hx'
  intro g hg hG i hi x hx
  exact hind g hg i hi x hx hG

end OnGroup

end ConLeche.SetTheory
