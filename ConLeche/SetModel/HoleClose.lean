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
theorem lfpTuple_le_on {hΦ : DefTupleOp k Φ} (h : ∃ L, IsClosedTuple w k Is Φ L)
    (hmono : MonoTuple w k Is Φ) (hmaps : MapsTuple w k Is Φ)
    (G : Nat → Prop) {B : Nat → V} (hB : InTupleSpace w k Is B)
    (hZ : ∀ g, g < k → G g →
      FamLe (Is g) (Φ (fun x => if G x then B x else lfpTuple w k Is Φ hΦ x) g) (B g)) :
    ∀ g, g < k → G g → FamLe (Is g) (lfpTuple w k Is Φ hΦ g) (B g) := by
  let P : Nat → V → V → Prop := fun m i x => G m → x ∈ˢ app (B m) i
  have hPdef : ∀ m, m < k → DefRel 2 fun v => P m (v 0) (v 1) := fun m _ => by
    dsimp only [P]
    by_cases hg : G m
    · exact (DefRel.mem_apply (DefFun.proj 1)
        (DefFun.app_apply (DefFun.const (B m)) (DefFun.proj 0))).congr fun _ =>
          ⟨fun h _ => h, fun h => h hg⟩
    · exact DefRel.true.congr fun _ =>
        ⟨fun _ hgm => absurd hgm hg, fun _ => trivial⟩
  have hZmem : InTupleSpace w k Is (fun x => if G x then B x else lfpTuple w k Is Φ hΦ x) := by
    intro m hm
    by_cases hg : G m
    · simp only [ite_eq_left hg]; exact hB m hm
    · simp only [ite_eq_right hg]; exact lfpTuple_mem w k Is Φ hΦ m hm
  have hSZ : TupleLe k Is (sepTuple_of_def w k Is Φ hΦ P hPdef)
      (fun x => if G x then B x else lfpTuple w k Is Φ hΦ x) := by
    intro m hm i hi y hy
    have hy' := mem_app_sepTuple_imp hi hy
    by_cases hg : G m
    · simp only [ite_eq_left hg]; exact hy'.2 hg
    · simp only [ite_eq_right hg]; exact hy'.1
  have hind := lfpTuple_induction_of_def h hmono hmaps P hPdef fun m hm i hi x hx hg => by
    have hSmem := sepTuple_mem w k Is Φ hΦ P
      (hasSep_sepTuple_of_def hΦ hPdef) (hasGraph_sepTuple_of_def hΦ hPdef)
    have hx' := hmono _ _ hSmem hZmem hSZ m hm i hi x hx
    exact hZ m hm hg i hi x hx'
  intro g hg hG i hi x hx
  exact hind g hg i hi x hx hG

end OnGroup

end ConLeche.SetTheory
