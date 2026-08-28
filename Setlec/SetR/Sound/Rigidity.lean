import Setlec.SetR.Sound.Motives

/-!
# Pinned-value rigidity (task #148, T4)

The off-domain-emptiness eliminations behind "semantic domain
determination" (the T4 architecture record's I9/D12 resolution):
membership in an application of the pinned pair former either
contradicts (an off-domain application of a non-`pt` `lamC` is the
empty set) or self-certifies the argument domains and folds to a
`sigmaSet`.  The `ne_pt` witnesses transpose
`Setlec/Model/BasisLemmas.lean`'s (`psigmaVal_ne_pt` etc.) onto the
`TT/Semantics` values, which are the same collapse towers.
-/

namespace Setlec.SetR

open Setlec.TT
open SetTheory

universe w

variable {V : Type w} [SetTheory V]

/-- An off-domain application of a non-collapsed abstraction is empty
(the graph's canonical off-domain behavior). -/
theorem app_lamC_of_not_mem {A a : V} {F : V → V}
    (hne : lamC A F ≠ pt) (ha : ¬ a ∈ˢ A) :
    SetTheory.app (lamC A F) a = SetTheory.empty := by
  have hnot : ¬ ∀ x, x ∈ˢ A → F x = pt := fun h => hne (lamC_of_forall h)
  rw [lamC_of_not hnot]
  exact app_graph_of_not_mem ha

/-- The pair former never collapses (transpose of `psigmaVal_ne_pt`). -/
theorem psigmaV_ne_pt {u v : Nat} : psigmaV V u v ≠ pt := by
  refine lamC_ne_pt_of_witness (empty_mem_univ u) ?_
  refine lamC_ne_pt_of_witness (x := pt) ?_ sigmaSet_ne_pt
  rw [piC_empty]
  exact pt_mem_unitSet

/-- Nor does its partial application's body, at any domain value
(transpose of `psigmaVal_inner_ne_pt`). -/
theorem psigmaV_inner_ne_pt {u v : Nat} {vA : V} :
    lamC (piC vA fun _ => (univ v : V))
      (fun B => sigmaSet (Nat.max u v) vA fun x => SetTheory.app B x)
      ≠ pt :=
  lamC_ne_pt_of_witness
    (lamC_mem fun _x _hx => empty_mem_univ v) sigmaSet_ne_pt

/-- The rigidity elimination: a member of the pinned pair former's
double application certifies the arguments' canonical domains and the
`sigmaSet` fold — or there is no member at all.  This is the
"membership self-certifies the domains" discharge of I9/D12 (the T4
architecture record); its off-domain branches replace the tt-only
`projParamCert` (#129/#130). -/
theorem mem_psigmaV_app {u v : Nat} {vA vB x : V}
    (hx : x ∈ˢ SetTheory.app (SetTheory.app (psigmaV V u v) vA) vB) :
    vA ∈ˢ (univ u : V) ∧ vB ∈ˢ piC vA (fun _ => (univ v : V)) ∧
    x ∈ˢ sigmaSet (Nat.max u v) vA (fun y => SetTheory.app vB y) := by
  by_cases hA : vA ∈ˢ (univ u : V)
  · rw [psigmaV, app_lamC hA] at hx
    by_cases hB : vB ∈ˢ piC vA (fun _ => (univ v : V))
    · rw [app_lamC hB] at hx
      exact ⟨hA, hB, hx⟩
    · rw [app_lamC_of_not_mem psigmaV_inner_ne_pt hB] at hx
      exact absurd hx (not_mem_empty x)
  · rw [show SetTheory.app (psigmaV V u v) vA = SetTheory.empty from
        app_lamC_of_not_mem psigmaV_ne_pt hA, app_empty] at hx
    exact absurd hx (not_mem_empty x)

/-- The pair constructor collapses at the `Prop` level (transpose of
`PairMkFacts.zero`'s witness). -/
theorem psigmaMkV_zero {u v : Nat} (h : Nat.max u v = 0) :
    psigmaMkV V u v = pt := by
  rw [psigmaMkV]
  refine lamC_of_forall fun A _hA => ?_
  refine lamC_of_forall fun B _hB => ?_
  refine lamC_of_forall fun a _ha => ?_
  refine lamC_of_forall fun b _hb => ?_
  rw [if_pos h]

end Setlec.SetR
