module

public import ConLeche.SetModel.Access

public section

/-!
# Why the least-fixed-point constructions drop a fibre (task #342)

An intersection of types need not be a type: `{ptTag, ∅}` and
`{ptTag, {∅}}` are strict and their intersection is the point — the two
closed fibres of `F X i = if ∅ ∈ X i then {ptTag, ∅} else {ptTag, {∅}}`.
Over the strict universe (`strictU`, the least fixed points' fibre
space) `lfpFamIn`/`lfpTuple` drop such a fibre to `∅` (`dropTo`).

And why the fibre space is `strictU`, not the universe of types `univ`
(task #342 stage S1): `univ` is cumulative, so `True = {pt}` is a type
of every level, but `{pt}` with `∅` added is no type — the adjunction
of `∅` (and the unions) would fail.
-/

namespace ConLeche.SetTheory.LfpTypesTest

universe u

variable {V : Type u} [SetTheory V]

/-! ## The countermodel: an intersection of strict sets can be the point -/

theorem ptTag_ne_empty : (ptTag : V) ≠ empty := fun h =>
  not_mem_empty _ (h ▸ empty_mem_ptTag)

theorem ptTag_ne_pt : (ptTag : V) ≠ pt := fun h =>
  ptTag_ne_empty (mem_pt.mp (h ▸ empty_mem_ptTag)).symm

theorem strict_pair {a : V} (ha : a ≠ ptTag) (hpa : a ≠ pt) : Strict (upair ptTag a : V) := by
  refine ⟨fun h => ha (mem_pt.mp (h ▸ mem_upair.mpr (Or.inr rfl))), fun hp => ?_⟩
  rcases mem_upair.mp hp with h | h
  · exact ptTag_ne_pt h.symm
  · exact hpa h.symm

/-- `{ptTag, ∅}` and `{ptTag, {∅}}` are strict, and their intersection is
the point: the closed fibres of `F X i = if ∅ ∈ X i then {ptTag, ∅} else
{ptTag, {∅}}`, whose raw least fibre is therefore not a type. -/
theorem hasSep_countermodel :
    HasSep (upair ptTag empty : V) (fun x => x ∈ˢ upair ptTag (sing empty)) :=
  hasSep_of_defPred
    (DefRel.mem_apply (DefFun.proj 0) (DefFun.const (upair ptTag (sing empty))))

theorem countermodel :
    Strict (upair ptTag empty : V) ∧ Strict (upair ptTag (sing empty) : V) ∧
      sep (upair ptTag empty : V) (fun x => x ∈ˢ upair ptTag (sing empty))
        hasSep_countermodel = pt := by
  have hs0 : (sing empty : V) ≠ ptTag := fun h => ptTag_ne_sing empty h.symm
  have hspt : (sing empty : V) ≠ pt := fun h =>
    ptTag_ne_empty (mem_sing.mp (h ▸ ptTag_mem_pt : (ptTag : V) ∈ˢ sing empty))
  refine ⟨strict_pair ptTag_ne_empty.symm pt_ne_empty.symm, strict_pair hs0 hspt, ?_⟩
  refine Subset.antisymm (fun x hx => ?_) (fun x hx => ?_)
  · obtain ⟨h1, h2⟩ := mem_sep.mp hx
    rcases mem_upair.mp h1 with rfl | rfl
    · exact ptTag_mem_pt
    · rcases mem_upair.mp h2 with h | h
      · exact absurd h.symm ptTag_ne_empty
      · have h0 : (empty : V) ∈ˢ sing empty := mem_sing.mpr rfl
        rw [← h] at h0
        exact absurd h0 (not_mem_empty _)
  · rw [mem_pt.mp hx]
    exact mem_sep.mpr ⟨mem_upair.mpr (Or.inl rfl), mem_upair.mpr (Or.inl rfl)⟩

/-- At a positive level the drop sends that intersection to `∅`. -/
example {w : Nat} (hw : w ≠ 0) :
    dropTo (strictU w)
        (sep (upair ptTag empty : V) (fun x => x ∈ˢ upair ptTag (sing empty))
          hasSep_countermodel)
      = empty := by
  rw [countermodel.2.2]
  unfold dropTo
  rw [ite_eq_right fun h => ((mem_strictU_pos hw).mp h).2.1 rfl]

/-! ## The universe of types is cumulative, but not closed under `∪ {∅}` -/

/-- Cumulativity: `True = {pt}` is a type of `Sort 1`. -/
example : (unitSet : V) ∈ˢ (univ 1 : V) := univ_mono (Nat.zero_le 1) _ (unitSet_mem_univ 0)

/-- `{pt} ∪ {∅}` is not a type: it holds the point and `∅`, so it is
neither a truth value nor strict. -/
example : ¬ (binUnion unitSet (sing empty) : V) ∈ˢ (univ 1 : V) := by
  intro h
  rcases IsTy_of_mem_univ h with h0 | hs
  · have he : (empty : V) ∈ˢ unitSet :=
      mem_univZero.mp h0 _ (mem_binUnion.mpr (Or.inr (mem_sing.mpr rfl)))
    exact pt_ne_empty (mem_unitSet_iff.mp he).symm
  · exact hs.2 (mem_binUnion.mpr (Or.inl pt_mem_unitSet))

end ConLeche.SetTheory.LfpTypesTest
