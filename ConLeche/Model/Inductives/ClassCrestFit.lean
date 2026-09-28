module

public import ConLeche.Model.Inductives.ClassHFits
public import ConLeche.Model.Inductives.ClassSpace

public section

/-!
# A crest's fit grows with the holes (P2d, DESIGN CLASSCHECK / P2D4)

T4's monotonicity (`classCtorWalk_mono`: every field monotone under the
earlier ones, the result's indices hole-free, along a hole relation) makes
a crest's fit (`CrestFitAt`) grow along the relation: the fields by
`spineFit_mono`, the result's index readings constant under a spine
fitting both frames (`crestFitAt_mono`).  At the class facts' valuation
space the relation is its hole order (`classHoleRel_tupRel`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower (projS)
open ConLeche.Semantics (AnnotTerm)

universe w

variable {V : Type w} [SetTheory V]

/-- **A crest's fit grows along a relation it is positive along.** -/
theorem crestFitAt_mono {R : FrameRel V} {ab : List (Nat × Nat × AnnotTerm)} {r : AnnotTerm}
    (hpos : PiPosThen (ResultIdxConst 0) ab.length R (mkPisAV ab r)) {ρ ρ' : Nat → V}
    (hR : R ρ ρ') {t : V} {fs : List V} (h : CrestFitAt ρ ab r t fs) : CrestFitAt ρ' ab r t fs := by
  obtain ⟨htm, i, vs, hr, hc⟩ := piPosThen_mkPisAV ab R r hpos
  obtain ⟨hsp, i', vs', hr', hvals⟩ := h
  obtain ⟨-, rfl⟩ := mkAppN_bvar_inj (hr.symm.trans hr')
  refine ⟨spineFit_mono _ htm hR hsp, i', vs, hr', fun l hl => ?_⟩
  have hmem : vs.getD l default ∈ vs.drop 0 := by
    rw [List.drop_zero, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hl, Option.getD_some]
    exact List.getElem_mem hl
  rw [← hc _ hmem _ _ (FrameRel.underTele_consList _ fs hR hsp)]
  exact hvals l hl

end ConLeche.Model
