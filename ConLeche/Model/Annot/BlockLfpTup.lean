module

public import ConLeche.Model.Annot.BlockLfpMono
import ConLeche.Semantics.Tower.BlockRecI
import ConLeche.SetTheory.Derive.Univ

public section

/-!
# The tuple order at the hole frame (lane HOLE2, checkpoint (c))

The consumer of positivity (`monoTuple_of_holes`) asks for a frame
relation along which every constructor is positive and which relates
the hole frames of two ordered tuples.  This file names it —
`LfpDatum.tupRel ψ ρp`, the tuple order seen at the hole frame of the
parameter frame `ρp` — and proves, at the level of sets, what
`nestPos`'s monotonicity theorem (`nestMemberCtor_sem`) needs of it:

* the frames agree off the member holes (`tupRel_agreesOff`): the
  parameter frame is the same at both;
* a member's hole grows at its full arity (`holeOn_tupRel`): the hole
  value is a λ-tower over the member's own binders
  (`LfpDatum.holeVal`), a tower of graphs over the SAME domains at both
  frames, whose leaves are the two tuples' components at the index
  tuple — ordered on the index set, both empty off it
  (`holeFam_fold_mono`);
* a hole value inhabits its member's type (`holeFam_mem_mkPisAV`): a
  λ-tower of graphs lies in the Π-tower over the same domains when its
  leaves do — the typing the frame's context needs.

`monoTuple_of_tupRel` is the consumer at this relation.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory
open ConLeche.SetTheory.Tower (projS)

open ConLeche.Semantics (AnnotTerm)
open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## λ-towers of graphs -/

/-- **A λ-tower grows with its leaves**: at any spine of its arity the
applied towers compare as their leaves at the fitting spines (off the
domains both applications are empty). -/
theorem holeFam_fold_mono :
    ∀ {ρ : Nat → V} {Fs : List AnnotTerm} {g g' : List V → V},
      (∀ vs, SpineFit ρ Fs vs → g vs ⊆ˢ g' vs) → ∀ as : List V, as.length = Fs.length →
      as.foldl app (holeFam ρ Fs g) ⊆ˢ as.foldl app (holeFam ρ Fs g')
  | _, [], _, _, h, [], _ => h [] trivial
  | _, [], _, _, _, _ :: _, hl => absurd hl (by simp)
  | _, _ :: _, _, _, _, [], hl => absurd hl (by simp)
  | ρ, F :: Fs, g, g', h, a :: as, hl => by
    show as.foldl app (app (lamR 1 (interp V ρ F) _) a)
      ⊆ˢ as.foldl app (app (lamR 1 (interp V ρ F) _) a)
    by_cases ha : a ∈ˢ interp V ρ F
    · rw [app_lamR_pos (by decide) ha, app_lamR_pos (by decide) ha]
      exact holeFam_fold_mono (fun vs hvs => h (a :: vs) ⟨ha, hvs⟩) as (by simpa using hl)
    · rw [app_lamR_of_not_mem (by decide) ha, app_lamR_of_not_mem (by decide) ha]
      exact Subset.refl _

/-- **A λ-tower inhabits the Π-tower over its domains** when its leaves
inhabit the codomain at every fitting spine (every binder in the graph
regime). -/
theorem holeFam_mem_mkPisAV :
    ∀ {ab : List (Nat × Nat × AnnotTerm)} {ρ : Nat → V} {B : AnnotTerm} {g : List V → V},
      (∀ d ∈ ab, d.2.1 ≠ 0) →
      (∀ vs, SpineFit ρ (ab.map (·.2.2)) vs → g vs ∈ˢ interp V (consList vs ρ) B) →
      holeFam ρ (ab.map (·.2.2)) g ∈ˢ interp V ρ (mkPisAV ab B)
  | [], _, _, _, _, h => h [] trivial
  | x :: ab, ρ, B, g, hb, h => by
    show lamR 1 (interp V ρ x.2.2) _ ∈ˢ piR x.2.1 (interp V ρ x.2.2) _
    rw [lamR_pos (by decide), piR_pos (hb x List.mem_cons_self)]
    refine graph_mem_piSet fun a ha => ?_
    exact holeFam_mem_mkPisAV (fun d hd => hb d (List.mem_cons_of_mem _ hd))
      fun vs hvs => h (a :: vs) ⟨ha, hvs⟩

namespace LfpDatum

variable (D : LfpDatum V)

/-- **The tuple order, seen at the hole frame** of the parameter frame
`ρp`: the frames of two tuples of the space, the first below the
second. -/
@[expose] def tupRel (ψ : Name → Nat) (ρp : Nat → V) : FrameRel V :=
  fun σ σ' => ∃ X Y, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X ∧
    InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) Y ∧ TupleLe D.N (D.idx ψ ρp) X Y ∧
    σ = D.frame ψ ρp X ∧ σ' = D.frame ψ ρp Y

variable {D}

/-- Member `t`'s hole value sits at the variable `nP + t` of the hole
frame (index `k - 1 - t`). -/
theorem frame_hole {ψ : Name → Nat} {ρp X : Nat → V} {t : Nat} (ht : t < D.k) :
    D.frame ψ ρp X (D.k - 1 - t) = D.holeVal ψ ρp X t := by
  unfold frame
  rw [consList_getD_of_lt _ _ _ (by simp; omega)]
  simp only [List.length_map, List.length_range, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range (show D.k - 1 - (D.k - 1 - t) < D.k by omega)]
  rw [show D.k - 1 - (D.k - 1 - t) = t by omega]
  rfl

/-- Above the holes the hole frame is the parameter frame. -/
theorem frame_param {ψ : Name → Nat} {ρp X : Nat → V} (i : Nat) :
    D.frame ψ ρp X (i + D.k) = ρp i := by
  unfold frame
  have := consList_apply_add ((List.range D.k).map (D.holeVal ψ ρp X)) ρp i
  simpa using this


/-- The hole frame's parameter values are the parameter frame's. -/
theorem holeParamVals_frame (ψ : Name → Nat) (ρp X : Nat → V) (nP : Nat) :
    holeParamVals D.k nP 0 (D.frame ψ ρp X) = frameIdx nP ρp := by
  unfold holeParamVals frameIdx LfpDatum.frame
  refine List.map_congr_left fun p hp => ?_
  have hp' := List.mem_range.mp hp
  have hlen : ((List.range D.k).map (D.holeVal ψ ρp X)).length = D.k := by simp
  rw [show 0 + D.k + nP - 1 - p = (nP - 1 - p) + ((List.range D.k).map (D.holeVal ψ ρp X)).length
    by rw [hlen]; omega, consList_apply_add]

/-- **A frame agreeing with the hole frame at the holes**: the parameter
frame below, and member slots whose values, applied to the parameters
and anything, are the hole values'. -/
theorem holeAgree_frame {ψ : Name → Nat} {ρp X : Nat → V} {nP : Nat} {vs : List V}
    (hlen : vs.length = D.k)
    (hv : ∀ m (hm : m < D.k) (is : List V), (frameIdx nP ρp ++ is).foldl app (D.holeVal ψ ρp X m)
      = (frameIdx nP ρp ++ is).foldl app (vs[m]'(by rw [hlen]; exact hm))) :
    HoleAgree D.k nP 0 (D.frame ψ ρp X) (consList vs ρp) := by
  have hlenF : ((List.range D.k).map (D.holeVal ψ ρp X)).length = D.k := by simp
  refine ⟨fun i hi => ?_, fun h _ h2 is => ?_⟩
  · obtain ⟨i', rfl⟩ : ∃ i', i = i' + D.k := ⟨i - D.k, by omega⟩
    have e1 := consList_apply_add ((List.range D.k).map (D.holeVal ψ ρp X)) ρp i'
    rw [hlenF] at e1
    have e2 := consList_apply_add vs ρp i'
    rw [hlen] at e2
    show consList _ ρp (i' + D.k) = consList vs ρp (i' + D.k)
    rw [e1, e2]
  · rw [holeParamVals_frame]
    obtain ⟨m, hm, rfl⟩ : ∃ m, m < D.k ∧ h = D.k - 1 - m := ⟨D.k - 1 - h, by omega, by omega⟩
    rw [frame_hole (ψ := ψ) (ρp := ρp) (X := X) hm, hv m hm is, consList_getD_of_lt vs ρp _ (by rw [hlen]; omega)]
    have hidx : vs.length - 1 - (D.k - 1 - m) = m := by rw [hlen]; omega
    rw [hidx, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlen]; exact hm)]
    rfl

/-- **The hole fit, at an agreeing frame**: a spine fits a constructor's
fields with holes at the hole frame exactly when it fits them at any
frame agreeing with it at the holes (M3), its result index readings
likewise. -/
theorem hfits_iff_of_holeAgree {ψ : Name → Nat} {ρp X : Nat → V} {c j : Nat}
    (hha : D.HolesApplied ψ c j) {σ : Nat → V}
    (hag : HoleAgree D.k (D.params ψ).length 0 (D.frame ψ ρp X) σ) {t : V} {fs : List V} :
    D.HFits ψ ρp X t c j fs ↔
      (j < D.nctors c ∧ SpineFit σ (D.fields ψ c j) fs ∧
        ∀ l, l < (D.ids c ψ).length → ∃ e, (D.resIdx ψ c j)[l]? = some e ∧
          interp V (consList fs σ) e = projS l t) := by
  have hsp : SpineFit (D.frame ψ ρp X) (D.fields ψ c j) fs ↔ SpineFit σ (D.fields ψ c j) fs :=
    spineFit_congr_holeApp _ (fun l F h => by simpa using hha.1 l F h) hag fs
  unfold HFits
  constructor
  · rintro ⟨hj, hs, hr⟩
    refine ⟨hj, hsp.mp hs, fun l hl => ?_⟩
    obtain ⟨e, he, heq⟩ := hr l hl
    refine ⟨e, he, ?_⟩
    rw [← heq]
    have hfl : fs.length = (D.fields ψ c j).length := hs.length_eq
    have hag' := hag.consList fs
    rw [Nat.zero_add, hfl] at hag'
    exact (interp_congr_holeApp (hha.2 e (List.mem_of_getElem? he)) hag').symm
  · rintro ⟨hj, hs, hr⟩
    refine ⟨hj, hsp.mpr hs, fun l hl => ?_⟩
    obtain ⟨e, he, heq⟩ := hr l hl
    refine ⟨e, he, ?_⟩
    rw [← heq]
    have hfl : fs.length = (D.fields ψ c j).length := hs.length_eq
    have hag' := hag.consList fs
    rw [Nat.zero_add, hfl] at hag'
    exact interp_congr_holeApp (hha.2 e (List.mem_of_getElem? he)) hag'


/-- **The frames agree off the member holes.** -/
theorem tupRel_agreeOff {ψ : Name → Nat} {ρp : Nat → V} {σ σ' : Nat → V}
    (h : D.tupRel ψ ρp σ σ') : ∀ i, D.k ≤ i → σ i = σ' i := by
  obtain ⟨X, Y, -, -, -, rfl, rfl⟩ := h
  intro i hi
  obtain ⟨j, rfl⟩ : ∃ j, i = j + D.k := ⟨i - D.k, by omega⟩
  rw [frame_param, frame_param]

/-- **A member's hole grows at its full arity** along the tuple order. -/
theorem holeOn_tupRel (hkN : D.k ≤ D.N) {ψ : Name → Nat} {ρp : Nat → V} {t : Nat}
    (ht : t < D.k) :
    HoleOn (D.tupRel ψ ρp) (D.k - 1 - t) ((D.pars t ψ).length + (D.ids t ψ).length) := by
  rintro _ _ ⟨X, Y, hX, hY, hXY, rfl, rfl⟩ as has
  rw [frame_hole ht, frame_hole ht]
  have htN : t < D.N := Nat.lt_of_lt_of_le ht hkN
  unfold holeVal
  refine holeFam_fold_mono (fun vs _ => ?_) as (by simpa using has)
  by_cases hT : tupW (D.u t ψ) (vs.drop (D.pars t ψ).length) ∈ˢ D.idx ψ ρp t
  · exact hXY t htN _ hT
  · rw [app_off_dom_of_mem_piSet (hX t htN) hT, app_off_dom_of_mem_piSet (hY t htN) hT]
    exact Subset.refl _

/-- **A hole value inhabits its member's type**, read as the Π-tower over
the member's binders ending in the block's sort. -/
theorem holeVal_mem (hkN : D.k ≤ D.N) {ψ : Name → Nat} {ρp X : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) {t : Nat} (ht : t < D.k)
    {ab : List (Nat × Nat × AnnotTerm)} (hab : ab.map (·.2.2) = D.pars t ψ ++ D.ids t ψ)
    (hbits : ∀ d ∈ ab, d.2.1 ≠ 0) :
    D.holeVal ψ ρp X t
      ∈ˢ interp V (shiftE (D.pars t ψ).length 0 ρp) (mkPisAV ab (.sort (D.w ψ))) := by
  have htN : t < D.N := Nat.lt_of_lt_of_le ht hkN
  unfold holeVal
  rw [← hab]
  refine holeFam_mem_mkPisAV hbits fun vs _ => ?_
  rw [interp_sort]
  by_cases hT : tupW (D.u t ψ) (vs.drop (D.pars t ψ).length) ∈ˢ D.idx ψ ρp t
  · exact app_mem_of_mem_piSet (hX t htN) hT
  · rw [app_off_dom_of_mem_piSet (hX t htN) hT]
    exact empty_mem_univ _

end LfpDatum

/-- **The consumer at the tuple order**: the operator is monotone as
soon as every constructor is positive along `tupRel`. -/
theorem monoTuple_of_tupRel {D : LfpDatum V} (hrd : D.ReadsHoles)
    {ψ : Name → Nat} {ρp : Nat → V} (hs : Sat V (D.params ψ).reverse ρp)
    (hfib : ∀ X, InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X → ∀ c, c < D.N →
      ∀ t, t ∈ˢ D.idx ψ ρp c → ∀ x,
        x ∈ˢ app (D.Φ ψ ρp X c) t ↔ ∃ j fs, D.fits ψ ρp X t c j fs ∧ x = D.inj ψ c j fs)
    (hpos : ∀ c, c < D.N → ∀ j, j < D.nctors c → D.CtorPos (D.tupRel ψ ρp) ψ c j) :
    MonoTuple (D.w ψ) D.N (D.idx ψ ρp) (D.Φ ψ ρp) :=
  monoTuple_of_holes hrd hs hfib _ (fun X Y hX hY hXY => ⟨X, Y, hX, hY, hXY, rfl, rfl⟩) hpos

end ConLeche.Model
