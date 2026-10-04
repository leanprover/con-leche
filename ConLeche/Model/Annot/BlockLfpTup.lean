module

public import ConLeche.Model.Annot.BlockLfp

public section

/-!
# The hole frame's values

What the walks need of the hole frame, at the level of sets:

* it reads the member holes and the parameters (`frame_hole`,
  `frame_param`);
* a hole value inhabits its member's type (`holeFam_mem_mkPisAV`,
  `LfpDatum.holeVal_mem`): a λ-tower of graphs lies in the Π-tower over
  the same domains when its leaves do — the typing the frame's context
  needs.
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

/-- **A hole value inhabits its member's hole type**, read at the
parameter frame as the Π-tower over the member's indices ending in the
block's sort. -/
theorem holeVal_mem (hkN : D.k ≤ D.N) {ψ : Name → Nat} {ρp X : Nat → V}
    (hX : InTupleSpace (D.w ψ) D.N (D.idx ψ ρp) X) {t : Nat} (ht : t < D.k)
    {ab : List (Nat × Nat × AnnotTerm)} (hab : ab.map (·.2.2) = D.ids t ψ)
    (hbits : ∀ d ∈ ab, d.2.1 ≠ 0) :
    D.holeVal ψ ρp X t ∈ˢ interp V ρp (mkPisAV ab (.sort (D.w ψ))) := by
  have htN : t < D.N := Nat.lt_of_lt_of_le ht hkN
  unfold holeVal
  rw [← hab]
  refine holeFam_mem_mkPisAV hbits fun vs _ => ?_
  rw [interp_sort]
  by_cases hT : tupW (D.u t ψ) vs ∈ˢ D.idx ψ ρp t
  · exact app_mem_of_mem_piSet (hX t htN) hT
  · rw [app_off_dom_of_mem_piSet (hX t htN) hT]
    exact empty_mem_univ _

end LfpDatum

end ConLeche.Model
