module

public import ConLeche.Model.Env.BlockLfp

public section

/-!
# The hole frame's values

What the walks need of the hole frame, at the level of sets:

* it reads the member holes and the parameters (`frame_hole`,
  `frame_param`);
* a hole value inhabits its member's type (`holeFam_mem_mkPisAV`,
  `LfpDatum.holeVal_mem`): a λ-tower lies in the Π-tower over the same
  domains when its leaves do — the typing the frame's context needs.
-/

namespace ConLeche.Model
open ConLeche.Term (Term)
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.SetTheory
open SetTheory
open ConLeche.SetTheory.Tower (projS)


open ConLeche (Name Level)

universe w

variable {V : Type w} [SetTheory V]

/-! ## λ-towers -/

/-- **A λ-tower inhabits the Π-tower over its domains** when its leaves
inhabit the codomain at every fitting spine and the codomain is a type
there (`lamV_mem`: the fibres are types — inner Π-types, or the
codomain). -/
theorem holeFam_mem_mkPisAV :
    ∀ {ab : List Term} {ρ : Nat → V} {B : Term} {g : List V → V} {hg : DefHoleFn ab.length g},
      (∀ vs, SpineFit ρ ab vs → g vs ∈ˢ interp V (consList vs ρ) B) →
      (∀ vs, SpineFit ρ ab vs → IsTy (interp V (consList vs ρ) B)) →
      holeFam ρ ab g hg ∈ˢ interp V ρ (mkPisAV ab B)
  | [], _, _, _, _, h, _ => by rw [holeFam_nil]; exact h [] trivial
  | d :: ab, ρ, B, g, hg, h, hT => by
    rw [holeFam_cons]
    show lamV _ _ _ ∈ˢ interp V ρ (.pi d (mkPisAV ab B))
    rw [interp_pi]
    refine lamV_mem (fun x hx => holeFam_mem_mkPisAV (fun vs hvs => h (x :: vs) ⟨hx, hvs⟩)
      (fun vs hvs => hT (x :: vs) ⟨hx, hvs⟩)) fun x hx => ?_
    cases ab with
    | nil => exact hT [x] ⟨hx, trivial⟩
    | cons d' ab => show IsTy (interp V (cons x ρ) (.pi d' (mkPisAV ab B))); rw [interp_pi]; exact IsTy_piV

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
    (hX : InTupleSpaceU (D.w ψ) D.N (D.idx ψ ρp) X) {t : Nat} (ht : t < D.k)
    {ab : List Term} (hab : ab = D.ids t ψ) :
    D.holeVal ψ ρp X t ∈ˢ interp V ρp (mkPisAV ab (.sort (D.w ψ))) := by
  have htN : t < D.N := Nat.lt_of_lt_of_le ht hkN
  unfold holeVal
  subst hab
  refine holeFam_mem_mkPisAV (fun vs hvs => ?_) fun vs _ => by rw [interp_sort]; exact IsTy_univ _
  rw [interp_sort]
  exact famSpaceIn_app (hX t htN) (tupW_mem hvs)

end LfpDatum

end ConLeche.Model
