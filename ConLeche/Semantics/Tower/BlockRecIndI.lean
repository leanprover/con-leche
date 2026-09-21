module

public import ConLeche.Semantics.Tower.BlockRecI
@[expose] public section

/-!
# Regime IND: the recursor family's candidate at `ℓ = 0` (task #315, M5 model half)

DESIGN "DESIGN DOCUMENT 2, v2" §3.3.  When every conclusion is a
proposition (`allProp`, which every mutual or nested `Prop` block is,
by the elimination guard) the recursor's TYPE is a proposition, so
inhabiting it IS the induction principle and the value is the point:

* the candidate is `fun _ => pt` — nothing is built, and the whole
  regime reduces to `pt ∈ˢ ⟦RecTy_c⟧`, which is the nested induction
  (outer `lfpTuple_induction` on the block's narrow tuple, inner
  `KeyInd` per container key: the SetModel tier's kit, F3's
  `InductionKit` generalised);
* every ι law is `pt = pt`: the left-hand side collapses by `app_pt`
  (the recursor value is the point, and applying the point is the
  point), the right-hand side because the residue's reading lies in a
  truth value — G4's repair, the residue's certified typing (G1) at
  `ℓ = 0`.

So this file is the whole of regime IND at the TERM level: the two
collapses, and the reduction of `BlockRecPre.hCand` to the induction
principle.  No kit, no graph, no `mkInj`, no `mkDepth`.
-/

namespace ConLeche.Semantics
open ConLeche.SetModel

open SetTheory
open ConLeche.SetTheory.Tower

universe uv

variable {V : Type uv} [SetTheory V]

/-- **The point absorbs a whole spine.** -/
theorem foldl_app_pt : ∀ (as : List V), as.foldl SetTheory.app (pt : V) = pt
  | [] => rfl
  | a :: as => by
    show as.foldl SetTheory.app (SetTheory.app (pt : V) a) = _
    rw [app_pt]
    exact foldl_app_pt as

/-- A member of a truth value is the point. -/
theorem eq_pt_of_mem_prop {T x : V} (hT : T ∈ˢ (univZero : V)) (hx : x ∈ˢ T) : x = pt :=
  eq_pt_of_mem_univZero hT hx

section Ind

variable {s K : Nat} {RecTy : Nat → AnnotTerm} {nCt : Nat → Nat} {pdoms : Nat → List AnnotTerm}
  {fdoms es : Nat → Nat → List AnnotTerm} {mk : Nat → Nat → AnnotTerm}
  {ihs : Nat → Nat → List AnnotTerm} {Rb : Nat → Nat → AnnotTerm} {ρ : Nat → V}

/-- **THE IND REGIME'S CANDIDATE** (DESIGN v2 §3.3): at a `Prop`-valued
family the tuple is the constant point, and `BlockRecPre`'s `hCand`
reduces to

* `hind`: the recursor's type is INHABITED — the induction principle,
  proved at the SetModel tier by induction on the block's narrow
  tuple, and
* `hres`: every rule's residue reads into a truth value — the
  residue's certified typing (G1) at `ℓ = 0`.

The ι laws are `pt = pt`. -/
theorem indCand_hCand
    (hind : ∀ c, c < K → (pt : V) ∈ˢ interp V ρ (RecTy c))
    (hres : ∀ c, c < K → ∀ j, j < nCt c → ∀ xs fs : List V,
      xs.length = (pdoms c).length →
      SpineFit (chainFrame K (fun _ => (pt : V)) ρ) (pdoms c ++ fdoms c j) (xs ++ fs) →
      ∃ T : V, T ∈ˢ (univZero : V) ∧
        interp V
            (consList
              ((ihs c j).map
                (interp V (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))))
              (consList (xs ++ fs) (chainFrame K (fun _ => (pt : V)) ρ))) (Rb c j) ∈ˢ T) :
    ∃ a : Nat → V, (∀ c, c < K → a c ∈ˢ interp V ρ (RecTy c)) ∧
      ∀ e ∈ iotaEqsAV K nCt pdoms fdoms es mk ihs Rb,
        (pt : V) ∈ˢ interp V (chainFrame K a ρ) e := by
  refine hCand_iotaEqsAV_of (fun _ => (pt : V)) hind fun c hc j hj xs fs hxl hsp => ?_
  obtain ⟨T, hT, hmem⟩ := hres c hc j hj xs fs hxl hsp
  rw [foldl_app_pt, eq_pt_of_mem_prop hT hmem]

end Ind

end ConLeche.Semantics
