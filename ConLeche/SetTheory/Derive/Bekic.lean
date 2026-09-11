module

public import ConLeche.SetTheory.Derive.LfpFam
public import ConLeche.SetTheory.Derive.Pair
@[expose] public section

/-!
# Bekić's lemma for least pre-fixed families (task #280)

A monotone functor `Φ` on families over a disjoint union `S ∪ C` of
index sets has, as the `S`-restriction of its least fixed point, the
least fixed point of its **`S`-section** at the fixed point's own
`C`-restriction — `X ↦ Φ(X ⊔ μ|_C)|_S` (`bekic_restr`) — and, dually,
its `C`-restriction is the least fixed point of `Y ↦ Φ(lfp(X ↦ Φ(X ⊔
Y)|_S) ⊔ Y)|_C`, the section with the `S`-part solved (`bekic_nested`).
This is what identifies an auxiliary copy of a container inside a
nested block's simultaneous fixed point with the container's own least
fixed point at the copy's pins (the nested design, §5.3 (T2)).

Families are graphs over their index set (`famSpace`); restriction
(`famRestr`) and join (`famJoin`) are the evident graphs; a section is a
functor on families over `S`, spelled as a graph on the family space so
that `lfpFamSet` applies to it.  Everything here is over the bare
`SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Restriction and join -/

/-- The restriction of a family to an index subset. -/
noncomputable def famRestr (X S : V) : V := graph (fun i => app X i) S

theorem app_famRestr {X S i : V} (hi : i ∈ˢ S) : app (famRestr X S) i = app X i :=
  app_graph hi

theorem famRestr_mem {w : Nat} {I X S : V} (hX : X ∈ˢ famSpace w I) (hS : S ⊆ˢ I) :
    famRestr X S ∈ˢ famSpace w S :=
  graph_mem_famSpace fun i hi => famSpace_app hX (hS i hi)

theorem famRestr_le {I X Y S : V} (h : FamLe I X Y) (hS : S ⊆ˢ I) :
    FamLe S (famRestr X S) (famRestr Y S) := by
  intro i hi
  rw [app_famRestr hi, app_famRestr hi]
  exact h i (hS i hi)

open Classical in
/-- The join of a family over `S` and a family over `C`, over `S ∪ C`
(the `S`-part wins on an overlap). -/
noncomputable def famJoin (S C XS XC : V) : V :=
  graph (fun i => if i ∈ˢ S then app XS i else app XC i) (binUnion S C)

theorem app_famJoin_left {S C XS XC i : V} (hi : i ∈ˢ S) :
    app (famJoin S C XS XC) i = app XS i := by
  unfold famJoin
  rw [app_graph (mem_binUnion.mpr (Or.inl hi)), if_pos hi]

theorem app_famJoin_right {S C XS XC i : V} (hi : i ∈ˢ C) (hS : ¬ i ∈ˢ S) :
    app (famJoin S C XS XC) i = app XC i := by
  unfold famJoin
  rw [app_graph (mem_binUnion.mpr (Or.inr hi)), if_neg hS]

theorem famJoin_mem {w : Nat} {S C XS XC : V} (hXS : XS ∈ˢ famSpace w S)
    (hXC : XC ∈ˢ famSpace w C) : famJoin S C XS XC ∈ˢ famSpace w (binUnion S C) := by
  refine graph_mem_famSpace fun i hi => ?_
  by_cases h : i ∈ˢ S
  · rw [if_pos h]; exact famSpace_app hXS h
  · rw [if_neg h]; exact famSpace_app hXC ((mem_binUnion.mp hi).resolve_left h)

theorem famJoin_le {S C XS XS' XC XC' : V} (hS : FamLe S XS XS') (hC : FamLe C XC XC') :
    FamLe (binUnion S C) (famJoin S C XS XC) (famJoin S C XS' XC') := by
  intro i hi
  by_cases h : i ∈ˢ S
  · rw [app_famJoin_left h, app_famJoin_left h]; exact hS i h
  · have hc : i ∈ˢ C := (mem_binUnion.mp hi).resolve_left h
    rw [app_famJoin_right hc h, app_famJoin_right hc h]; exact hC i hc

/-- A family over `S ∪ C` is the join of its two restrictions. -/
theorem famJoin_famRestr {w : Nat} {S C X : V} (hX : X ∈ˢ famSpace w (binUnion S C)) :
    famJoin S C (famRestr X S) (famRestr X C) = X := by
  refine famSpace_ext (famJoin_mem (famRestr_mem hX fun i hi => mem_binUnion.mpr (Or.inl hi))
    (famRestr_mem hX fun i hi => mem_binUnion.mpr (Or.inr hi))) hX fun i hi => ?_
  by_cases h : i ∈ˢ S
  · rw [app_famJoin_left h, app_famRestr h]
  · have hc : i ∈ˢ C := (mem_binUnion.mp hi).resolve_left h
    rw [app_famJoin_right hc h, app_famRestr hc]

/-! ## Sections -/

/-- The `S`-section of `Φ` at a fixed `C`-part `Y`: `X ↦ Φ(X ⊔ Y)|_S`,
as a graph on the family space over `S`. -/
noncomputable def famSec (w : Nat) (S C Φ Y : V) : V :=
  graph (fun X => famRestr (app Φ (famJoin S C X Y)) S) (famSpace w S)

theorem app_famSec {w : Nat} {S C Φ Y X : V} (hX : X ∈ˢ famSpace w S) :
    app (famSec w S C Φ Y) X = famRestr (app Φ (famJoin S C X Y)) S :=
  app_graph hX

theorem famSec_maps {w : Nat} {S C Φ Y : V} (hmaps : MapsFam w (binUnion S C) Φ)
    (hY : Y ∈ˢ famSpace w C) : MapsFam w S (famSec w S C Φ Y) := by
  intro X hX
  rw [app_famSec hX]
  exact famRestr_mem (hmaps _ (famJoin_mem hX hY)) fun i hi => mem_binUnion.mpr (Or.inl hi)

theorem famSec_mono {w : Nat} {S C Φ Y : V} (hmono : MonoFam w (binUnion S C) Φ)
    (hY : Y ∈ˢ famSpace w C) : MonoFam w S (famSec w S C Φ Y) := by
  intro X X' hX hX' hle
  rw [app_famSec hX, app_famSec hX']
  exact famRestr_le (hmono _ _ (famJoin_mem hX hY) (famJoin_mem hX' hY)
    (famJoin_le hle (FamLe.refl _ _))) fun i hi => mem_binUnion.mpr (Or.inl hi)

/-- The section is monotone in its fixed part too. -/
theorem famSec_le_of_le {w : Nat} {S C Φ Y Y' : V} (hmono : MonoFam w (binUnion S C) Φ)
    (hY : Y ∈ˢ famSpace w C) (hY' : Y' ∈ˢ famSpace w C) (hle : FamLe C Y Y')
    {X : V} (hX : X ∈ˢ famSpace w S) :
    FamLe S (app (famSec w S C Φ Y) X) (app (famSec w S C Φ Y') X) := by
  rw [app_famSec hX, app_famSec hX]
  exact famRestr_le (hmono _ _ (famJoin_mem hX hY) (famJoin_mem hX hY')
    (famJoin_le (FamLe.refl _ _) hle)) fun i hi => mem_binUnion.mpr (Or.inl hi)

/-! ## Least fixed points are monotone in the functor -/

/-- **Monotonicity in the functor**: a pointwise larger functor with a
closed member has the larger least pre-fixed family. -/
theorem lfpFamSet_mono_functor {w : Nat} {I F F' : V}
    (hle : ∀ X, X ∈ˢ famSpace w I → FamLe I (app F X) (app F' X))
    (hmono' : MonoFam w I F') (hcl' : ∃ L, IsClosedFam w I F' L) :
    FamLe I (lfpFamSet w I F) (lfpFamSet w I F') := by
  refine lfpFamSet_le ⟨lfpFamSet_mem w I F', fun i hi x hx => ?_⟩
  exact lfpFamSet_closed hcl' hmono' i hi x (hle _ (lfpFamSet_mem w I F') i hi x hx)

/-- Functors agreeing on the family space have the same least
pre-fixed family. -/
theorem lfpFamSet_congr_functor {w : Nat} {I F F' : V}
    (heq : ∀ X, X ∈ˢ famSpace w I → app F X = app F' X)
    (hmono : MonoFam w I F) (hcl : ∃ L, IsClosedFam w I F L) :
    lfpFamSet w I F = lfpFamSet w I F' := by
  have hmono' : MonoFam w I F' := by
    intro X Y hX hY hle
    rw [← heq X hX, ← heq Y hY]; exact hmono X Y hX hY hle
  have hcl' : ∃ L, IsClosedFam w I F' L := by
    obtain ⟨L, hL, hcl⟩ := hcl
    exact ⟨L, hL, by rw [← heq L hL]; exact hcl⟩
  refine famSpace_ext (lfpFamSet_mem w I F) (lfpFamSet_mem w I F') fun i hi => ?_
  refine Subset.antisymm (lfpFamSet_mono_functor (fun X hX => by rw [heq X hX]; exact FamLe.refl _ _)
    hmono' hcl' i hi) (lfpFamSet_mono_functor (fun X hX => by rw [heq X hX]; exact FamLe.refl _ _)
    hmono hcl i hi)

/-! ## Bekić -/

section Bekic

variable {w : Nat} {S C Φ : V}
  (hmono : MonoFam w (binUnion S C) Φ) (hmaps : MapsFam w (binUnion S C) Φ)
  (hcl : ∃ L, IsClosedFam w (binUnion S C) Φ L)

include hmono hmaps hcl

/-- **Bekić's lemma, the projection**: the `S`-restriction of the least
fixed point is the least fixed point of the `S`-section at the fixed
point's `C`-restriction. -/
theorem bekic_restr :
    famRestr (lfpFamSet w (binUnion S C) Φ) S
      = lfpFamSet w S (famSec w S C Φ (famRestr (lfpFamSet w (binUnion S C) Φ) C)) := by
  let μ := lfpFamSet w (binUnion S C) Φ
  have hμmem : μ ∈ˢ famSpace w (binUnion S C) := lfpFamSet_mem _ _ _
  have hSsub : S ⊆ˢ binUnion S C := fun i hi => mem_binUnion.mpr (Or.inl hi)
  have hCsub : C ⊆ˢ binUnion S C := fun i hi => mem_binUnion.mpr (Or.inr hi)
  have hμS : famRestr μ S ∈ˢ famSpace w S := famRestr_mem hμmem hSsub
  have hμC : famRestr μ C ∈ˢ famSpace w C := famRestr_mem hμmem hCsub
  let F := famSec w S C Φ (famRestr μ C)
  have hfix : app Φ μ = μ := lfpFamSet_eq hcl hmono hmaps
  -- the restriction is a fixed point of the section
  have hFμS : app F (famRestr μ S) = famRestr μ S := by
    rw [app_famSec hμS, famJoin_famRestr hμmem, hfix]
  have hclosedS : IsClosedFam w S F (famRestr μ S) :=
    ⟨hμS, by rw [hFμS]; exact FamLe.refl _ _⟩
  have hFmono : MonoFam w S F := famSec_mono hmono hμC
  let ν := lfpFamSet w S F
  have hνmem : ν ∈ˢ famSpace w S := lfpFamSet_mem _ _ _
  -- `ν ≤ μ|_S`
  have hνle : FamLe S ν (famRestr μ S) := lfpFamSet_le hclosedS
  -- `ν ⊔ μ|_C` is closed under `Φ`, so `μ ≤ ν ⊔ μ|_C`
  have hjoinmem : famJoin S C ν (famRestr μ C) ∈ˢ famSpace w (binUnion S C) := famJoin_mem hνmem hμC
  have hjoinle : FamLe (binUnion S C) (famJoin S C ν (famRestr μ C)) μ := by
    have := famJoin_le hνle (FamLe.refl C (famRestr μ C))
    rwa [famJoin_famRestr hμmem] at this
  have hclosedJ : IsClosedFam w (binUnion S C) Φ (famJoin S C ν (famRestr μ C)) := by
    refine ⟨hjoinmem, fun i hi x hx => ?_⟩
    by_cases hiS : i ∈ˢ S
    · -- on `S`: the section's closure
      rw [app_famJoin_left hiS]
      have hcl := lfpFamSet_closed ⟨_, hclosedS⟩ hFmono i hiS
      rw [app_famSec hνmem, app_famRestr hiS] at hcl
      exact hcl x hx
    · -- on `C`: monotonicity into the fixed point
      have hiC : i ∈ˢ C := (mem_binUnion.mp hi).resolve_left hiS
      rw [app_famJoin_right hiC hiS, app_famRestr hiC]
      have := hmono _ _ hjoinmem hμmem hjoinle i hi x hx
      rwa [hfix] at this
  have hμle : FamLe (binUnion S C) μ (famJoin S C ν (famRestr μ C)) := lfpFamSet_le hclosedJ
  refine famSpace_ext hμS hνmem fun i hi => ?_
  refine Subset.antisymm (fun x hx => ?_) (hνle i hi)
  rw [app_famRestr hi] at hx
  have := hμle i (hSsub i hi) x hx
  rwa [app_famJoin_left hi] at this

/-- The `C`-section with the `S`-part solved: `Y ↦ Φ(lfp(X ↦ Φ(X ⊔ Y)|_S) ⊔ Y)|_C`. -/
noncomputable def famNested (w : Nat) (S C Φ : V) : V :=
  graph (fun Y => famRestr (app Φ (famJoin S C (lfpFamSet w S (famSec w S C Φ Y)) Y)) C)
    (famSpace w C)

omit hmono hmaps hcl in
theorem app_famNested {Y : V} (hY : Y ∈ˢ famSpace w C) :
    app (famNested w S C Φ) Y
      = famRestr (app Φ (famJoin S C (lfpFamSet w S (famSec w S C Φ Y)) Y)) C :=
  app_graph hY

omit hmaps hcl in
/-- The solved section's least fixed point is monotone in the fixed
part. -/
theorem lfpFamSet_famSec_mono {Y Y' : V} (hY : Y ∈ˢ famSpace w C) (hY' : Y' ∈ˢ famSpace w C)
    (hle : FamLe C Y Y') (hcl' : ∃ L, IsClosedFam w S (famSec w S C Φ Y') L) :
    FamLe S (lfpFamSet w S (famSec w S C Φ Y)) (lfpFamSet w S (famSec w S C Φ Y')) :=
  lfpFamSet_mono_functor (fun _ hX => famSec_le_of_le hmono hY hY' hle hX)
    (famSec_mono hmono hY') hcl'

/-- **Bekić's lemma, the nested form**: the `C`-restriction of the least
fixed point is the least fixed point of the `C`-section with the
`S`-part solved.  The sections at arbitrary `C`-families must have
closed members (`hsec`; at the fixed point's own restriction the
member is `μ|_S`, and a consumer with a container witness has one at
every family). -/
theorem bekic_nested (hdisj : ∀ i, i ∈ˢ S → ¬ i ∈ˢ C)
    (hsec : ∀ Y, Y ∈ˢ famSpace w C → ∃ L, IsClosedFam w S (famSec w S C Φ Y) L) :
    famRestr (lfpFamSet w (binUnion S C) Φ) C = lfpFamSet w C (famNested w S C Φ) := by
  let μ := lfpFamSet w (binUnion S C) Φ
  have hμmem : μ ∈ˢ famSpace w (binUnion S C) := lfpFamSet_mem _ _ _
  have hSsub : S ⊆ˢ binUnion S C := fun i hi => mem_binUnion.mpr (Or.inl hi)
  have hCsub : C ⊆ˢ binUnion S C := fun i hi => mem_binUnion.mpr (Or.inr hi)
  have hμC : famRestr μ C ∈ˢ famSpace w C := famRestr_mem hμmem hCsub
  have hfix : app Φ μ = μ := lfpFamSet_eq hcl hmono hmaps
  have hbek := bekic_restr hmono hmaps hcl (S := S) (C := C)
  let G := famNested w S C Φ
  -- `μ|_C` is a fixed point of `G`
  have hGμC : app G (famRestr μ C) = famRestr μ C := by
    rw [app_famNested hμC, ← hbek, famJoin_famRestr hμmem, hfix]
  have hclosedC : IsClosedFam w C G (famRestr μ C) := ⟨hμC, by rw [hGμC]; exact FamLe.refl _ _⟩
  -- `G` is monotone
  have hGmono : MonoFam w C G := by
    intro Y Y' hY hY' hle
    rw [app_famNested hY, app_famNested hY']
    refine famRestr_le (hmono _ _ (famJoin_mem (lfpFamSet_mem _ _ _) hY)
      (famJoin_mem (lfpFamSet_mem _ _ _) hY')
      (famJoin_le (lfpFamSet_famSec_mono hmono hY hY' hle (hsec Y' hY')) hle)) hCsub
  let κ := lfpFamSet w C G
  have hκmem : κ ∈ˢ famSpace w C := lfpFamSet_mem _ _ _
  have hκle : FamLe C κ (famRestr μ C) := lfpFamSet_le hclosedC
  -- `lfp(sec κ) ⊔ κ` is closed under `Φ`
  let ν := lfpFamSet w S (famSec w S C Φ κ)
  have hνmem : ν ∈ˢ famSpace w S := lfpFamSet_mem _ _ _
  have hclosedJ : IsClosedFam w (binUnion S C) Φ (famJoin S C ν κ) := by
    refine ⟨famJoin_mem hνmem hκmem, fun i hi x hx => ?_⟩
    by_cases hiS : i ∈ˢ S
    · rw [app_famJoin_left hiS]
      have h := lfpFamSet_closed (hsec κ hκmem) (famSec_mono hmono hκmem) i hiS
      rw [app_famSec hνmem, app_famRestr hiS] at h
      exact h x hx
    · have hiC : i ∈ˢ C := (mem_binUnion.mp hi).resolve_left hiS
      rw [app_famJoin_right hiC hiS]
      have h := lfpFamSet_closed ⟨_, hclosedC⟩ hGmono i hiC
      rw [app_famNested hκmem, app_famRestr hiC] at h
      exact h x hx
  have hμle : FamLe (binUnion S C) μ (famJoin S C ν κ) := lfpFamSet_le hclosedJ
  refine famSpace_ext hμC hκmem fun i hi => ?_
  refine Subset.antisymm (fun x hx => ?_) (hκle i hi)
  rw [app_famRestr hi] at hx
  have := hμle i (hCsub i hi) x hx
  rwa [app_famJoin_right hi (fun hiS => hdisj i hiS hi)] at this

end Bekic

end ConLeche.SetTheory
