module

public import ConLeche.SetTheory.Derive.Bekic
@[expose] public section

/-!
# Bekić at one component, along an index map (task #279 M-F)

The nested design's set-equality form (DESIGN §M.59): the auxiliary
block's simultaneous least fixed point `μ = lfp Φ` over `S ∪ C`
has, at the component `S` of a copy, the CONTAINER's own least fixed
point `lfp G` over the container's index set `J` — provided the copy's
section of `Φ` at the fixed point's other components agrees with `G`
along a bijection `f : J ≃ S` of the index sets (`hagree`, the
"operator identity" of §M.59 (c)).  Then, fibrewise,

    app μ (f i) = app (lfp G) i        for every `i ∈ J`.

The proof is `bekic_restr` (`μ|_S` is the least fixed point of the
`S`-section at `μ|_C`) plus two closure arguments transported along
`f`: the pull-back of `μ|_S` is `G`-closed (so `lfp G ≤ μ|_S ∘ f`),
and the push-forward of `lfp G` is closed under the section (so
`μ|_S ≤ lfp G ∘ g`).  No order among the components enters: `μ|_C`
is whatever the simultaneous fixed point makes it, and the agreement
is asked at that value only.  Everything here is over the bare
`SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-! ## Transport of families along an index map -/

/-- The pull-back of a family `X` over `S` along `f : J → S`: the family
`i ↦ X (f i)` over `J`. -/
noncomputable def famPull (f : V → V) (X J : V) : V := graph (fun i => app X (f i)) J

theorem app_famPull {f : V → V} {X J i : V} (hi : i ∈ˢ J) : app (famPull f X J) i = app X (f i) :=
  app_graph hi

theorem famPull_mem {w : Nat} {f : V → V} {X J S : V} (hX : X ∈ˢ famSpace w S)
    (hf : ∀ i, i ∈ˢ J → f i ∈ˢ S) : famPull f X J ∈ˢ famSpace w J :=
  graph_mem_famSpace fun i hi => famSpace_app hX (hf i hi)

/-- The pull-back of a push-forward along an inverse pair is the
family itself. -/
theorem famPull_famPull_inv {w : Nat} {f g : V → V} {X J S : V} (hX : X ∈ˢ famSpace w J)
    (hf : ∀ i, i ∈ˢ J → f i ∈ˢ S) (hg : ∀ s, s ∈ˢ S → g s ∈ˢ J)
    (hgf : ∀ i, i ∈ˢ J → g (f i) = i) :
    famPull f (famPull g X S) J = X := by
  refine famSpace_ext (famPull_mem (famPull_mem hX hg) hf) hX fun i hi => ?_
  rw [app_famPull hi, app_famPull (hf i hi), hgf i hi]

/-! ## Bekić at one component -/

/-- **Bekić at one component, along an index bijection.**  For the
simultaneous least fixed point `μ` of `Φ` over `S ∪ C` and a functor
`G` over `J` with `f : J → S`, `g : S → J` mutually inverse, if the
`S`-section of `Φ` at `μ|_C` agrees with `G` along `f` — at every
family `Y` over `S`, the fibre of `Φ (Y ⊔ μ|_C)` at `f i` is the fibre
of `G (Y ∘ f)` at `i` — then `μ`'s fibre at `f i` is `lfp G`'s at `i`. -/
theorem bekic_component {w : Nat} {S C Φ : V}
    (hmono : MonoFam w (binUnion S C) Φ) (hmaps : MapsFam w (binUnion S C) Φ)
    (hcl : ∃ L, IsClosedFam w (binUnion S C) Φ L)
    {J G : V} (hGmono : MonoFam w J G) (hGmaps : MapsFam w J G)
    (hGcl : ∃ L, IsClosedFam w J G L)
    (f g : V → V) (hf : ∀ i, i ∈ˢ J → f i ∈ˢ S) (hg : ∀ s, s ∈ˢ S → g s ∈ˢ J)
    (hgf : ∀ i, i ∈ˢ J → g (f i) = i) (hfg : ∀ s, s ∈ˢ S → f (g s) = s)
    (hagree : ∀ Y, Y ∈ˢ famSpace w S → ∀ i, i ∈ˢ J →
      app (app Φ (famJoin S C Y (famRestr (lfpFamSet w (binUnion S C) Φ) C))) (f i)
        = app (app G (famPull f Y J)) i) :
    ∀ i, i ∈ˢ J → app (lfpFamSet w (binUnion S C) Φ) (f i) = app (lfpFamSet w J G) i := by
  intro i hi
  let μ := lfpFamSet w (binUnion S C) Φ
  have hμmem : μ ∈ˢ famSpace w (binUnion S C) := lfpFamSet_mem _ _ _
  have hSsub : S ⊆ˢ binUnion S C := fun i hi => mem_binUnion.mpr (Or.inl hi)
  have hCsub : C ⊆ˢ binUnion S C := fun i hi => mem_binUnion.mpr (Or.inr hi)
  have hμS : famRestr μ S ∈ˢ famSpace w S := famRestr_mem hμmem hSsub
  have hfix : app Φ μ = μ := lfpFamSet_eq hcl hmono hmaps
  let ν := lfpFamSet w J G
  have hνmem : ν ∈ˢ famSpace w J := lfpFamSet_mem _ _ _
  have hνfix : app G ν = ν := lfpFamSet_eq hGcl hGmono hGmaps
  refine Subset.antisymm ?_ ?_
  · -- `μ|_S ≤ lfp G ∘ g`: the push-forward of `lfp G` is closed under the section
    have hbek := bekic_restr hmono hmaps hcl (S := S) (C := C)
    let P := famPull g ν S
    have hPmem : P ∈ˢ famSpace w S := famPull_mem hνmem hg
    have hPull : famPull f P J = ν := famPull_famPull_inv hνmem hf hg hgf
    have hclosed : IsClosedFam w S (famSec w S C Φ (famRestr μ C)) P := by
      refine ⟨hPmem, fun s hs x hx => ?_⟩
      rw [app_famSec hPmem, app_famRestr hs] at hx
      have hs' : s = f (g s) := (hfg s hs).symm
      rw [hs', hagree P hPmem (g s) (hg s hs), hPull, hνfix] at hx
      rw [app_famPull hs]
      exact hx
    have hle : FamLe S (famRestr μ S) P := by
      rw [hbek]; exact lfpFamSet_le hclosed
    intro x hx
    have := hle (f i) (hf i hi) x (by rw [app_famRestr (hf i hi)]; exact hx)
    rw [app_famPull (hf i hi), hgf i hi] at this
    exact this
  · -- `lfp G ≤ μ|_S ∘ f`: the pull-back of `μ|_S` is `G`-closed
    have hclosed : IsClosedFam w J G (famPull f (famRestr μ S) J) := by
      refine ⟨famPull_mem hμS hf, fun i hi x hx => ?_⟩
      rw [← hagree _ hμS i hi, famJoin_famRestr hμmem, hfix] at hx
      rw [app_famPull hi, app_famRestr (hf i hi)]
      exact hx
    intro x hx
    have := lfpFamSet_le hclosed i hi x hx
    rw [app_famPull hi, app_famRestr (hf i hi)] at this
    exact this

/-- `bekic_component` over an index set `I` with `S ⊆ I`: the other
components are the complement `I ∖ S`. -/
theorem bekic_component' {w : Nat} {I S Φ : V} (hS : S ⊆ˢ I)
    (hmono : MonoFam w I Φ) (hmaps : MapsFam w I Φ) (hcl : ∃ L, IsClosedFam w I Φ L)
    {J G : V} (hGmono : MonoFam w J G) (hGmaps : MapsFam w J G)
    (hGcl : ∃ L, IsClosedFam w J G L)
    (f g : V → V) (hf : ∀ i, i ∈ˢ J → f i ∈ˢ S) (hg : ∀ s, s ∈ˢ S → g s ∈ˢ J)
    (hgf : ∀ i, i ∈ˢ J → g (f i) = i) (hfg : ∀ s, s ∈ˢ S → f (g s) = s)
    (hagree : ∀ Y, Y ∈ˢ famSpace w S → ∀ i, i ∈ˢ J →
      app (app Φ (famJoin S (sep I (fun i => ¬ i ∈ˢ S)) Y
        (famRestr (lfpFamSet w I Φ) (sep I (fun i => ¬ i ∈ˢ S))))) (f i)
        = app (app G (famPull f Y J)) i) :
    ∀ i, i ∈ˢ J → app (lfpFamSet w I Φ) (f i) = app (lfpFamSet w J G) i := by
  have hI : binUnion S (sep I (fun i => ¬ i ∈ˢ S)) = I := by
    refine Subset.antisymm (fun z hz => ?_) (fun z hz => ?_)
    · rcases mem_binUnion.mp hz with h | h
      · exact hS z h
      · exact (mem_sep.mp h).1
    · by_cases h : z ∈ˢ S
      · exact mem_binUnion.mpr (Or.inl h)
      · exact mem_binUnion.mpr (Or.inr (mem_sep.mpr ⟨hz, h⟩))
  obtain ⟨C, hC⟩ : ∃ C, C = sep I (fun i => ¬ i ∈ˢ S) := ⟨_, rfl⟩
  rw [← hC] at hI hagree
  rw [← hI] at hmono hmaps hcl hagree ⊢
  exact bekic_component hmono hmaps hcl hGmono hGmaps hGcl f g hf hg hgf hfg hagree

end ConLeche.SetTheory
