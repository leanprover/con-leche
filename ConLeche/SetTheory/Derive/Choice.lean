module

public import ConLeche.SetTheory.Derive.Graphs

@[expose] public section

/-!
# Choice, derived from the first-order Jech-form axiom

Wraps `SetTheory.choice` (`IsChoiceFn`) into `choiceFn`, derives the
indexed-family form `piSet_choose` (constructing a dependent choice
function inside `piSet A B hB` using non-overlapping Kuratowski-tagged
slices), and retires the meta-level global selector `schoice`.
-/

namespace ConLeche.SetTheory

universe u

variable {V : Type u} [SetTheory V]

/-- Jech-form choice function for a set `x` of nonempty sets. -/
noncomputable def choiceFn (x : V) (h : ∀ a, a ∈ˢ x → ∃ y, y ∈ˢ a) : V :=
  Classical.choose (SetTheory.choice x h)

theorem choiceFn_spec {x : V} (h : ∀ a, a ∈ˢ x → ∃ y, y ∈ˢ a) :
    IsChoiceFn (Mem (V := V)) (choiceFn x h) x :=
  Classical.choose_spec (SetTheory.choice x h)

theorem choiceFn_ne_pt {x : V} (h : ∀ a, a ∈ˢ x → ∃ y, y ∈ˢ a) :
    choiceFn x h ≠ (pt : V) := by
  intro heq
  have h1 := (choiceFn_spec h).1 ptTag (heq ▸ ptTag_mem_pt)
  obtain ⟨a, y, -, -, hkp⟩ := h1
  rw [isKPair_iff] at hkp
  exact ptTag_ne_kpair a y hkp

theorem app_choiceFn_mem {x a : V} (h : ∀ b, b ∈ˢ x → ∃ y, y ∈ˢ b)
    (ha : a ∈ˢ x) : app (choiceFn x h) a ∈ˢ a := by
  have hspec := choiceFn_spec h
  obtain ⟨y, ⟨hy, p, hp, hkp⟩, huniq⟩ := hspec.2 a ha
  rw [isKPair_iff] at hkp
  subst hkp
  have happ : app (choiceFn x h) a = y := by
    refine app_eq_of_unique (choiceFn_ne_pt h) hp ?_
    intro y' hy'
    obtain ⟨a', y'', ha', hy'', hkp'⟩ := hspec.1 (kpair a y') hy'
    rw [isKPair_iff] at hkp'
    obtain ⟨ha_eq, hy_eq⟩ := kpair_inj hkp'
    rw [← ha_eq, ← hy_eq] at hy''
    exact huniq y' ⟨hy'', kpair a y', hy', isKPair_kpair a y'⟩
  rwa [happ]

/-- Dependent choice over `piSet`: any family `B` over `A` with
nonempty fibres admits a choice function in `piSet A B hB`.
Uses disjoint tagged slices `slice a := {⟨a, y⟩ ∈ sigmaPairs A B hB}`
so distinct indices never collide even when fibres coincide. -/
theorem piSet_choose {A : V} {B : V → V} (hB : HasSigmaPairs A B)
    (hne : ∀ a, a ∈ˢ A → ∃ y, y ∈ˢ B a) : ∃ f, f ∈ˢ piSet A B hB := by
  let S := sigmaPairs A B hB
  have hsepSlice : ∀ a : V, HasSep S (fun p => ∃ y, p = kpair a y) := fun a =>
    hasSep_of_def (by fo_def [DefFun.kpair_apply])
  let slice : V → V := fun a => sep S (fun p => ∃ y, p = kpair a y) (hsepSlice a)
  have hslice_def : DefFun 1 fun v => slice (v 0) := by
    dsimp only [slice]
    fo_def [DefFun.sep_apply_curry, DefFun.kpair_apply]
  have himgSlices : HasImage slice A := hasImage_of_defFun1 hslice_def A
  let slices := image slice A himgSlices
  have hneSlices : ∀ s, s ∈ˢ slices → ∃ p, p ∈ˢ s := by
    intro s hs
    obtain ⟨a, ha, rfl⟩ := mem_image.mp hs
    obtain ⟨y, hy⟩ := hne a ha
    exact ⟨kpair a y, mem_sep.mpr ⟨mem_sigmaPairs.mpr ⟨a, ha, y, hy, rfl⟩, y, rfl⟩⟩
  let c := choiceFn slices hneSlices
  let F : V → V := fun a => app (sing (app c (slice a))) a
  have hF_def : DefFun 1 fun v => F (v 0) := by
    dsimp only [F]
    fo_def [DefFun.app_apply, DefFun.sing_apply, hslice_def]
  have hG : HasGraph A F := hasGraph_of_defFun1 hF_def
  refine ⟨graph F A hG, graph_mem_piSet fun a ha => ?_⟩
  have ha_slice : slice a ∈ˢ slices := mem_image.mpr ⟨a, ha, rfl⟩
  have hmem := app_choiceFn_mem hneSlices ha_slice
  obtain ⟨hpS, y, hkp⟩ := mem_sep.mp hmem
  obtain ⟨a', _, y', hy', hp_eq⟩ := mem_sigmaPairs.mp hpS
  rw [hkp] at hp_eq
  obtain ⟨ha_eq, hy_eq⟩ := kpair_inj hp_eq
  rw [← ha_eq, ← hy_eq] at hy'
  have hne_pt : sing (kpair a y) ≠ (pt : V) := by
    intro heq
    have : kpair a y = ptTag := mem_pt.mp (heq ▸ mem_sing.mpr rfl)
    exact ptTag_ne_kpair a y this.symm
  have happ : F a = y := by
    dsimp only [F]
    rw [hkp]
    refine app_eq_of_unique hne_pt (mem_sing.mpr rfl) ?_
    intro z hz
    exact (kpair_inj (mem_sing.mp hz)).2
  rwa [happ]

end ConLeche.SetTheory
