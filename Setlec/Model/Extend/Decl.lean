import Setlec.Model.Extend.Ind
import Setlec.Model.Extend.Proj

/-!
# Decl — split out of `Setlec.Model.Extend`

`checkIndDecl_sound`: checking a modeled inductive block preserves
having a model.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory Expr

/-- Checking a modeled inductive block preserves having a model. -/
theorem checkIndDecl_sound {env env₂ : Env} {block : List ConstantInfo}
    (h : checkIndDecl (fueledOps F) env block = .ok env₂) (m : EnvModel V env) :
    Nonempty (EnvModel V env₂) := by
  rw [checkIndDecl] at h
  have hbn : ∀ ci ∈ block, (block.map (·.name)).contains ci.name = true :=
    fun ci hci => by
      have : ci.name ∈ block.map (·.name) := List.mem_map_of_mem hci
      simpa using this
  split at h
  · -- the single-constructor arm installs the projection family
    rename_i cvT capsT cvC nP nF heqI heqC
    simp only [Bind.bind, Except.bind, pure, Except.pure] at h
    obtain ⟨env₁, hfold, h⟩ := Except.bind_ok h
    have hI₀ : BlockInstalled (block.map (·.name)) env m.val := by
      intro n hn ci₂ hf₂
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [checkIndMember_fold_names block env env₁ hfold ci₀ hci₀] at hf₂
      exact nomatch hf₂
    have hpins0 : ∀ (cv : ConstantVal) (caps₂ : IndCaps),
        (ConstantInfo.indInfo cv caps₂) ∈ block →
        EtaPins env cv.name cv.levelParams
          (indBlockCaps env cvT cvC nP nF) := by
      intro cv caps₂ hmem
      have hmemf : (ConstantInfo.indInfo cv caps₂) ∈
          ([ConstantInfo.indInfo cvT capsT] : List ConstantInfo) := by
        rw [← heqI]
        exact List.mem_filter.mpr ⟨hmem, rfl⟩
      have hid := List.mem_singleton.mp hmemf
      injection hid with h1 h2
      rw [h1]
      refine ⟨?_, ?_⟩
      · intro hcape
        simp only [indBlockCaps, Bool.and_eq_true] at hcape
        exact checkEtaThm_inv hcape.2
      · intro hcapu
        simp only [indBlockCaps] at hcapu
        exact checkUnitThm_inv hcapu
    obtain ⟨m₁, hI₁⟩ := checkIndFold_sound block env env₁ hbn hpins0
      hfold m hI₀
    have hTin : (ConstantInfo.indInfo cvT capsT) ∈ block := by
      have h1 : ConstantInfo.indInfo cvT capsT ∈
          [ConstantInfo.indInfo cvT capsT] :=
        List.mem_singleton.mpr rfl
      rw [← heqI] at h1
      exact (List.mem_filter.mp h1).1
    have hCin : (ConstantInfo.ctorInfo cvC nP nF) ∈ block := by
      have h1 : ConstantInfo.ctorInfo cvC nP nF ∈
          [ConstantInfo.ctorInfo cvC nP nF] :=
        List.mem_singleton.mpr rfl
      rw [← heqC] at h1
      exact (List.mem_filter.mp h1).1
    have hbnT : (block.map (·.name)).contains cvT.name = true := by
      have hmm : cvT.name ∈ block.map (fun x => x.name) :=
        List.mem_map_of_mem (f := fun x => x.name) hTin
      simpa using hmm
    have hbnC : (block.map (·.name)).contains cvC.name = true := by
      have hmm : cvC.name ∈ block.map (fun x => x.name) :=
        List.mem_map_of_mem (f := fun x => x.name) hCin
      simpa using hmm
    try simp only [Bind.bind, Except.bind] at h
    by_cases hfresh : ((List.range nF).all
        (fun j => (env₁.find? (projFnName cvT.name j)).isNone)) = true
    case neg => rw [if_neg hfresh] at h; exact nomatch h
    rw [if_pos hfresh] at h
    try simp only [pure, Except.pure] at h
    try dsimp only at h
    have hinv₀ : ProjPhaseInv cvT.name cvC.name nF env₁ m₁.val := by
      refine ⟨?_, ?_, ?_⟩
      · intro ci hf
        exact hI₁ cvT.name hbnT ci hf
      · intro ci hf
        exact hI₁ cvC.name hbnC ci hf
      · intro j hj ci hf
        have hnone := List.all_eq_true.mp hfresh j (List.mem_range.mpr hj)
        rw [Option.isNone_iff_eq_none.mp hnone] at hf
        exact nomatch hf
    obtain ⟨mf, -⟩ :=
      checkProjFold_sound (List.range nF) env₁ env₂ h m₁ hinv₀
    exact ⟨mf⟩
  · -- no single-constructor structure: the plain member fold
    have hI₀ : BlockInstalled (block.map (·.name)) env m.val := by
      intro n hn ci₂ hf₂
      have hmem : n ∈ block.map (·.name) := by simpa using hn
      obtain ⟨ci₀, hci₀, rfl⟩ := List.mem_map.mp hmem
      rw [checkIndMember_fold_names block env env₂ h ci₀ hci₀] at hf₂
      exact nomatch hf₂
    obtain ⟨m₂, -⟩ := checkIndFold_sound block env env₂ hbn
      (fun _ _ _ => ⟨fun hcape => absurd hcape (by decide),
        fun hcapu => absurd hcapu (by decide)⟩) h m hI₀
    exact ⟨m₂⟩

end Setlec
