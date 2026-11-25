module

public import ConLeche.SetModel.TaggedSum

@[expose] public section

/-!
# Omega-indexed unions (task #188)

The ω-indexed union `omegaUnion F h = ⋃_{k ∈ ω} F k`, a member of
`tg w` at `w ≥ 1` when every `F k` (`k ∈ˢ ω`) is (`omega_mem_tg_succ`,
given a set-level graph witness `HasGraph omega F`).

Everything here is over the bare `SetTheory` interface; no syntax.
-/

namespace ConLeche.SetTheory.Tower

universe u

variable {V : Type u} [SetTheory V]

/-- The union of an ω-indexed family `⋃_{k ∈ ω} F k`. -/
noncomputable def omegaUnion (F : V → V) (h : HasImage F omega) : V :=
  sUnion (image F omega h)

theorem mem_omegaUnion {F : V → V} {h : HasImage F omega} {x : V} :
    x ∈ˢ omegaUnion F h ↔ ∃ k, k ∈ˢ (omega : V) ∧ x ∈ˢ F k := by
  unfold omegaUnion
  rw [mem_sUnion]
  constructor
  · rintro ⟨y, hy, hxy⟩
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hy
    exact ⟨k, hk, hxy⟩
  · rintro ⟨k, hk, hxk⟩
    exact ⟨F k, mem_image.mpr ⟨k, hk, rfl⟩, hxk⟩

theorem omegaUnion_congr {F F' : V → V} (h : HasImage F omega) (h' : HasImage F' omega)
    (heq : ∀ k, k ∈ˢ (omega : V) → F k = F' k) : omegaUnion F h = omegaUnion F' h' := by
  unfold omegaUnion
  rw [image_congr h h' heq]

theorem _root_.ConLeche.SetTheory.DefFun.omegaUnion_apply {p : Nat} {F : (Fin (p + 1) → V) → V}
    {h : ∀ env, HasImage (fun k => F (fcons k env)) omega}
    (hF : DefFun (p + 1) F) :
    DefFun p fun env => omegaUnion (fun k => F (fcons k env)) (h env) := by
  unfold omegaUnion
  exact DefFun.sUnion_apply (DefFun.image_apply hF DefFun.omega_const)

theorem _root_.ConLeche.SetTheory.DefFun.omegaUnion_apply_curry {p : Nat} {F : V → (Fin p → V) → V}
    {h : ∀ env, HasImage (fun k => F k env) omega}
    (hF : DefFun (p + 1) fun v => F (v 0) (ftail v)) :
    DefFun p fun env => omegaUnion (fun k => F k env) (h env) :=
  _root_.ConLeche.SetTheory.DefFun.omegaUnion_apply (F := fun v => F (v 0) (ftail v)) hF

/-- An ω-indexed union of members of a positive axiomatic level is a
member (a size bound), given a set-level graph witness `HasGraph omega F`. -/
theorem omegaUnion_mem_tg_pos {w : Nat} (hw : w ≠ 0) {F : V → V}
    (hImg : HasImage F omega) (hG : HasGraph omega F)
    (h : ∀ k, k ∈ˢ (omega : V) → F k ∈ˢ (tg w : V)) :
    omegaUnion F hImg ∈ˢ (tg w : V) := by
  obtain ⟨w', rfl⟩ : ∃ w', w = w' + 1 := ⟨w - 1, by omega⟩
  unfold omegaUnion
  exact (tg_isGrothendieck (Nat.succ_ne_zero w')).famUnion_mem (omega_mem_tg_succ w') h hImg hG

/-- Convenience form of `omegaUnion_mem_tg_pos` when `F` is `DefFunOn omega F`. -/
theorem omegaUnion_mem_tg_pos_of_def {w : Nat} (hw : w ≠ 0) {F : V → V}
    (hImg : HasImage F omega) (hDef : DefFunOn omega F)
    (h : ∀ k, k ∈ˢ (omega : V) → F k ∈ˢ (tg w : V)) :
    omegaUnion F hImg ∈ˢ (tg w : V) :=
  omegaUnion_mem_tg_pos hw hImg (hasGraph_of_defFunOn hDef) h

end ConLeche.SetTheory.Tower
