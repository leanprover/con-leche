import Setlec.Model.InterpLemmas

/-!
# Transport lemmas for annotation truthfulness (`AnnotOk`)

`AnnotOk` quantifies over opened binder bodies, so it needs the same
transport family as the interpretation itself: valuation extensionality,
weakening (shift / top), closed-term invariance, level instantiation,
environment monotonicity, and constant-valuation extensionality.  Each
proof mirrors the corresponding `interp_*` lemma, transporting the
conditions through the interpretation rewrites.
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat} {cval : ConstVal V}

open SetTheory Expr

theorem AnnotOk.ext : ∀ (e : Expr) {d : Nat} {ρ ρ' : Nat → V},
    (∀ i, i < d → ρ i = ρ' i) → fvarsBelow d e →
    AnnotOk V cval env φ d ρ e → AnnotOk V cval env φ d ρ' e
  | .forallE n ty body m, d, ρ, ρ', h, hb, ha => by
    simp only [fvarsBelow] at hb
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, vE, htie, hcond⟩ := ha
    refine ⟨AnnotOk.ext ty h hb.1 haty, vE, htie, ?_⟩
    intro x A hA hx
    rw [← interp_ext ty h hb.1] at hA
    obtain ⟨hbody, hw⟩ := hcond x A hA hx
    have hupd : ∀ i, i < d + 1 → updV V ρ d x i = updV V ρ' d x i := by
      intro i hi
      simp only [updV]
      split
      · rfl
      · exact h i (by omega)
    refine ⟨AnnotOk.ext _ hupd (fvarsBelow_instantiate1 0 hb.2) hbody, ?_⟩
    obtain ⟨w, hwi, hmem⟩ := hw
    exact ⟨w, by rw [← interp_ext _ hupd (fvarsBelow_instantiate1 0 hb.2)]; exact hwi, hmem⟩
  | .lam n ty body m, d, ρ, ρ', h, hb, ha => by
    simp only [fvarsBelow] at hb
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcod, hcond⟩ := ha
    refine ⟨AnnotOk.ext ty h hb.1 haty, hcod, ?_⟩
    intro x A hA hx
    rw [← interp_ext ty h hb.1] at hA
    obtain ⟨hbody, hw⟩ := hcond x A hA hx
    have hupd : ∀ i, i < d + 1 → updV V ρ d x i = updV V ρ' d x i := by
      intro i hi
      simp only [updV]
      split
      · rfl
      · exact h i (by omega)
    refine ⟨AnnotOk.ext _ hupd (fvarsBelow_instantiate1 0 hb.2) hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hw
    exact ⟨w, B,
      by rw [← interp_ext _ hupd (fvarsBelow_instantiate1 0 hb.2)]; exact hwi, hwB, hBu⟩
  | .app f a, d, ρ, ρ', h, hb, ha => by
    simp only [fvarsBelow] at hb
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hva, hfib⟩ := ha
    refine ⟨AnnotOk.ext f h hb.1 haf, AnnotOk.ext a h hb.2 haa,
      vf, va, vE, A, B, ?_, ?_, hpi, hva, hfib⟩
    · rw [← interp_ext f h hb.1]; exact hfi
    · rw [← interp_ext a h hb.2]; exact hai
  | .bvar _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .sort _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .const _ _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .fvar _ _ _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .letE n ty val body, d, ρ, ρ', h, hb, ha => by
    simp only [fvarsBelow] at hb
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
    have hupd : ∀ i, i < d + 1 → updV V ρ d xv i = updV V ρ' d xv i := by
      intro i hi
      simp only [updV]
      split
      · rfl
      · exact h i (by omega)
    refine ⟨AnnotOk.ext ty h hb.1 haty, AnnotOk.ext val h hb.2.1 hav, xv, ?_, ?_⟩
    · rw [← interp_ext val h hb.2.1]; exact hxv
    · exact AnnotOk.ext _ hupd (fvarsBelow_instantiate1 0 hb.2.2) hopen
  | .lit _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .proj s' i e, d, ρ, ρ', h, hb, ha => by
    simp only [fvarsBelow] at hb
    simp only [AnnotOk] at ha ⊢
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := ha
    refine ⟨AnnotOk.ext e h hb hae, hi2, ve, u', v', A, Bf, ?_, hsig, hAu, hBf⟩
    rw [← interp_ext e h hb]; exact hvei
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

theorem AnnotOk.shift : ∀ (e : Expr) {d p : Nat} {ρ : Nat → V} {x0 : V},
    p ≤ d → WScoped d e →
    AnnotOk V cval env φ d ρ e →
    AnnotOk V cval env φ (d + 1) (insV ρ p x0) (shiftFrom p e)
  | .forallE n ty body m, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d ty ∧ WScoped d body := by simpa [WScoped] using hw
    simp only [AnnotOk] at ha
    obtain ⟨haty, vE, htie, hcond⟩ := ha
    simp only [shiftFrom, AnnotOk]
    refine ⟨AnnotOk.shift ty hpd hw'.1 haty, vE, htie, ?_⟩
    intro x A hA hx
    rw [interp_shift ty hpd hw'.1] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    rw [← shiftFrom_instantiate1 hpd, ← insV_updV hpd]
    refine ⟨AnnotOk.shift _ (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2) hbody, ?_⟩
    obtain ⟨w, hwi, hmem⟩ := hwfact
    refine ⟨w, ?_, hmem⟩
    rw [interp_shift _ (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
    exact hwi
  | .lam n ty body m, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d ty ∧ WScoped d body := by simpa [WScoped] using hw
    simp only [AnnotOk] at ha
    obtain ⟨haty, hcod, hcond⟩ := ha
    simp only [shiftFrom, AnnotOk]
    refine ⟨AnnotOk.shift ty hpd hw'.1 haty, hcod, ?_⟩
    intro x A hA hx
    rw [interp_shift ty hpd hw'.1] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    rw [← shiftFrom_instantiate1 hpd, ← insV_updV hpd]
    refine ⟨AnnotOk.shift _ (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2) hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hwfact
    refine ⟨w, B, ?_, hwB, hBu⟩
    rw [interp_shift _ (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
    exact hwi
  | .app f a, d, p, ρ, x0, hpd, hw, ha => by
    simp only [WScoped] at hw
    simp only [AnnotOk] at ha
    simp only [shiftFrom, AnnotOk]
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hva, hfib⟩ := ha
    refine ⟨AnnotOk.shift f hpd hw.1 haf, AnnotOk.shift a hpd hw.2 haa,
      vf, va, vE, A, B, ?_, ?_, hpi, hva, hfib⟩
    · rw [interp_shift f hpd hw.1]; exact hfi
    · rw [interp_shift a hpd hw.2]; exact hai
  | .bvar _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .sort _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .const _ _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .fvar idx n ty, _, _, _, _, _, _, _ => by
    simp only [shiftFrom]
    split <;> simp [AnnotOk]
  | .letE n ty val body, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d ty ∧ WScoped d val ∧ WScoped d body := by
      simpa [WScoped] using hw
    simp only [AnnotOk] at ha
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
    simp only [shiftFrom, AnnotOk]
    refine ⟨AnnotOk.shift ty hpd hw'.1 haty,
      AnnotOk.shift val hpd hw'.2.1 hav, xv, ?_, ?_⟩
    · rw [interp_shift val hpd hw'.2.1]; exact hxv
    · rw [← shiftFrom_instantiate1 hpd, ← insV_updV hpd]
      exact AnnotOk.shift _ (Nat.le_succ_of_le hpd)
        (hw'.1.instantiate1 0 hw'.2.2) hopen
  | .lit _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .proj s' i e, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d e := by simpa [WScoped] using hw
    simp only [AnnotOk] at ha
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := ha
    simp only [shiftFrom, AnnotOk]
    refine ⟨AnnotOk.shift e hpd hw' hae, hi2, ve, u', v', A, Bf, ?_, hsig, hAu, hBf⟩
    rw [interp_shift e hpd hw']; exact hvei
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Converse of `AnnotOk.shift`: annotation truthfulness descends from
the shifted term at the extended frame back to the term itself.  Each
clause's interpretation facts transport along the `interp_shift`
equality; the opened bodies relabel by `shiftFrom_instantiate1`. -/
theorem AnnotOk.unshift : ∀ (e : Expr) {d p : Nat} {ρ : Nat → V} {x0 : V},
    p ≤ d → WScoped d e →
    AnnotOk V cval env φ (d + 1) (insV ρ p x0) (shiftFrom p e) →
    AnnotOk V cval env φ d ρ e
  | .forallE n ty body m, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d ty ∧ WScoped d body := by simpa [WScoped] using hw
    simp only [shiftFrom, AnnotOk] at ha
    obtain ⟨haty, vE, htie, hcond⟩ := ha
    simp only [AnnotOk]
    refine ⟨AnnotOk.unshift ty hpd hw'.1 haty, vE, htie, ?_⟩
    intro x A hA hx
    rw [← interp_shift ty hpd hw'.1 (x := x0)] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    rw [← shiftFrom_instantiate1 hpd, ← insV_updV hpd] at hbody hwfact
    refine ⟨AnnotOk.unshift _ (Nat.le_succ_of_le hpd)
      (hw'.1.instantiate1 0 hw'.2) hbody, ?_⟩
    obtain ⟨w, hwi, hmem⟩ := hwfact
    refine ⟨w, ?_, hmem⟩
    rw [← interp_shift _ (Nat.le_succ_of_le hpd)
      (hw'.1.instantiate1 0 hw'.2) (x := x0)]
    exact hwi
  | .lam n ty body m, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d ty ∧ WScoped d body := by simpa [WScoped] using hw
    simp only [shiftFrom, AnnotOk] at ha
    obtain ⟨haty, hcod, hcond⟩ := ha
    simp only [AnnotOk]
    refine ⟨AnnotOk.unshift ty hpd hw'.1 haty, hcod, ?_⟩
    intro x A hA hx
    rw [← interp_shift ty hpd hw'.1 (x := x0)] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    rw [← shiftFrom_instantiate1 hpd, ← insV_updV hpd] at hbody hwfact
    refine ⟨AnnotOk.unshift _ (Nat.le_succ_of_le hpd)
      (hw'.1.instantiate1 0 hw'.2) hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hwfact
    refine ⟨w, B, ?_, hwB, hBu⟩
    rw [← interp_shift _ (Nat.le_succ_of_le hpd)
      (hw'.1.instantiate1 0 hw'.2) (x := x0)]
    exact hwi
  | .app f a, d, p, ρ, x0, hpd, hw, ha => by
    simp only [WScoped] at hw
    simp only [shiftFrom, AnnotOk] at ha
    simp only [AnnotOk]
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hva, hfib⟩ := ha
    refine ⟨AnnotOk.unshift f hpd hw.1 haf, AnnotOk.unshift a hpd hw.2 haa,
      vf, va, vE, A, B, ?_, ?_, hpi, hva, hfib⟩
    · rw [← interp_shift f hpd hw.1 (x := x0)]; exact hfi
    · rw [← interp_shift a hpd hw.2 (x := x0)]; exact hai
  | .bvar _, _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .sort _, _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .const _ _, _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .fvar idx n ty, _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .letE n ty val body, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d ty ∧ WScoped d val ∧ WScoped d body := by
      simpa [WScoped] using hw
    simp only [shiftFrom, AnnotOk] at ha
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
    simp only [AnnotOk]
    rw [interp_shift val hpd hw'.2.1] at hxv
    rw [← shiftFrom_instantiate1 hpd, ← insV_updV hpd] at hopen
    exact ⟨AnnotOk.unshift ty hpd hw'.1 haty,
      AnnotOk.unshift val hpd hw'.2.1 hav, xv, hxv,
      AnnotOk.unshift _ (Nat.le_succ_of_le hpd)
        (hw'.1.instantiate1 0 hw'.2.2) hopen⟩
  | .lit _, _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .proj s' i e, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d e := by simpa [WScoped] using hw
    simp only [shiftFrom, AnnotOk] at ha
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := ha
    simp only [AnnotOk]
    refine ⟨AnnotOk.unshift e hpd hw' hae, hi2, ve, u', v', A, Bf, ?_,
      hsig, hAu, hBf⟩
    rw [← interp_shift e hpd hw' (x := x0)]; exact hvei
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Converse of `AnnotOk.weaken_top`: annotation truthfulness descends
from the extended frame for terms scoped below it. -/
theorem AnnotOk.strengthen_top {e : Expr} {d : Nat} {ρ : Nat → V} {x : V}
    (hw : WScoped d e)
    (ha : AnnotOk V cval env φ (d + 1) (updV V ρ d x) e) :
    AnnotOk V cval env φ d ρ e := by
  refine AnnotOk.unshift (x0 := x) e (Nat.le_refl d) hw ?_
  rw [shiftFrom_eq_self hw.fvarsBelow]
  exact AnnotOk.ext e
    (fun i hi => by simp only [insV, updV]; grind)
    (fvarsBelow_mono (Nat.le_succ d) hw.fvarsBelow) ha

/-- Weakening at the top for annotation truthfulness. -/
theorem AnnotOk.weaken_top {e : Expr} {d : Nat} {ρ : Nat → V} {x : V}
    (hw : WScoped d e) (ha : AnnotOk V cval env φ d ρ e) :
    AnnotOk V cval env φ (d + 1) (updV V ρ d x) e := by
  have h := AnnotOk.shift (x0 := x) e (Nat.le_refl d) hw ha
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  exact AnnotOk.ext e
    (fun i hi => by simp only [insV, updV]; grind)
    (fvarsBelow_mono (Nat.le_succ d) hw.fvarsBelow) h

/-- Closed terms: annotation truthfulness transports to any depth and
valuation. -/
theorem AnnotOk.closed_invariant {e : Expr} (hcl : e.hasFvar = false) :
    ∀ (d : Nat) (ρ : Nat → V),
      AnnotOk V cval env φ 0 (rho0 V) e → AnnotOk V cval env φ d ρ e
  | 0, ρ, ha =>
    AnnotOk.ext e (fun i hi => by omega)
      ((WScoped.of_not_hasFvar (d := 0) hcl).fvarsBelow) ha
  | d + 1, ρ, ha => by
    have hw : WScoped d e := WScoped.of_not_hasFvar hcl
    have h1 := AnnotOk.closed_invariant hcl d ρ ha
    have h2 := AnnotOk.shift (x0 := ρ d) e (Nat.le_refl d) hw h1
    rw [shiftFrom_eq_self hw.fvarsBelow] at h2
    exact AnnotOk.ext e
      (fun i hi => by simp only [insV]; grind)
      (fvarsBelow_mono (Nat.le_succ d) hw.fvarsBelow) h2

/-- Level instantiation for annotation truthfulness. -/
theorem AnnotOk.instLevels (hcp : ConstValParams cval env)
    {ks : List Name} {vs : List Level} :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      AnnotOk V cval env (Level.substFn φ ks vs) d ρ e →
      AnnotOk V cval env φ d ρ (e.instantiateLevelParams ks vs)
  | .forallE n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨haty, vE, htie, hcond⟩ := ha
    simp only [instantiateLevelParams, AnnotOk]
    refine ⟨AnnotOk.instLevels hcp ty d ρ haty, vE, ?_, ?_⟩
    · intro v' hv'
      simp only [Option.map_eq_some_iff] at hv'
      obtain ⟨v₀, hv₀, rfl⟩ := hv'
      rw [Level.eval_subst]
      exact htie v₀ hv₀
    · intro x A hA hx
      rw [interp_instLevels hcp ty d ρ] at hA
      obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
      rw [← instantiateLevelParams_instantiate1]
      refine ⟨AnnotOk.instLevels hcp _ (d + 1) (updV V ρ d x) hbody, ?_⟩
      obtain ⟨w, hwi, hmem⟩ := hwfact
      refine ⟨w, ?_, hmem⟩
      rw [interp_instLevels hcp _ (d + 1) (updV V ρ d x)]
      exact hwi
  | .lam n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨haty, vE, hcond⟩ := ha
    simp only [instantiateLevelParams, AnnotOk]
    refine ⟨AnnotOk.instLevels hcp ty d ρ haty, vE, ?_⟩
    intro x A hA hx
    rw [interp_instLevels hcp ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    rw [← instantiateLevelParams_instantiate1]
    refine ⟨AnnotOk.instLevels hcp _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hwfact
    refine ⟨w, B, ?_, hwB, hBu⟩
    rw [interp_instLevels hcp _ (d + 1) (updV V ρ d x)]
    exact hwi
  | .app f a, d, ρ, ha => by
    simp only [AnnotOk] at ha
    simp only [instantiateLevelParams, AnnotOk]
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hva, hfib⟩ := ha
    refine ⟨AnnotOk.instLevels hcp f d ρ haf, AnnotOk.instLevels hcp a d ρ haa,
      vf, va, vE, A, B, ?_, ?_, hpi, hva, hfib⟩
    · rw [interp_instLevels hcp f d ρ]; exact hfi
    · rw [interp_instLevels hcp a d ρ]; exact hai
  | .bvar _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .sort _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .const _ _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .fvar _ _ _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .letE n ty val body, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
    simp only [instantiateLevelParams, AnnotOk]
    refine ⟨AnnotOk.instLevels hcp ty d ρ haty,
      AnnotOk.instLevels hcp val d ρ hav, xv, ?_, ?_⟩
    · rw [interp_instLevels hcp val d ρ]; exact hxv
    · rw [← instantiateLevelParams_instantiate1]
      exact AnnotOk.instLevels hcp _ (d + 1) (updV V ρ d xv) hopen
  | .lit _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .proj s' i e, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := ha
    simp only [instantiateLevelParams, AnnotOk]
    refine ⟨AnnotOk.instLevels hcp e d ρ hae, hi2, ve, u', v', A, Bf, ?_, hsig, hAu, hBf⟩
    rw [interp_instLevels hcp e d ρ]; exact hvei
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Renaming constants along a `RenameOk` map preserves annotation
truthfulness (inversion direction: the renamed expression's
truthfulness yields the original's). -/
theorem AnnotOk_renameConsts {f : Name → Name}
    (hro : RenameOk cval env f) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      AnnotOk V cval env φ d ρ (e.renameConsts f) →
      AnnotOk V cval env φ d ρ e
  | .forallE n ty body m, d, ρ, ha => by
    simp only [Expr.renameConsts, AnnotOk] at ha
    obtain ⟨haty, vE, htie, hcond⟩ := ha
    simp only [AnnotOk]
    refine ⟨AnnotOk_renameConsts hro ty d ρ haty, vE, htie, ?_⟩
    intro x A hA hx
    rw [← interp_renameConsts hro ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    rw [← renameConsts_instantiate1] at hbody hwfact
    refine ⟨AnnotOk_renameConsts hro _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    obtain ⟨w, hwi, hmem⟩ := hwfact
    refine ⟨w, ?_, hmem⟩
    rw [← interp_renameConsts hro _ (d + 1) (updV V ρ d x)]
    exact hwi
  | .lam n ty body m, d, ρ, ha => by
    simp only [Expr.renameConsts, AnnotOk] at ha
    obtain ⟨haty, hcod, hcond⟩ := ha
    simp only [AnnotOk]
    refine ⟨AnnotOk_renameConsts hro ty d ρ haty, hcod, ?_⟩
    intro x A hA hx
    rw [← interp_renameConsts hro ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    rw [← renameConsts_instantiate1] at hbody hwfact
    refine ⟨AnnotOk_renameConsts hro _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hwfact
    refine ⟨w, B, ?_, hwB, hBu⟩
    rw [← interp_renameConsts hro _ (d + 1) (updV V ρ d x)]
    exact hwi
  | .app g a, d, ρ, ha => by
    simp only [Expr.renameConsts, AnnotOk] at ha
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hva, hfib⟩ := ha
    simp only [AnnotOk]
    refine ⟨AnnotOk_renameConsts hro g d ρ haf,
      AnnotOk_renameConsts hro a d ρ haa,
      vf, va, vE, A, B, ?_, ?_, hpi, hva, hfib⟩
    · rw [← interp_renameConsts hro g d ρ]; exact hfi
    · rw [← interp_renameConsts hro a d ρ]; exact hai
  | .bvar _, _, _, _ => by simp [AnnotOk, Expr.renameConsts]
  | .sort _, _, _, _ => by simp [AnnotOk, Expr.renameConsts]
  | .const _ _, _, _, _ => by simp [AnnotOk, Expr.renameConsts]
  | .fvar _ _ _, _, _, _ => by simp [AnnotOk, Expr.renameConsts]
  | .letE n ty val body, d, ρ, ha => by
    simp only [Expr.renameConsts, AnnotOk] at ha
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
    simp only [AnnotOk]
    rw [interp_renameConsts hro val d ρ] at hxv
    rw [← renameConsts_instantiate1] at hopen
    exact ⟨AnnotOk_renameConsts hro ty d ρ haty,
      AnnotOk_renameConsts hro val d ρ hav, xv, hxv,
      AnnotOk_renameConsts hro _ (d + 1) (updV V ρ d xv) hopen⟩
  | .lit _, _, _, _ => by simp [AnnotOk, Expr.renameConsts]
  | .proj s' i e, d, ρ, ha => by
    simp only [Expr.renameConsts, AnnotOk] at ha
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := ha
    simp only [AnnotOk]
    refine ⟨AnnotOk_renameConsts hro e d ρ hae, hi2, ve, u', v', A, Bf,
      ?_, hsig, hAu, hBf⟩
    rw [← interp_renameConsts hro e d ρ]
    exact hvei
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Environment monotonicity for annotation truthfulness. -/
theorem AnnotOk.mono {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V), e.constsResolve env = true →
      AnnotOk V cval env φ d ρ e →
      AnnotOk V cval (⟨c₀ :: env.consts⟩ : Env) φ d ρ e
  | .forallE n ty body m, d, ρ, hres, ha => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, vE, htie, hcond⟩ := ha
    refine ⟨AnnotOk.mono hfresh ty d ρ hres.1 haty, vE, htie, ?_⟩
    intro x A hA hx
    rw [interp_mono hfresh ty d ρ hres.1] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    refine ⟨AnnotOk.mono hfresh _ (d + 1) (updV V ρ d x)
      (constsResolve_instantiate1 hres.1 0 hres.2) hbody, ?_⟩
    obtain ⟨w, hwi, hmem⟩ := hwfact
    refine ⟨w, ?_, hmem⟩
    rw [interp_mono hfresh _ (d + 1) (updV V ρ d x)
      (constsResolve_instantiate1 hres.1 0 hres.2)]
    exact hwi
  | .lam n ty body m, d, ρ, hres, ha => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcod, hcond⟩ := ha
    refine ⟨AnnotOk.mono hfresh ty d ρ hres.1 haty, hcod, ?_⟩
    intro x A hA hx
    rw [interp_mono hfresh ty d ρ hres.1] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    refine ⟨AnnotOk.mono hfresh _ (d + 1) (updV V ρ d x)
      (constsResolve_instantiate1 hres.1 0 hres.2) hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hwfact
    refine ⟨w, B, ?_, hwB, hBu⟩
    rw [interp_mono hfresh _ (d + 1) (updV V ρ d x)
      (constsResolve_instantiate1 hres.1 0 hres.2)]
    exact hwi
  | .app f a, d, ρ, hres, ha => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hva, hfib⟩ := ha
    refine ⟨AnnotOk.mono hfresh f d ρ hres.1 haf, AnnotOk.mono hfresh a d ρ hres.2 haa,
      vf, va, vE, A, B, ?_, ?_, hpi, hva, hfib⟩
    · rw [interp_mono hfresh f d ρ hres.1]; exact hfi
    · rw [interp_mono hfresh a d ρ hres.2]; exact hai
  | .bvar _, _, _, _, _ => by simp [AnnotOk]
  | .sort _, _, _, _, _ => by simp [AnnotOk]
  | .const _ _, _, _, _, _ => by simp [AnnotOk]
  | .fvar _ _ _, _, _, _, _ => by simp [AnnotOk]
  | .letE n ty val body, d, ρ, hres, ha => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
    refine ⟨AnnotOk.mono hfresh ty d ρ hres.1.1 haty,
      AnnotOk.mono hfresh val d ρ hres.1.2 hav, xv, ?_, ?_⟩
    · rw [interp_mono hfresh val d ρ hres.1.2]; exact hxv
    · exact AnnotOk.mono hfresh _ (d + 1) (updV V ρ d xv)
        (constsResolve_instantiate1 hres.1.1 0 hres.2) hopen
  | .lit _, _, _, _, _ => by simp [AnnotOk]
  | .proj s' i e, d, ρ, hres, ha => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [AnnotOk] at ha ⊢
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := ha
    refine ⟨AnnotOk.mono hfresh e d ρ hres.2 hae, hi2, ve, u', v', A, Bf, ?_, hsig, hAu, hBf⟩
    rw [interp_mono hfresh e d ρ hres.2]; exact hvei
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Constant-valuation extensionality for annotation truthfulness. -/
theorem AnnotOk.cval_ext {cval₁ cval₂ : ConstVal V}
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat, cval₁ n ψ = cval₂ n ψ) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      AnnotOk V cval₁ env φ d ρ e → AnnotOk V cval₂ env φ d ρ e
  | .forallE n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, vE, htie, hcond⟩ := ha
    refine ⟨AnnotOk.cval_ext hagree ty d ρ haty, vE, htie, ?_⟩
    intro x A hA hx
    rw [← interp_cval_ext hagree ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    refine ⟨AnnotOk.cval_ext hagree _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    obtain ⟨w, hwi, hmem⟩ := hwfact
    refine ⟨w, ?_, hmem⟩
    rw [← interp_cval_ext hagree _ (d + 1) (updV V ρ d x)]
    exact hwi
  | .lam n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcod, hcond⟩ := ha
    refine ⟨AnnotOk.cval_ext hagree ty d ρ haty, hcod, ?_⟩
    intro x A hA hx
    rw [← interp_cval_ext hagree ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    refine ⟨AnnotOk.cval_ext hagree _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hwfact
    refine ⟨w, B, ?_, hwB, hBu⟩
    rw [← interp_cval_ext hagree _ (d + 1) (updV V ρ d x)]
    exact hwi
  | .app f a, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hva, hfib⟩ := ha
    refine ⟨AnnotOk.cval_ext hagree f d ρ haf, AnnotOk.cval_ext hagree a d ρ haa,
      vf, va, vE, A, B, ?_, ?_, hpi, hva, hfib⟩
    · rw [← interp_cval_ext hagree f d ρ]; exact hfi
    · rw [← interp_cval_ext hagree a d ρ]; exact hai
  | .bvar _, _, _, _ => by simp [AnnotOk]
  | .sort _, _, _, _ => by simp [AnnotOk]
  | .const _ _, _, _, _ => by simp [AnnotOk]
  | .fvar _ _ _, _, _, _ => by simp [AnnotOk]
  | .letE n ty val body, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
    refine ⟨AnnotOk.cval_ext hagree ty d ρ haty,
      AnnotOk.cval_ext hagree val d ρ hav, xv, ?_, ?_⟩
    · rw [← interp_cval_ext hagree val d ρ]; exact hxv
    · exact AnnotOk.cval_ext hagree _ (d + 1) (updV V ρ d xv) hopen
  | .lit _, _, _, _ => by simp [AnnotOk]
  | .proj s' i e, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := ha
    refine ⟨AnnotOk.cval_ext hagree e d ρ hae, hi2, ve, u', v', A, Bf, ?_, hsig, hAu, hBf⟩
    rw [← interp_cval_ext hagree e d ρ]; exact hvei
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Annotation truthfulness only reads the environment through the
interpretation, hence transfers between environments agreeing on level
parameters (e.g. differing only in a recursor's rule list). -/
theorem AnnotOk.env_ext {env₁ env₂ : Env}
    (henv : ∀ n, (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
        (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : natLitSupported env₁ = natLitSupported env₂)
    (hstr : strLitSupported env₁ = strLitSupported env₂) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      AnnotOk V cval env₁ φ d ρ e → AnnotOk V cval env₂ φ d ρ e
  | .forallE n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, vE, htie, hcond⟩ := ha
    refine ⟨AnnotOk.env_ext henv hnat hstr ty d ρ haty, vE, htie, ?_⟩
    intro x A hA hx
    rw [← interp_env_ext henv hnat hstr ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    refine ⟨AnnotOk.env_ext henv hnat hstr _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    obtain ⟨w, hwi, hmem⟩ := hwfact
    refine ⟨w, ?_, hmem⟩
    rw [← interp_env_ext henv hnat hstr _ (d + 1) (updV V ρ d x)]
    exact hwi
  | .lam n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcod, hcond⟩ := ha
    refine ⟨AnnotOk.env_ext henv hnat hstr ty d ρ haty, hcod, ?_⟩
    intro x A hA hx
    rw [← interp_env_ext henv hnat hstr ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    refine ⟨AnnotOk.env_ext henv hnat hstr _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    obtain ⟨w, B, hwi, hwB, hBu⟩ := hwfact
    refine ⟨w, B, ?_, hwB, hBu⟩
    rw [← interp_env_ext henv hnat hstr _ (d + 1) (updV V ρ d x)]
    exact hwi
  | .app f a, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haf, haa, vf, va, vE, A, B, hfi, hai, hpi, hva, hfib⟩ := ha
    refine ⟨AnnotOk.env_ext henv hnat hstr f d ρ haf, AnnotOk.env_ext henv hnat hstr a d ρ haa,
      vf, va, vE, A, B, ?_, ?_, hpi, hva, hfib⟩
    · rw [← interp_env_ext henv hnat hstr f d ρ]; exact hfi
    · rw [← interp_env_ext henv hnat hstr a d ρ]; exact hai
  | .bvar _, _, _, _ => by simp [AnnotOk]
  | .sort _, _, _, _ => by simp [AnnotOk]
  | .const _ _, _, _, _ => by simp [AnnotOk]
  | .fvar _ _ _, _, _, _ => by simp [AnnotOk]
  | .letE n ty val body, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hav, xv, hxv, hopen⟩ := ha
    refine ⟨AnnotOk.env_ext henv hnat hstr ty d ρ haty,
      AnnotOk.env_ext henv hnat hstr val d ρ hav, xv, ?_, ?_⟩
    · rw [← interp_env_ext henv hnat hstr val d ρ]; exact hxv
    · exact AnnotOk.env_ext henv hnat hstr _ (d + 1) (updV V ρ d xv) hopen
  | .lit _, _, _, _ => by simp [AnnotOk]
  | .proj s' i e, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨hae, hi2, ve, u', v', A, Bf, hvei, hsig, hAu, hBf⟩ := ha
    refine ⟨AnnotOk.env_ext henv hnat hstr e d ρ hae, hi2, ve, u', v', A, Bf, ?_, hsig, hAu, hBf⟩
    rw [← interp_env_ext henv hnat hstr e d ρ]; exact hvei
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end Setlec
