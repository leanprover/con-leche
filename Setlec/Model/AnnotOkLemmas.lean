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
    intro v hv
    obtain ⟨w, hwi, hmem⟩ := hw v hv
    exact ⟨w, by rw [← interp_ext _ hupd (fvarsBelow_instantiate1 0 hb.2)]; exact hwi, hmem⟩
  | .lam n ty body m, d, ρ, ρ', h, hb, ha => by
    simp only [fvarsBelow] at hb
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcond⟩ := ha
    refine ⟨AnnotOk.ext ty h hb.1 haty, ?_⟩
    intro x A hA hx
    rw [← interp_ext ty h hb.1] at hA
    have hupd : ∀ i, i < d + 1 → updV V ρ d x i = updV V ρ' d x i := by
      intro i hi
      simp only [updV]
      split
      · rfl
      · exact h i (by omega)
    exact AnnotOk.ext _ hupd (fvarsBelow_instantiate1 0 hb.2) (hcond x A hA hx)
  | .app f a, d, ρ, ρ', h, hb, ha => by
    simp only [fvarsBelow] at hb
    simp only [AnnotOk] at ha ⊢
    exact ⟨AnnotOk.ext f h hb.1 ha.1, AnnotOk.ext a h hb.2 ha.2⟩
  | .bvar _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .sort _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .const _ _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .fvar _ _ _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .letE _ _ _ _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .lit _, _, _, _, _, _, _ => by simp [AnnotOk]
  | .proj _ _ _, _, _, _, _, _, _ => by simp [AnnotOk]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

theorem AnnotOk.shift : ∀ (e : Expr) {d p : Nat} {ρ : Nat → V} {x0 : V},
    p ≤ d → WScoped d e →
    AnnotOk V cval env φ d ρ e →
    AnnotOk V cval env φ (d + 1) (insV ρ p x0) (shiftFrom p e)
  | .forallE n ty body m, d, p, ρ, x0, hpd, hw, ha => by
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
    intro v hv
    obtain ⟨w, hwi, hmem⟩ := hwfact v hv
    refine ⟨w, ?_, hmem⟩
    rw [interp_shift _ (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
    exact hwi
  | .lam n ty body m, d, p, ρ, x0, hpd, hw, ha => by
    have hw' : WScoped d ty ∧ WScoped d body := by simpa [WScoped] using hw
    simp only [AnnotOk] at ha
    obtain ⟨haty, hcond⟩ := ha
    simp only [shiftFrom, AnnotOk]
    refine ⟨AnnotOk.shift ty hpd hw'.1 haty, ?_⟩
    intro x A hA hx
    rw [interp_shift ty hpd hw'.1] at hA
    rw [← shiftFrom_instantiate1 hpd, ← insV_updV hpd]
    exact AnnotOk.shift _ (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)
      (hcond x A hA hx)
  | .app f a, d, p, ρ, x0, hpd, hw, ha => by
    simp only [WScoped] at hw
    simp only [AnnotOk] at ha
    simp only [shiftFrom, AnnotOk]
    exact ⟨AnnotOk.shift f hpd hw.1 ha.1, AnnotOk.shift a hpd hw.2 ha.2⟩
  | .bvar _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .sort _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .const _ _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .fvar idx n ty, _, _, _, _, _, _, _ => by
    simp only [shiftFrom]
    split <;> simp [AnnotOk]
  | .letE _ _ _ _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .lit _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
  | .proj _ _ _, _, _, _, _, _, _, _ => by simp [AnnotOk, shiftFrom]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

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
    obtain ⟨haty, ⟨v, hv⟩, hcond⟩ := ha
    simp only [instantiateLevelParams, AnnotOk]
    refine ⟨AnnotOk.instLevels hcp ty d ρ haty, ⟨Level.subst ks vs v, by simp [hv]⟩, ?_⟩
    intro x A hA hx
    rw [interp_instLevels hcp ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    rw [← instantiateLevelParams_instantiate1]
    refine ⟨AnnotOk.instLevels hcp _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    intro v' hv'
    simp only [hv, Option.map_some, Option.some.injEq] at hv'
    obtain ⟨w, hwi, hmem⟩ := hwfact v hv
    refine ⟨w, ?_, ?_⟩
    · rw [interp_instLevels hcp _ (d + 1) (updV V ρ d x)]
      exact hwi
    · rw [← hv', Level.eval_subst]
      exact hmem
  | .lam n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha
    obtain ⟨haty, hcond⟩ := ha
    simp only [instantiateLevelParams, AnnotOk]
    refine ⟨AnnotOk.instLevels hcp ty d ρ haty, ?_⟩
    intro x A hA hx
    rw [interp_instLevels hcp ty d ρ] at hA
    rw [← instantiateLevelParams_instantiate1]
    exact AnnotOk.instLevels hcp _ (d + 1) (updV V ρ d x) (hcond x A hA hx)
  | .app f a, d, ρ, ha => by
    simp only [AnnotOk] at ha
    simp only [instantiateLevelParams, AnnotOk]
    exact ⟨AnnotOk.instLevels hcp f d ρ ha.1, AnnotOk.instLevels hcp a d ρ ha.2⟩
  | .bvar _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .sort _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .const _ _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .fvar _ _ _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .letE _ _ _ _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .lit _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
  | .proj _ _ _, _, _, _ => by simp [AnnotOk, instantiateLevelParams]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

/-- Environment monotonicity for annotation truthfulness. -/
theorem AnnotOk.mono {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V), e.constsResolve env = true →
      AnnotOk V cval env φ d ρ e →
      AnnotOk V cval (⟨c₀ :: env.consts⟩ : Env) φ d ρ e
  | .forallE n ty body m, d, ρ, hres, ha => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcod, hcond⟩ := ha
    refine ⟨AnnotOk.mono hfresh ty d ρ hres.1 haty, hcod, ?_⟩
    intro x A hA hx
    rw [interp_mono hfresh ty d ρ hres.1] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    refine ⟨AnnotOk.mono hfresh _ (d + 1) (updV V ρ d x)
      (constsResolve_instantiate1 hres.1 0 hres.2) hbody, ?_⟩
    intro v hv
    obtain ⟨w, hwi, hmem⟩ := hwfact v hv
    refine ⟨w, ?_, hmem⟩
    rw [interp_mono hfresh _ (d + 1) (updV V ρ d x)
      (constsResolve_instantiate1 hres.1 0 hres.2)]
    exact hwi
  | .lam n ty body m, d, ρ, hres, ha => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcond⟩ := ha
    refine ⟨AnnotOk.mono hfresh ty d ρ hres.1 haty, ?_⟩
    intro x A hA hx
    rw [interp_mono hfresh ty d ρ hres.1] at hA
    exact AnnotOk.mono hfresh _ (d + 1) (updV V ρ d x)
      (constsResolve_instantiate1 hres.1 0 hres.2) (hcond x A hA hx)
  | .app f a, d, ρ, hres, ha => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [AnnotOk] at ha ⊢
    exact ⟨AnnotOk.mono hfresh f d ρ hres.1 ha.1, AnnotOk.mono hfresh a d ρ hres.2 ha.2⟩
  | .bvar _, _, _, _, _ => by simp [AnnotOk]
  | .sort _, _, _, _, _ => by simp [AnnotOk]
  | .const _ _, _, _, _, _ => by simp [AnnotOk]
  | .fvar _ _ _, _, _, _, _ => by simp [AnnotOk]
  | .letE _ _ _ _, _, _, _, _ => by simp [AnnotOk]
  | .lit _, _, _, _, _ => by simp [AnnotOk]
  | .proj _ _ _, _, _, _, _ => by simp [AnnotOk]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

/-- Constant-valuation extensionality for annotation truthfulness. -/
theorem AnnotOk.cval_ext {cval₁ cval₂ : ConstVal V}
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat, cval₁ n ψ = cval₂ n ψ) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      AnnotOk V cval₁ env φ d ρ e → AnnotOk V cval₂ env φ d ρ e
  | .forallE n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcod, hcond⟩ := ha
    refine ⟨AnnotOk.cval_ext hagree ty d ρ haty, hcod, ?_⟩
    intro x A hA hx
    rw [← interp_cval_ext hagree ty d ρ] at hA
    obtain ⟨hbody, hwfact⟩ := hcond x A hA hx
    refine ⟨AnnotOk.cval_ext hagree _ (d + 1) (updV V ρ d x) hbody, ?_⟩
    intro v hv
    obtain ⟨w, hwi, hmem⟩ := hwfact v hv
    refine ⟨w, ?_, hmem⟩
    rw [← interp_cval_ext hagree _ (d + 1) (updV V ρ d x)]
    exact hwi
  | .lam n ty body m, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    obtain ⟨haty, hcond⟩ := ha
    refine ⟨AnnotOk.cval_ext hagree ty d ρ haty, ?_⟩
    intro x A hA hx
    rw [← interp_cval_ext hagree ty d ρ] at hA
    exact AnnotOk.cval_ext hagree _ (d + 1) (updV V ρ d x) (hcond x A hA hx)
  | .app f a, d, ρ, ha => by
    simp only [AnnotOk] at ha ⊢
    exact ⟨AnnotOk.cval_ext hagree f d ρ ha.1, AnnotOk.cval_ext hagree a d ρ ha.2⟩
  | .bvar _, _, _, _ => by simp [AnnotOk]
  | .sort _, _, _, _ => by simp [AnnotOk]
  | .const _ _, _, _, _ => by simp [AnnotOk]
  | .fvar _ _ _, _, _, _ => by simp [AnnotOk]
  | .letE _ _ _ _, _, _, _ => by simp [AnnotOk]
  | .lit _, _, _, _ => by simp [AnnotOk]
  | .proj _ _ _, _, _, _ => by simp [AnnotOk]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

end Setlec
