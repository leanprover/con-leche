import Setlec.Model.AnnotOkLemmas
import Setlec.Verify.Abstract

/-!
# Transport lemmas for the local-context assumptions (`FvarsOk`)

Valuation extensionality, weakening at the top, closedness, and — the
induction step of every soundness theorem — preservation under opening a
binder (`FvarsOk.instantiate1`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat} {cval : ConstVal V}

open SetTheory Expr

/-- `FvarsOk` only reads the valuation below `d`. -/
theorem FvarsOk.ext : ∀ (e : Expr) {d : Nat} {ρ ρ' : Nat → V},
    (∀ i, i < d → ρ i = ρ' i) → WScoped d e →
    FvarsOk V cval env φ d ρ e → FvarsOk V cval env φ d ρ' e
  | .fvar idx n ty, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    obtain ⟨hidx, haty, T, hT, hmem⟩ := hok
    refine ⟨hidx,
      AnnotOk.ext ty h (fvarsBelow_mono (by omega) hw.2.fvarsBelow) haty, T, ?_, ?_⟩
    · rw [← interp_ext ty h (fvarsBelow_mono (by omega) hw.2.fvarsBelow)]
      exact hT
    · rw [← h idx hidx]; exact hmem
  | .app f a, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.ext f h hw.1 hok.1, FvarsOk.ext a h hw.2 hok.2⟩
  | .lam n ty body m, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.ext ty h hw.1 hok.1, FvarsOk.ext body h hw.2 hok.2⟩
  | .forallE n ty body m, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.ext ty h hw.1 hok.1, FvarsOk.ext body h hw.2 hok.2⟩
  | .letE n ty val body, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.ext ty h hw.1 hok.1, FvarsOk.ext val h hw.2.1 hok.2.1,
      FvarsOk.ext body h hw.2.2 hok.2.2⟩
  | .proj s i e, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact FvarsOk.ext e h hw hok
  | .bvar _, _, _, _, _, _, _ => by simp [FvarsOk]
  | .sort _, _, _, _, _, _, _ => by simp [FvarsOk]
  | .const _ _, _, _, _, _, _, _ => by simp [FvarsOk]
  | .lit _, _, _, _, _, _, _ => by simp [FvarsOk]
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Weakening at the top for the local-context assumptions. -/
theorem FvarsOk.weaken_top :
    ∀ (e : Expr) {d : Nat} {ρ : Nat → V} {x : V},
    WScoped d e → FvarsOk V cval env φ d ρ e →
    FvarsOk V cval env φ (d + 1) (updV V ρ d x) e
  | .fvar idx n ty, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    obtain ⟨hidx, haty, T, hT, hmem⟩ := hok
    refine ⟨by omega,
      AnnotOk.weaken_top (hw.2.mono (by omega)) haty, T, ?_, ?_⟩
    · rw [interp_weaken_top (hw.2.mono (by omega))]
      exact hT
    · simp only [updV]
      have : idx ≠ d := by omega
      simp [this, hmem]
  | .app f a, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top f hw.1 hok.1, FvarsOk.weaken_top a hw.2 hok.2⟩
  | .lam n ty body m, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top ty hw.1 hok.1, FvarsOk.weaken_top body hw.2 hok.2⟩
  | .forallE n ty body m, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top ty hw.1 hok.1, FvarsOk.weaken_top body hw.2 hok.2⟩
  | .letE n ty val body, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top ty hw.1 hok.1, FvarsOk.weaken_top val hw.2.1 hok.2.1,
      FvarsOk.weaken_top body hw.2.2 hok.2.2⟩
  | .proj s i e, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact FvarsOk.weaken_top e hw hok
  | .bvar _, _, _, _, _, _ => by simp [FvarsOk]
  | .sort _, _, _, _, _, _ => by simp [FvarsOk]
  | .const _ _, _, _, _, _, _ => by simp [FvarsOk]
  | .lit _, _, _, _, _, _ => by simp [FvarsOk]
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Opening a binder preserves the local-context assumptions: the fresh
variable is valued by a member of the domain's interpretation, whose
annotation truthfulness is supplied alongside. -/
theorem FvarsOk.instantiate1 {d : Nat} {n : Name} {ty : Expr}
    {ρ : Nat → V} {x A : V}
    (hwty : WScoped d ty)
    (haty : AnnotOk V cval env φ d ρ ty)
    (hA : interpExpr V cval env φ d ρ ty = some A) (hx : x ∈ˢ A) :
    ∀ (body : Expr) (k : Nat), WScoped d body → FvarsOk V cval env φ d ρ body →
      FvarsOk V cval env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty) k)
  | .bvar i, k, _, _ => by
    simp only [Expr.instantiate1]
    split
    · simp only [FvarsOk]
      refine ⟨Nat.lt_succ_self d,
        AnnotOk.weaken_top hwty haty, A, ?_, ?_⟩
      · rw [interp_weaken_top hwty]; exact hA
      · simp [updV, hx]
    · split <;> simp [FvarsOk]
  | .fvar idx n' ty', k, hw, hok => by
    simp only [Expr.instantiate1]
    exact FvarsOk.weaken_top _ hw hok
  | .app f a, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 hwty haty hA hx f k hw.1 hok.1,
      FvarsOk.instantiate1 hwty haty hA hx a k hw.2 hok.2⟩
  | .lam n' ty' body' m, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 hwty haty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 hwty haty hA hx body' (k + 1) hw.2 hok.2⟩
  | .forallE n' ty' body' m, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 hwty haty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 hwty haty hA hx body' (k + 1) hw.2 hok.2⟩
  | .letE n' ty' val' body', k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 hwty haty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 hwty haty hA hx val' k hw.2.1 hok.2.1,
      FvarsOk.instantiate1 hwty haty hA hx body' (k + 1) hw.2.2 hok.2.2⟩
  | .proj s i e, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact FvarsOk.instantiate1 hwty haty hA hx e k hw hok
  | .sort _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]
  | .const _ _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]
  | .lit _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]

/-- Closed expressions vacuously satisfy the local-context assumptions. -/
theorem FvarsOk.of_not_hasFvar : ∀ {e : Expr} (_ : e.hasFvar = false)
    {d : Nat} {ρ : Nat → V}, FvarsOk V cval env φ d ρ e := by
  intro e
  induction e <;> intro h d ρ <;> simp_all [Expr.hasFvar, FvarsOk]



/-- `FvarsOk` only sees skeleton and leaves, so it transports across
`Expr.LeafEquiv`. -/
theorem FvarsOk.congr : ∀ (e₁ e₂ : Expr), Expr.LeafEquiv e₁ e₂ →
    ∀ {d : Nat} {ρ : Nat → V},
    FvarsOk V cval env φ d ρ e₁ → FvarsOk V cval env φ d ρ e₂ := by
  intro e₁
  induction e₁ with
  | fvar idx n ty _ =>
    intro e₂ hle d ρ hok
    cases e₂ with
    | fvar idx' n' ty' =>
      simp only [Expr.LeafEquiv] at hle
      obtain ⟨rfl, rfl, rfl⟩ := hle
      exact hok
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | app f a ihf iha =>
    intro e₂ hle d ρ hok
    cases e₂ with
    | app f' a' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [FvarsOk] at hok ⊢
      exact ⟨ihf f' hle.1 hok.1, iha a' hle.2 hok.2⟩
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | lam n ty body m ihty ihbody =>
    intro e₂ hle d ρ hok
    cases e₂ with
    | lam n' ty' body' m' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [FvarsOk] at hok ⊢
      exact ⟨ihty ty' hle.1 hok.1, ihbody body' hle.2 hok.2⟩
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | forallE n ty body m ihty ihbody =>
    intro e₂ hle d ρ hok
    cases e₂ with
    | forallE n' ty' body' m' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [FvarsOk] at hok ⊢
      exact ⟨ihty ty' hle.1 hok.1, ihbody body' hle.2 hok.2⟩
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | letE n ty val body ihty ihval ihbody =>
    intro e₂ hle d ρ hok
    cases e₂ with
    | letE n' ty' val' body' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [FvarsOk] at hok ⊢
      exact ⟨ihty ty' hle.1 hok.1, ihval val' hle.2.1 hok.2.1, ihbody body' hle.2.2 hok.2.2⟩
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | proj s i e ih =>
    intro e₂ hle d ρ hok
    cases e₂ with
    | proj s' i' e' =>
      simp only [Expr.LeafEquiv] at hle
      simp only [FvarsOk] at hok ⊢
      exact ih e' hle hok
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | bvar i =>
    intro e₂ hle d ρ _
    cases e₂ with
    | bvar j => simp [FvarsOk]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | sort u =>
    intro e₂ hle d ρ _
    cases e₂ with
    | sort u' => simp [FvarsOk]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | const n us =>
    intro e₂ hle d ρ _
    cases e₂ with
    | const n' us' => simp [FvarsOk]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])
  | lit l =>
    intro e₂ hle d ρ _
    cases e₂ with
    | lit l' => simp [FvarsOk]
    | _ => exact absurd hle (by simp [Expr.LeafEquiv])

end Setlec
