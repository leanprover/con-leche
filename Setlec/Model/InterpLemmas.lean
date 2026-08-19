import Setlec.Model.Interp
import Setlec.Verify.InferShift
import Setlec.Verify.EnvIrrel

/-!
# Weakening and stability lemmas for the interpretation

The lemma stack that lets soundness proofs step under a binder:

* `interp_ext`: the interpretation only reads the valuation at the indices
  of reachable free variables.
* `interp_shift`: inserting a value at position `p ≤ d` (and shifting the
  term) does not change the interpretation — the semantic weakening lemma.
* `interp_weaken_top`, `FvarsOk.weaken_top`: the common instance used when
  opening a binder (insert at the top, term unchanged).
* `FvarsOk.instantiate1`: opening a binder body with a fresh `fvar` valued
  by a member of the domain preserves the local-context assumptions — the
  induction step for every soundness theorem.
-/

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat}

open SetTheory Expr

/-- Insert `x` at position `p`, shifting the valuation above it. -/
def insV (ρ : Nat → V) (p : Nat) (x : V) : Nat → V :=
  fun i => if i < p then ρ i else if i = p then x else ρ (i - 1)

omit [SetTheory V] in
theorem insV_updV {ρ : Nat → V} {p d : Nat} {x x' : V} (hpd : p ≤ d) :
    insV (updV V ρ d x') p x = updV V (insV ρ p x) (d + 1) x' := by
  funext i
  simp only [insV, updV]
  grind

/-- `sortLevelOf` is shift invariant. -/
theorem sortLevelOf_shift {p d : Nat} {e : Expr} (hpd : p ≤ d) (hw : WScoped d e) :
    sortLevelOf env φ (d + 1) (shiftFrom p e) = sortLevelOf env φ d e := by
  unfold sortLevelOf
  rw [inferType_shift env e hpd hw]
  cases h : inferType env d e with
  | error err => rfl
  | ok t =>
    simp only [Functor.map, Except.map, Bind.bind, Except.bind, ensureSort_shift]

/-- The interpretation only reads the valuation at indices of reachable
free variables. -/
theorem interp_ext : ∀ (e : Expr) {d : Nat} {ρ ρ' : Nat → V},
    (∀ i, i < d → ρ i = ρ' i) → fvarsBelow d e →
    interpExpr V env φ d ρ e = interpExpr V env φ d ρ' e
  | .sort _, _, _, _, _, _ => by simp [interpExpr]
  | .fvar idx n ty, d, ρ, ρ', h, hb => by
    simp only [fvarsBelow] at hb
    simp only [interpExpr, h idx hb]
  | .forallE n ty body bi, d, ρ, ρ', h, hb => by
    simp only [fvarsBelow] at hb
    simp only [interpExpr]
    rw [interp_ext ty h hb.1]
    cases hty : interpExpr V env φ d ρ' ty with
    | none => rfl
    | some A =>
      simp only []
      cases hv : sortLevelOf env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some vE =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_ext (body.instantiate1 (.fvar d n ty))
          (ρ := updV V ρ d x) (ρ' := updV V ρ' d x)
          (fun i hi => by
            simp only [updV]
            split
            · rfl
            · exact h i (by omega))
          (fvarsBelow_instantiate1 0 hb.2)]
  | .bvar _, _, _, _, _, _ => by simp [interpExpr]
  | .const _ _, _, _, _, _, _ => by simp [interpExpr]
  | .app _ _, _, _, _, _, _ => by simp [interpExpr]
  | .lam _ _ _ _, _, _, _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _, _, _, _ => by simp [interpExpr]
  | .lit _, _, _, _, _, _ => by simp [interpExpr]
  | .proj _ _ _, _, _, _, _, _ => by simp [interpExpr]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- Semantic weakening: inserting a value at `p ≤ d` and shifting the term
leaves the interpretation unchanged. -/
theorem interp_shift : ∀ (e : Expr) {d p : Nat} {ρ : Nat → V} {x : V},
    p ≤ d → WScoped d e →
    interpExpr V env φ (d + 1) (insV ρ p x) (shiftFrom p e) = interpExpr V env φ d ρ e
  | .sort _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .fvar idx n ty, d, p, ρ, x, hpd, hw => by
    simp only [shiftFrom]
    split
    · simp only [interpExpr, insV]
      have : ¬ (idx + 1 < p) := by omega
      have h2 : ¬ (idx + 1 = p) := by omega
      simp [this, h2]
    · simp only [interpExpr, insV]
      have : idx < p := by omega
      simp [this]
  | .forallE n ty body bi, d, p, ρ, x, hpd, hw => by
    have hw' : WScoped d ty ∧ WScoped d body := by simpa [WScoped] using hw
    simp only [shiftFrom, interpExpr]
    rw [← shiftFrom_instantiate1 hpd]
    rw [interp_shift ty hpd hw'.1]
    cases hty : interpExpr V env φ d ρ ty with
    | none => rfl
    | some A =>
      simp only []
      rw [sortLevelOf_shift (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
      cases hv : sortLevelOf env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some vE =>
        simp only [Option.some.injEq]
        congr 1
        funext x'
        rw [← insV_updV hpd,
          interp_shift (body.instantiate1 (.fvar d n ty))
            (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
  | .bvar _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .const _ _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .app _ _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .lam _ _ _ _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .letE _ _ _ _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .lit _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .proj _ _ _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- Weakening at the top: valuing a fresh top variable does not change the
interpretation of a term scoped below it. -/
theorem interp_weaken_top {e : Expr} {d : Nat} {ρ : Nat → V} {x : V}
    (hw : WScoped d e) :
    interpExpr V env φ (d + 1) (updV V ρ d x) e = interpExpr V env φ d ρ e := by
  have h := interp_shift (env := env) (φ := φ) e (ρ := ρ) (x := x) (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [← h]
  exact interp_ext e
    (fun i hi => by simp only [insV, updV]; grind)
    (fvarsBelow_mono (Nat.le_succ d) hw.fvarsBelow)

/-- `FvarsOk` only reads the valuation below `d`. -/
theorem FvarsOk.ext : ∀ (e : Expr) {d : Nat} {ρ ρ' : Nat → V},
    (∀ i, i < d → ρ i = ρ' i) → WScoped d e →
    FvarsOk V env φ d ρ e → FvarsOk V env φ d ρ' e
  | .fvar idx n ty, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    obtain ⟨hidx, hty, T, hT, hmem⟩ := hok
    refine ⟨hidx, FvarsOk.ext ty h (hw.2.mono (by omega)) hty, T, ?_, ?_⟩
    · rw [← interp_ext ty h (fvarsBelow_mono (by omega) hw.2.fvarsBelow)]
      exact hT
    · rw [← h idx hidx]; exact hmem
  | .app f a, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.ext f h hw.1 hok.1, FvarsOk.ext a h hw.2 hok.2⟩
  | .lam n ty body bi, d, ρ, ρ', h, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.ext ty h hw.1 hok.1, FvarsOk.ext body h hw.2 hok.2⟩
  | .forallE n ty body bi, d, ρ, ρ', h, hw, hok => by
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
theorem FvarsOk.weaken_top : ∀ (e : Expr) {d : Nat} {ρ : Nat → V} {x : V},
    WScoped d e → FvarsOk V env φ d ρ e → FvarsOk V env φ (d + 1) (updV V ρ d x) e
  | .fvar idx n ty, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    obtain ⟨hidx, hty, T, hT, hmem⟩ := hok
    refine ⟨by omega, FvarsOk.weaken_top ty (hw.2.mono (by omega)) hty, T, ?_, ?_⟩
    · rw [interp_weaken_top (hw.2.mono (by omega))]
      exact hT
    · simp only [updV]
      have : idx ≠ d := by omega
      simp [this, hmem]
  | .app f a, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top f hw.1 hok.1, FvarsOk.weaken_top a hw.2 hok.2⟩
  | .lam n ty body bi, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top ty hw.1 hok.1, FvarsOk.weaken_top body hw.2 hok.2⟩
  | .forallE n ty body bi, d, ρ, x, hw, hok => by
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

/-- Opening a binder preserves the local-context assumptions: substituting
`fvar d n ty` for the bound variable and valuing it with a member `x` of
the domain's interpretation. -/
theorem FvarsOk.instantiate1 {d : Nat} {n : Name} {ty : Expr} {ρ : Nat → V} {x A : V}
    (hwty : WScoped d ty) (hty : FvarsOk V env φ d ρ ty)
    (hA : interpExpr V env φ d ρ ty = some A) (hx : x ∈ˢ A) :
    ∀ (body : Expr) (k : Nat), WScoped d body → FvarsOk V env φ d ρ body →
      FvarsOk V env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty) k)
  | .bvar i, k, _, _ => by
    simp only [Expr.instantiate1]
    split
    · simp only [FvarsOk]
      refine ⟨Nat.lt_succ_self d, FvarsOk.weaken_top ty hwty hty, A, ?_, ?_⟩
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
    exact ⟨FvarsOk.instantiate1 hwty hty hA hx f k hw.1 hok.1,
      FvarsOk.instantiate1 hwty hty hA hx a k hw.2 hok.2⟩
  | .lam n' ty' body' bi, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 hwty hty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 hwty hty hA hx body' (k + 1) hw.2 hok.2⟩
  | .forallE n' ty' body' bi, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 hwty hty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 hwty hty hA hx body' (k + 1) hw.2 hok.2⟩
  | .letE n' ty' val' body', k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 hwty hty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 hwty hty hA hx val' k hw.2.1 hok.2.1,
      FvarsOk.instantiate1 hwty hty hA hx body' (k + 1) hw.2.2 hok.2.2⟩
  | .proj s i e, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact FvarsOk.instantiate1 hwty hty hA hx e k hw hok
  | .sort _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]
  | .const _ _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]
  | .lit _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]

/-- `sortLevelOf` ignores the environment (current fragment; becomes
monotonicity in task 2). -/
theorem sortLevelOf_env_irrel (env env' : Env) (d : Nat) (e : Expr) :
    sortLevelOf env φ d e = sortLevelOf env' φ d e := by
  unfold sortLevelOf
  rw [inferType_env_irrel env env',
    show ensureSort env = ensureSort env' from funext (ensureSort_env_irrel env env')]

/-- The interpretation ignores the environment (current fragment). -/
theorem interp_env_irrel (env env' : Env) : ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
    interpExpr V env φ d ρ e = interpExpr V env' φ d ρ e
  | .sort _, _, _ => by simp [interpExpr]
  | .fvar _ _ _, _, _ => by simp [interpExpr]
  | .forallE n ty body bi, d, ρ => by
    simp only [interpExpr]
    rw [interp_env_irrel env env' ty d ρ,
      sortLevelOf_env_irrel env env' (d + 1) (body.instantiate1 (.fvar d n ty))]
    cases interpExpr V env' φ d ρ ty with
    | none => rfl
    | some A =>
      simp only []
      cases sortLevelOf env' φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some vE =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_env_irrel env env' (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x)]
  | .bvar _, _, _ => by simp [interpExpr]
  | .const _ _, _, _ => by simp [interpExpr]
  | .app _ _, _, _ => by simp [interpExpr]
  | .lam _ _ _ _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _ => by simp [interpExpr]
  | .lit _, _, _ => by simp [interpExpr]
  | .proj _ _ _, _, _ => by simp [interpExpr]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

theorem interpClosed_env_irrel (env env' : Env) (e : Expr) :
    interpClosed V env φ e = interpClosed V env' φ e :=
  interp_env_irrel env env' e 0 (rho0 V)

/-- Closed expressions vacuously satisfy the local-context assumptions. -/
theorem FvarsOk.of_not_hasFvar : ∀ {e : Expr} (_ : e.hasFvar = false)
    {d : Nat} {ρ : Nat → V}, FvarsOk V env φ d ρ e := by
  intro e
  induction e <;> intro h d ρ <;> simp_all [Expr.hasFvar, FvarsOk]

end Setlec
