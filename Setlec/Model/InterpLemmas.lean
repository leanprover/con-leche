import Setlec.Model.Interp
import Setlec.Verify.InferShift
import Setlec.Verify.InstLevels

/-!
# Weakening and stability lemmas for the interpretation

The lemma stack behind the soundness proofs:

* `interp_ext`, `interp_shift`, `interp_weaken_top`, `FvarsOk.weaken_top`,
  `FvarsOk.instantiate1` — stepping under a binder;
* `interp_instLevels` — level instantiation corresponds to composing the
  level assignment (`Level.substFn`);
* `interp_params_ext` — the interpretation reads the level assignment only
  at the expression's level parameters;
* `interp_mono` — stability under extending the environment with a fresh
  constant;
* `interp_closed_invariant` — closed terms are interpreted independently
  of depth and valuation.

Several need `EnvWF` (reduction may unfold stored definitions) and
`ConstValParams` (constant values only read their own parameters).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {env : Env} {φ : Name → Nat} {cval : ConstVal V}

open SetTheory Expr

/-- The constant valuation only reads each constant's own parameters. -/
def ConstValParams (cval : ConstVal V) (env : Env) : Prop :=
  ∀ n ci, env.find? n = some ci →
    ∀ φ₁ φ₂ : Name → Nat, (∀ p ∈ ci.toConstantVal.levelParams, φ₁ p = φ₂ p) →
      cval n φ₁ = cval n φ₂

/-- The `const` clause of the interpretation, as an equation. -/
theorem interp_const {n : Name} {ws : List Level} {ci : ConstantInfo} {d : Nat} {ρ : Nat → V}
    (hf : env.find? n = some ci)
    (hal : ws.length = ci.toConstantVal.levelParams.length) :
    interpExpr V cval env φ d ρ (.const n ws) =
      some (cval n (Level.substFn φ ci.toConstantVal.levelParams ws)) := by
  simp only [interpExpr, hf]
  rw [if_pos hal]

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
theorem sortLevelOf_shift (henv : EnvWF env) {p d : Nat} {e : Expr} (hpd : p ≤ d)
    (hw : WScoped d e) :
    sortLevelOf env φ (d + 1) (shiftFrom p e) = sortLevelOf env φ d e := by
  unfold sortLevelOf
  rw [inferType_shift henv e hpd hw]
  cases h : inferType env d e with
  | error err => rfl
  | ok t =>
    simp only [Functor.map, Except.map, Bind.bind, Except.bind, ensureSort_shift henv]

/-- `sortLevelOf` after level instantiation composes the assignment. -/
theorem sortLevelOf_instLevels (henv : EnvWF env) (ks : List Name) (vs : List Level)
    (d : Nat) (e : Expr) :
    sortLevelOf env φ d (e.instantiateLevelParams ks vs) =
      sortLevelOf env (Level.substFn φ ks vs) d e := by
  unfold sortLevelOf
  rw [inferType_instLevels henv ks vs e d]
  cases h : inferType env d e with
  | error err => rfl
  | ok t =>
    simp only [Except.map, Bind.bind, Except.bind, ensureSort_instLevels henv]
    cases hs : ensureSort env t with
    | error e => rfl
    | ok u => simp [Except.map, Level.eval_subst]

/-- `sortLevelOf` is stable under a fresh environment extension. -/
theorem sortLevelOf_mono {c₀ : ConstantInfo} (henv : EnvWF env)
    (hfresh : env.find? c₀.name = none) {d : Nat} {e : Expr}
    (hres : e.constsResolve env = true) :
    sortLevelOf (⟨c₀ :: env.consts⟩ : Env) φ d e = sortLevelOf env φ d e := by
  unfold sortLevelOf
  rw [inferType_mono henv hfresh e d hres]
  cases h : inferType env d e with
  | error err => rfl
  | ok t =>
    simp only [Bind.bind, Except.bind]
    rw [ensureSort_mono henv hfresh (inferType_constsResolve henv e h hres)]

/-- The interpretation only reads the valuation at indices of reachable
free variables. -/
theorem interp_ext : ∀ (e : Expr) {d : Nat} {ρ ρ' : Nat → V},
    (∀ i, i < d → ρ i = ρ' i) → fvarsBelow d e →
    interpExpr V cval env φ d ρ e = interpExpr V cval env φ d ρ' e
  | .sort _, _, _, _, _, _ => by simp [interpExpr]
  | .const _ _, _, _, _, _, _ => by simp [interpExpr]
  | .fvar idx n ty, d, ρ, ρ', h, hb => by
    simp only [fvarsBelow] at hb
    simp only [interpExpr, h idx hb]
  | .forallE n ty body bi, d, ρ, ρ', h, hb => by
    simp only [fvarsBelow] at hb
    simp only [interpExpr]
    rw [interp_ext ty h hb.1]
    cases hty : interpExpr V cval env φ d ρ' ty with
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
theorem interp_shift (henv : EnvWF env) : ∀ (e : Expr) {d p : Nat} {ρ : Nat → V} {x : V},
    p ≤ d → WScoped d e →
    interpExpr V cval env φ (d + 1) (insV ρ p x) (shiftFrom p e) =
      interpExpr V cval env φ d ρ e
  | .sort _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .const _ _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
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
    rw [interp_shift henv ty hpd hw'.1]
    cases hty : interpExpr V cval env φ d ρ ty with
    | none => rfl
    | some A =>
      simp only []
      rw [sortLevelOf_shift henv (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
      cases hv : sortLevelOf env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some vE =>
        simp only [Option.some.injEq]
        congr 1
        funext x'
        rw [← insV_updV hpd,
          interp_shift henv (body.instantiate1 (.fvar d n ty))
            (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
  | .bvar _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
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
theorem interp_weaken_top (henv : EnvWF env) {e : Expr} {d : Nat} {ρ : Nat → V} {x : V}
    (hw : WScoped d e) :
    interpExpr V cval env φ (d + 1) (updV V ρ d x) e = interpExpr V cval env φ d ρ e := by
  have h := interp_shift (cval := cval) (φ := φ) henv e (ρ := ρ) (x := x) (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [← h]
  exact interp_ext e
    (fun i hi => by simp only [insV, updV]; grind)
    (fvarsBelow_mono (Nat.le_succ d) hw.fvarsBelow)

/-- `FvarsOk` only reads the valuation below `d`. -/
theorem FvarsOk.ext : ∀ (e : Expr) {d : Nat} {ρ ρ' : Nat → V},
    (∀ i, i < d → ρ i = ρ' i) → WScoped d e →
    FvarsOk V cval env φ d ρ e → FvarsOk V cval env φ d ρ' e
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
theorem FvarsOk.weaken_top (henv : EnvWF env) :
    ∀ (e : Expr) {d : Nat} {ρ : Nat → V} {x : V},
    WScoped d e → FvarsOk V cval env φ d ρ e →
    FvarsOk V cval env φ (d + 1) (updV V ρ d x) e
  | .fvar idx n ty, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    obtain ⟨hidx, hty, T, hT, hmem⟩ := hok
    refine ⟨by omega, FvarsOk.weaken_top henv ty (hw.2.mono (by omega)) hty, T, ?_, ?_⟩
    · rw [interp_weaken_top henv (hw.2.mono (by omega))]
      exact hT
    · simp only [updV]
      have : idx ≠ d := by omega
      simp [this, hmem]
  | .app f a, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top henv f hw.1 hok.1, FvarsOk.weaken_top henv a hw.2 hok.2⟩
  | .lam n ty body bi, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top henv ty hw.1 hok.1, FvarsOk.weaken_top henv body hw.2 hok.2⟩
  | .forallE n ty body bi, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top henv ty hw.1 hok.1, FvarsOk.weaken_top henv body hw.2 hok.2⟩
  | .letE n ty val body, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact ⟨FvarsOk.weaken_top henv ty hw.1 hok.1, FvarsOk.weaken_top henv val hw.2.1 hok.2.1,
      FvarsOk.weaken_top henv body hw.2.2 hok.2.2⟩
  | .proj s i e, d, ρ, x, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok ⊢
    exact FvarsOk.weaken_top henv e hw hok
  | .bvar _, _, _, _, _, _ => by simp [FvarsOk]
  | .sort _, _, _, _, _, _ => by simp [FvarsOk]
  | .const _ _, _, _, _, _, _ => by simp [FvarsOk]
  | .lit _, _, _, _, _, _ => by simp [FvarsOk]
termination_by e => e.sizeF
decreasing_by all_goals first
  | (simp [Expr.sizeF]; omega)
  | simp [Expr.sizeF]

/-- Opening a binder preserves the local-context assumptions. -/
theorem FvarsOk.instantiate1 (henv : EnvWF env) {d : Nat} {n : Name} {ty : Expr}
    {ρ : Nat → V} {x A : V}
    (hwty : WScoped d ty) (hty : FvarsOk V cval env φ d ρ ty)
    (hA : interpExpr V cval env φ d ρ ty = some A) (hx : x ∈ˢ A) :
    ∀ (body : Expr) (k : Nat), WScoped d body → FvarsOk V cval env φ d ρ body →
      FvarsOk V cval env φ (d + 1) (updV V ρ d x) (body.instantiate1 (.fvar d n ty) k)
  | .bvar i, k, _, _ => by
    simp only [Expr.instantiate1]
    split
    · simp only [FvarsOk]
      refine ⟨Nat.lt_succ_self d, FvarsOk.weaken_top henv ty hwty hty, A, ?_, ?_⟩
      · rw [interp_weaken_top henv hwty]; exact hA
      · simp [updV, hx]
    · split <;> simp [FvarsOk]
  | .fvar idx n' ty', k, hw, hok => by
    simp only [Expr.instantiate1]
    exact FvarsOk.weaken_top henv _ hw hok
  | .app f a, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 henv hwty hty hA hx f k hw.1 hok.1,
      FvarsOk.instantiate1 henv hwty hty hA hx a k hw.2 hok.2⟩
  | .lam n' ty' body' bi, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 henv hwty hty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 henv hwty hty hA hx body' (k + 1) hw.2 hok.2⟩
  | .forallE n' ty' body' bi, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 henv hwty hty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 henv hwty hty hA hx body' (k + 1) hw.2 hok.2⟩
  | .letE n' ty' val' body', k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact ⟨FvarsOk.instantiate1 henv hwty hty hA hx ty' k hw.1 hok.1,
      FvarsOk.instantiate1 henv hwty hty hA hx val' k hw.2.1 hok.2.1,
      FvarsOk.instantiate1 henv hwty hty hA hx body' (k + 1) hw.2.2 hok.2.2⟩
  | .proj s i e, k, hw, hok => by
    simp only [WScoped] at hw
    simp only [FvarsOk] at hok
    simp only [Expr.instantiate1, FvarsOk]
    exact FvarsOk.instantiate1 henv hwty hty hA hx e k hw hok
  | .sort _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]
  | .const _ _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]
  | .lit _, _, _, _ => by simp [Expr.instantiate1, FvarsOk]

/-- Closed expressions vacuously satisfy the local-context assumptions. -/
theorem FvarsOk.of_not_hasFvar : ∀ {e : Expr} (_ : e.hasFvar = false)
    {d : Nat} {ρ : Nat → V}, FvarsOk V cval env φ d ρ e := by
  intro e
  induction e <;> intro h d ρ <;> simp_all [Expr.hasFvar, FvarsOk]

/-- Closed terms are interpreted independently of depth and valuation. -/
theorem interp_closed_invariant (henv : EnvWF env) {e : Expr} (hcl : e.hasFvar = false) :
    ∀ (d : Nat) (ρ : Nat → V),
      interpExpr V cval env φ d ρ e = interpClosed V cval env φ e
  | 0, ρ =>
    interp_ext e (fun i hi => by omega)
      ((WScoped.of_not_hasFvar (d := 0) hcl).fvarsBelow)
  | d + 1, ρ => by
    have hw : WScoped d e := WScoped.of_not_hasFvar hcl
    have h1 : interpExpr V cval env φ (d + 1) ρ e =
        interpExpr V cval env φ (d + 1) (insV ρ d (ρ d)) e :=
      interp_ext e (fun i hi => by simp only [insV]; grind)
        (fvarsBelow_mono (Nat.le_succ d) hw.fvarsBelow)
    rw [h1, ← shiftFrom_eq_self (p := d) hw.fvarsBelow,
      interp_shift henv e (Nat.le_refl d) hw,
      shiftFrom_eq_self (p := d) hw.fvarsBelow]
    exact interp_closed_invariant henv hcl d ρ

/-- Level instantiation composes the level assignment. -/
theorem interp_instLevels (henv : EnvWF env) (hcp : ConstValParams cval env)
    {ks : List Name} {vs : List Level} :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      interpExpr V cval env φ d ρ (e.instantiateLevelParams ks vs) =
        interpExpr V cval env (Level.substFn φ ks vs) d ρ e
  | .sort u, d, ρ => by
    simp [interpExpr, instantiateLevelParams, Level.eval_subst]
  | .fvar idx n ty, d, ρ => by simp [interpExpr, instantiateLevelParams]
  | .const n ws, d, ρ => by
    simp only [interpExpr, instantiateLevelParams]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      have hlen : (ws.map (Level.subst ks vs)).length = ws.length := by simp
      by_cases hal : ws.length = ci.toConstantVal.levelParams.length
      · rw [if_pos (by simpa [hlen] using hal), if_pos hal]
        congr 1
        refine hcp n ci hf _ _ fun p hp => ?_
        exact Level.substFn_map_subst hal hp
      · rw [if_neg (by simpa [hlen] using hal), if_neg hal]
  | .forallE n ty body bi, d, ρ => by
    simp only [interpExpr, instantiateLevelParams]
    rw [← instantiateLevelParams_instantiate1]
    rw [interp_instLevels henv hcp ty d ρ]
    cases hty : interpExpr V cval env (Level.substFn φ ks vs) d ρ ty with
    | none => rfl
    | some A =>
      simp only []
      rw [sortLevelOf_instLevels henv]
      cases hv : sortLevelOf env (Level.substFn φ ks vs) (d + 1)
          (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some vE =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_instLevels henv hcp (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x)]
  | .bvar _, _, _ => by simp [interpExpr, instantiateLevelParams]
  | .app _ _, _, _ => by simp [interpExpr, instantiateLevelParams]
  | .lam _ _ _ _, _, _ => by simp [interpExpr, instantiateLevelParams]
  | .letE _ _ _ _, _, _ => by simp [interpExpr, instantiateLevelParams]
  | .lit _, _, _ => by simp [interpExpr, instantiateLevelParams]
  | .proj _ _ _, _, _ => by simp [interpExpr, instantiateLevelParams]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- The interpretation reads `φ` only at the expression's level
parameters. -/
theorem interp_params_ext (henv : EnvWF env) (hcp : ConstValParams cval env)
    {ps : List Name} {φ₁ φ₂ : Name → Nat} (hφ : ∀ p ∈ ps, φ₁ p = φ₂ p) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V), e.allLevelParamsDefined ps = true →
      interpExpr V cval env φ₁ d ρ e = interpExpr V cval env φ₂ d ρ e
  | .sort u, d, ρ, hp => by
    simp only [interpExpr, Option.some.injEq]
    rw [Level.eval_ext (by simpa [allLevelParamsDefined] using hp) hφ]
  | .fvar idx n ty, d, ρ, _ => by simp [interpExpr]
  | .const n ws, d, ρ, hp => by
    simp only [interpExpr]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      by_cases hal : ws.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hal, if_pos hal]
        congr 1
        refine hcp n ci hf _ _ fun p hpmem => ?_
        refine Level.substFn_ext hφ ?_ hal p hpmem
        intro u hu
        simp only [allLevelParamsDefined, List.all_eq_true] at hp
        exact hp u hu
      · rw [if_neg hal, if_neg hal]
  | .forallE n ty body bi, d, ρ, hp => by
    simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
    obtain ⟨⟨hpty, hpbody⟩, -⟩ := hp
    simp only [interpExpr]
    rw [interp_params_ext henv hcp hφ ty d ρ hpty]
    cases hty : interpExpr V cval env φ₂ d ρ ty with
    | none => rfl
    | some A =>
      simp only []
      have hb' : (body.instantiate1 (.fvar d n ty)).allLevelParamsDefined ps = true :=
        allLevelParamsDefined_instantiate1 hpty 0 hpbody
      have hsl : sortLevelOf env φ₁ (d + 1) (body.instantiate1 (.fvar d n ty)) =
          sortLevelOf env φ₂ (d + 1) (body.instantiate1 (.fvar d n ty)) := by
        unfold sortLevelOf
        cases hi : inferType env (d + 1) (body.instantiate1 (.fvar d n ty)) with
        | error e => rfl
        | ok t =>
          simp only [Bind.bind, Except.bind]
          cases hs : ensureSort env t with
          | error e => rfl
          | ok u =>
            simp only [Option.some.injEq]
            have ht := inferType_allLevelParams henv _ hi hb'
            have hu : (Expr.sort u).allLevelParamsDefined ps = true := by
              unfold ensureSort at hs
              cases hw : whnf env whnfFuel t with
              | error e => rw [hw] at hs; exact nomatch hs
              | ok w =>
                have h2 := whnf_allLevelParams henv whnfFuel hw ht
                rw [hw] at hs
                cases w <;>
                  simp_all [Bind.bind, Except.bind, pure, Except.pure, allLevelParamsDefined]
            exact Level.eval_ext (by simpa [allLevelParamsDefined] using hu) hφ
      rw [hsl]
      cases hv : sortLevelOf env φ₂ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some vE =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_params_ext henv hcp hφ (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x) hb']
  | .bvar _, _, _, _ => by simp [interpExpr]
  | .app _ _, _, _, _ => by simp [interpExpr]
  | .lam _ _ _ _, _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _, _ => by simp [interpExpr]
  | .lit _, _, _, _ => by simp [interpExpr]
  | .proj _ _ _, _, _, _ => by simp [interpExpr]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- The interpretation is stable under a fresh environment extension. -/
theorem interp_mono {c₀ : ConstantInfo} (henv : EnvWF env)
    (hfresh : env.find? c₀.name = none) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V), e.constsResolve env = true →
      interpExpr V cval (⟨c₀ :: env.consts⟩ : Env) φ d ρ e =
        interpExpr V cval env φ d ρ e
  | .sort u, d, ρ, _ => by simp [interpExpr]
  | .fvar idx n ty, d, ρ, _ => by simp [interpExpr]
  | .const n ws, d, ρ, hres => by
    simp only [constsResolve] at hres
    simp only [interpExpr, Env.find?_cons_of_isSome hfresh hres]
  | .forallE n ty body bi, d, ρ, hres => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [interpExpr]
    rw [interp_mono henv hfresh ty d ρ hres.1]
    cases hty : interpExpr V cval env φ d ρ ty with
    | none => rfl
    | some A =>
      simp only []
      rw [sortLevelOf_mono henv hfresh (constsResolve_instantiate1 hres.1 0 hres.2)]
      cases hv : sortLevelOf env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some vE =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_mono henv hfresh (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x) (constsResolve_instantiate1 hres.1 0 hres.2)]
  | .bvar _, _, _, _ => by simp [interpExpr]
  | .app _ _, _, _, _ => by simp [interpExpr]
  | .lam _ _ _ _, _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _, _ => by simp [interpExpr]
  | .lit _, _, _, _ => by simp [interpExpr]
  | .proj _ _ _, _, _, _ => by simp [interpExpr]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

/-- The interpretation reads the constant valuation only at names that
resolve in the environment. -/
theorem interp_cval_ext {cval₁ cval₂ : ConstVal V}
    (hagree : ∀ n, (env.find? n).isSome = true → ∀ ψ : Name → Nat, cval₁ n ψ = cval₂ n ψ) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      interpExpr V cval₁ env φ d ρ e = interpExpr V cval₂ env φ d ρ e
  | .sort u, d, ρ => by simp [interpExpr]
  | .fvar idx n ty, d, ρ => by simp [interpExpr]
  | .const n ws, d, ρ => by
    simp only [interpExpr]
    cases hf : env.find? n with
    | none => rfl
    | some ci =>
      dsimp only
      split
      · rw [hagree n (by simp [hf])]
      · rfl
  | .forallE n ty body bi, d, ρ => by
    simp only [interpExpr]
    rw [interp_cval_ext hagree ty d ρ]
    cases hty : interpExpr V cval₂ env φ d ρ ty with
    | none => rfl
    | some A =>
      simp only []
      cases hv : sortLevelOf env φ (d + 1) (body.instantiate1 (.fvar d n ty)) with
      | none => rfl
      | some vE =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_cval_ext hagree (body.instantiate1 (.fvar d n ty)) (d + 1) (updV V ρ d x)]
  | .bvar _, _, _ => by simp [interpExpr]
  | .app _ _, _, _ => by simp [interpExpr]
  | .lam _ _ _ _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _ => by simp [interpExpr]
  | .lit _, _, _ => by simp [interpExpr]
  | .proj _ _ _, _, _ => by simp [interpExpr]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

theorem interpClosed_mono {c₀ : ConstantInfo} (henv : EnvWF env)
    (hfresh : env.find? c₀.name = none) {e : Expr} (hres : e.constsResolve env = true) :
    interpClosed V cval (⟨c₀ :: env.consts⟩ : Env) φ e = interpClosed V cval env φ e :=
  interp_mono henv hfresh e 0 (rho0 V) hres

end Setlec
