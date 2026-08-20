import Setlec.Model.Interp
import Setlec.Verify.InstLevels
import Setlec.Verify.Subst

/-!
# Weakening and stability lemmas for the interpretation

With the codomain-sort annotations the interpretation is purely
structural, so this family no longer depends on the checker's reduction
or inference:

* `interp_ext`, `interp_shift`, `interp_weaken_top` — stepping under a
  binder;
* `interp_closed_invariant` — closed terms are interpreted independently
  of depth and valuation;
* `interp_instLevels` — level instantiation composes the level assignment;
* `interp_params_ext` — only the expression's level parameters are read;
* `interp_mono` — stability under a fresh environment extension;
* `interp_cval_ext` — only resolvable constants' values are read.
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
  | .forallE n ty body m, d, ρ, ρ', h, hb => by
    simp only [fvarsBelow] at hb
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_ext ty h hb.1]
      cases hty : interpExpr V cval env φ d ρ' ty with
      | none => rfl
      | some A =>
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
  | .lam n ty body m, d, ρ, ρ', h, hb => by
    simp only [fvarsBelow] at hb
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_ext ty h hb.1]
      cases hty : interpExpr V cval env φ d ρ' ty with
      | none => rfl
      | some A =>
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
  | .app f a, d, ρ, ρ', h, hb => by
    simp only [fvarsBelow] at hb
    simp only [interpExpr]
    rw [interp_ext f h hb.1, interp_ext a h hb.2]
  | .bvar _, _, _, _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _, _, _, _ => by simp [interpExpr]
  | .lit l, _, _, _, _, _ => by cases l <;> simp [interpExpr]
  | .proj s' i e, d, ρ, ρ', h, hb => by
    simp only [fvarsBelow] at hb
    simp only [interpExpr]
    rw [interp_ext e h hb]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Semantic weakening: inserting a value at `p ≤ d` and shifting the term
leaves the interpretation unchanged. -/
theorem interp_shift : ∀ (e : Expr) {d p : Nat} {ρ : Nat → V} {x : V},
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
  | .forallE n ty body m, d, p, ρ, x, hpd, hw => by
    have hw' : WScoped d ty ∧ WScoped d body := by simpa [WScoped] using hw
    simp only [shiftFrom, interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [← shiftFrom_instantiate1 hpd]
      rw [interp_shift ty hpd hw'.1]
      cases hty : interpExpr V cval env φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x'
        rw [← insV_updV hpd,
          interp_shift (body.instantiate1 (.fvar d n ty))
            (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
  | .lam n ty body m, d, p, ρ, x, hpd, hw => by
    have hw' : WScoped d ty ∧ WScoped d body := by simpa [WScoped] using hw
    simp only [shiftFrom, interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [← shiftFrom_instantiate1 hpd]
      rw [interp_shift ty hpd hw'.1]
      cases hty : interpExpr V cval env φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x'
        rw [← insV_updV hpd,
          interp_shift (body.instantiate1 (.fvar d n ty))
            (Nat.le_succ_of_le hpd) (hw'.1.instantiate1 0 hw'.2)]
  | .app f a, d, p, ρ, x, hpd, hw => by
    have hw' : WScoped d f ∧ WScoped d a := by simpa [WScoped] using hw
    simp only [shiftFrom, interpExpr]
    rw [interp_shift f hpd hw'.1, interp_shift a hpd hw'.2]
  | .bvar _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .letE _ _ _ _, _, _, _, _, _, _ => by simp [interpExpr, shiftFrom]
  | .lit l, _, _, _, _, _, _ => by cases l <;> simp [interpExpr, shiftFrom]
  | .proj s' i e, d, p, ρ, x, hpd, hw => by
    have hw' : WScoped d e := by simpa [WScoped] using hw
    simp only [shiftFrom, interpExpr]
    rw [interp_shift e hpd hw']
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- Weakening at the top: valuing a fresh top variable does not change the
interpretation of a term scoped below it. -/
theorem interp_weaken_top {e : Expr} {d : Nat} {ρ : Nat → V} {x : V}
    (hw : WScoped d e) :
    interpExpr V cval env φ (d + 1) (updV V ρ d x) e = interpExpr V cval env φ d ρ e := by
  have h := interp_shift (env := env) (cval := cval) (φ := φ) e (ρ := ρ) (x := x) (Nat.le_refl d) hw
  rw [shiftFrom_eq_self hw.fvarsBelow] at h
  rw [← h]
  exact interp_ext e
    (fun i hi => by simp only [insV, updV]; grind)
    (fvarsBelow_mono (Nat.le_succ d) hw.fvarsBelow)

/-- Closed terms are interpreted independently of depth and valuation. -/
theorem interp_closed_invariant {e : Expr} (hcl : e.hasFvar = false) :
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
      interp_shift e (Nat.le_refl d) hw,
      shiftFrom_eq_self (p := d) hw.fvarsBelow]
    exact interp_closed_invariant hcl d ρ

/-- Level instantiation composes the level assignment. -/
theorem interp_instLevels (hcp : ConstValParams cval env)
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
  | .forallE n ty body m, d, ρ => by
    simp only [interpExpr, instantiateLevelParams]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      rw [← instantiateLevelParams_instantiate1]
      rw [interp_instLevels hcp ty d ρ]
      cases hty : interpExpr V cval env (Level.substFn φ ks vs) d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        rw [Level.eval_subst]
        congr 1
        funext x
        rw [interp_instLevels hcp (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x)]
  | .lam n ty body m, d, ρ => by
    simp only [interpExpr, instantiateLevelParams]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only [Option.map_some]
      rw [← instantiateLevelParams_instantiate1]
      rw [interp_instLevels hcp ty d ρ]
      cases hty : interpExpr V cval env (Level.substFn φ ks vs) d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        rw [Level.eval_subst]
        congr 1
        funext x
        rw [interp_instLevels hcp (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x)]
  | .app f a, d, ρ => by
    simp only [interpExpr, instantiateLevelParams]
    rw [interp_instLevels hcp f d ρ, interp_instLevels hcp a d ρ]
  | .bvar _, _, _ => by simp [interpExpr, instantiateLevelParams]
  | .letE _ _ _ _, _, _ => by simp [interpExpr, instantiateLevelParams]
  | .lit l, d, ρ => by
    cases l with
    | strVal s => simp [interpExpr, instantiateLevelParams]
    | natVal n =>
      simp only [instantiateLevelParams]
      by_cases hs : natLitSupported env
      · obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3,
          -⟩ := natLitSupported_inv hs
        simp only [interpExpr, hs, if_true, Level.substFn_nil]
        rw [hcp natZeroName _ hz _ _
            (by simp [ConstantInfo.toConstantVal, h2]),
          hcp natSuccName _ hsc _ _
            (by simp [ConstantInfo.toConstantVal, h3])]
      · simp [interpExpr, hs]
  | .proj s' i e, d, ρ => by
    simp only [interpExpr, instantiateLevelParams]
    rw [interp_instLevels hcp e d ρ]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- The condition under which renaming constants is invisible to the
interpretation: every renamed constant resolves with the same level
parameters, unresolved names stay unresolved, and the valuation agrees
on the renaming. -/
def RenameOk (cval : ConstVal V) (env : Env) (f : Name → Name) : Prop :=
  (∀ n ci, env.find? n = some ci → ∃ ci', env.find? (f n) = some ci' ∧
    ci'.toConstantVal.levelParams = ci.toConstantVal.levelParams) ∧
  (∀ n, env.find? n = none → env.find? (f n) = none) ∧
  (∀ (n : Name) (ψ' : Name → Nat), cval (f n) ψ' = cval n ψ')

/-- Renaming constants along a `RenameOk` map preserves the
interpretation. -/
theorem interp_renameConsts {f : Name → Name}
    (hro : RenameOk cval env f) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      interpExpr V cval env φ d ρ (e.renameConsts f) =
        interpExpr V cval env φ d ρ e
  | .sort u, d, ρ => by simp [interpExpr, Expr.renameConsts]
  | .fvar idx n ty, d, ρ => by simp [interpExpr, Expr.renameConsts]
  | .const n ws, d, ρ => by
    simp only [interpExpr, Expr.renameConsts]
    cases hf : env.find? n with
    | none =>
      rw [hro.2.1 n hf]
    | some ci =>
      obtain ⟨ci', hf', hlp⟩ := hro.1 n ci hf
      rw [hf']
      dsimp only
      rw [hlp]
      by_cases hal : ws.length = ci.toConstantVal.levelParams.length
      · rw [if_pos hal, if_pos hal, hro.2.2]
      · rw [if_neg hal, if_neg hal]
  | .forallE n ty body m, d, ρ => by
    simp only [interpExpr, Expr.renameConsts]
    cases m.cod with
    | none => rfl
    | some v =>
      rw [← renameConsts_instantiate1]
      rw [interp_renameConsts hro ty d ρ]
      cases hty : interpExpr V cval env φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_renameConsts hro (body.instantiate1 (.fvar d n ty))
          (d + 1) (updV V ρ d x)]
  | .lam n ty body m, d, ρ => by
    simp only [interpExpr, Expr.renameConsts]
    cases m.cod with
    | none => rfl
    | some v =>
      rw [← renameConsts_instantiate1]
      rw [interp_renameConsts hro ty d ρ]
      cases hty : interpExpr V cval env φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_renameConsts hro (body.instantiate1 (.fvar d n ty))
          (d + 1) (updV V ρ d x)]
  | .app g a, d, ρ => by
    simp only [interpExpr, Expr.renameConsts]
    rw [interp_renameConsts hro g d ρ, interp_renameConsts hro a d ρ]
  | .bvar _, _, _ => by simp [interpExpr, Expr.renameConsts]
  | .letE _ _ _ _, _, _ => by simp [interpExpr, Expr.renameConsts]
  | .lit _, _, _ => by simp [interpExpr, Expr.renameConsts]
  | .proj s' i e, d, ρ => by
    simp only [interpExpr, Expr.renameConsts]
    rw [interp_renameConsts hro e d ρ]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- The interpretation reads `φ` only at the expression's level
parameters. -/
theorem interp_params_ext (hcp : ConstValParams cval env)
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
  | .forallE n ty body m, d, ρ, hp => by
    simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
    obtain ⟨⟨hpty, hpbody⟩, hpcod⟩ := hp
    simp only [interpExpr]
    cases hc : m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_params_ext hcp hφ ty d ρ hpty]
      cases hty : interpExpr V cval env φ₂ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        rw [Level.eval_ext (by simpa [hc] using hpcod) hφ]
        congr 1
        funext x
        rw [interp_params_ext hcp hφ (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x) (allLevelParamsDefined_instantiate1 hpty 0 hpbody)]
  | .lam n ty body m, d, ρ, hp => by
    simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
    obtain ⟨⟨hpty, hpbody⟩, hpcod⟩ := hp
    simp only [interpExpr]
    cases hc : m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_params_ext hcp hφ ty d ρ hpty]
      cases hty : interpExpr V cval env φ₂ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        rw [Level.eval_ext (by simpa [hc] using hpcod) hφ]
        congr 1
        funext x
        rw [interp_params_ext hcp hφ (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x) (allLevelParamsDefined_instantiate1 hpty 0 hpbody)]
  | .app f a, d, ρ, hp => by
    simp only [allLevelParamsDefined, Bool.and_eq_true] at hp
    simp only [interpExpr]
    rw [interp_params_ext hcp hφ f d ρ hp.1, interp_params_ext hcp hφ a d ρ hp.2]
  | .bvar _, _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _, _ => by simp [interpExpr]
  | .lit l, d, ρ, _ => by
    cases l with
    | strVal s => simp [interpExpr]
    | natVal n =>
      by_cases hs : natLitSupported env
      · obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, h1, h2, h3,
          -⟩ := natLitSupported_inv hs
        simp only [interpExpr, hs, if_true, Level.substFn_nil]
        rw [hcp natZeroName _ hz _ _
            (by simp [ConstantInfo.toConstantVal, h2]),
          hcp natSuccName _ hsc _ _
            (by simp [ConstantInfo.toConstantVal, h3])]
      · simp [interpExpr, hs]
  | .proj s' i e, d, ρ, hp => by
    simp only [allLevelParamsDefined] at hp
    simp only [interpExpr]
    rw [interp_params_ext hcp hφ e d ρ hp]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- The interpretation is stable under a fresh environment extension. -/
theorem interp_mono {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V), e.constsResolve env = true →
      interpExpr V cval (⟨c₀ :: env.consts⟩ : Env) φ d ρ e =
        interpExpr V cval env φ d ρ e
  | .sort u, d, ρ, _ => by simp [interpExpr]
  | .fvar idx n ty, d, ρ, _ => by simp [interpExpr]
  | .const n ws, d, ρ, hres => by
    simp only [constsResolve] at hres
    simp only [interpExpr, Env.find?_cons_of_isSome hfresh hres]
  | .forallE n ty body m, d, ρ, hres => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_mono hfresh ty d ρ hres.1]
      cases hty : interpExpr V cval env φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_mono hfresh (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x) (constsResolve_instantiate1 hres.1 0 hres.2)]
  | .lam n ty body m, d, ρ, hres => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_mono hfresh ty d ρ hres.1]
      cases hty : interpExpr V cval env φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_mono hfresh (body.instantiate1 (.fvar d n ty)) (d + 1)
          (updV V ρ d x) (constsResolve_instantiate1 hres.1 0 hres.2)]
  | .app f a, d, ρ, hres => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [interpExpr]
    rw [interp_mono hfresh f d ρ hres.1, interp_mono hfresh a d ρ hres.2]
  | .bvar _, _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _, _ => by simp [interpExpr]
  | .lit l, d, ρ, hres => by
    cases l with
    | strVal s => simp [interpExpr]
    | natVal n =>
      simp only [constsResolve, Bool.and_eq_true] at hres
      have hg : natLitSupported (⟨c₀ :: env.consts⟩ : Env) =
          natLitSupported env :=
        natLitSupported_congr
          (Env.find?_cons_of_isSome hfresh hres.1.1)
          (Env.find?_cons_of_isSome hfresh hres.1.2)
          (Env.find?_cons_of_isSome hfresh hres.2)
      simp only [interpExpr, hg]
  | .proj s' i e, d, ρ, hres => by
    simp only [constsResolve, Bool.and_eq_true] at hres
    simp only [interpExpr]
    rw [interp_mono hfresh e d ρ hres.2]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

theorem interpClosed_mono {c₀ : ConstantInfo} (hfresh : env.find? c₀.name = none)
    {e : Expr} (hres : e.constsResolve env = true) :
    interpClosed V cval (⟨c₀ :: env.consts⟩ : Env) φ e = interpClosed V cval env φ e :=
  interp_mono hfresh e 0 (rho0 V) hres

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
  | .forallE n ty body m, d, ρ => by
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_cval_ext hagree ty d ρ]
      cases hty : interpExpr V cval₂ env φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_cval_ext hagree (body.instantiate1 (.fvar d n ty)) (d + 1) (updV V ρ d x)]
  | .lam n ty body m, d, ρ => by
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_cval_ext hagree ty d ρ]
      cases hty : interpExpr V cval₂ env φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_cval_ext hagree (body.instantiate1 (.fvar d n ty)) (d + 1) (updV V ρ d x)]
  | .app f a, d, ρ => by
    simp only [interpExpr]
    rw [interp_cval_ext hagree f d ρ, interp_cval_ext hagree a d ρ]
  | .bvar _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _ => by simp [interpExpr]
  | .lit l, d, ρ => by
    cases l with
    | strVal s => simp [interpExpr]
    | natVal n =>
      by_cases hs : natLitSupported env
      · obtain ⟨cv, caps, cv0, i0, j0, cv1, i1, j1, hn, hz, hsc, -⟩ :=
          natLitSupported_inv hs
        simp only [interpExpr, hs, if_true]
        rw [hagree natZeroName (by simp [hz]) _,
          hagree natSuccName (by simp [hsc]) _]
      · simp [interpExpr, hs]
  | .proj s' i e, d, ρ => by
    simp only [interpExpr]
    rw [interp_cval_ext hagree e d ρ]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- The interpretation reads stored constants only through their level
parameters: environments that agree there (e.g. differing only in a
recursor's rule list) interpret every expression alike. -/
theorem interp_env_ext {env₁ env₂ : Env}
    (henv : ∀ n, (env₁.find? n).map (fun ci => ci.toConstantVal.levelParams) =
        (env₂.find? n).map (fun ci => ci.toConstantVal.levelParams))
    (hnat : natLitSupported env₁ = natLitSupported env₂) :
    ∀ (e : Expr) (d : Nat) (ρ : Nat → V),
      interpExpr V cval env₁ φ d ρ e = interpExpr V cval env₂ φ d ρ e
  | .sort u, d, ρ => by simp [interpExpr]
  | .fvar idx n ty, d, ρ => by simp [interpExpr]
  | .const n ws, d, ρ => by
    simp only [interpExpr]
    have h := henv n
    cases hf : env₁.find? n with
    | none =>
      rw [hf] at h
      cases hf2 : env₂.find? n with
      | none => rfl
      | some ci₂ => rw [hf2] at h; exact nomatch h
    | some ci =>
      rw [hf] at h
      cases hf2 : env₂.find? n with
      | none => rw [hf2] at h; exact nomatch h
      | some ci₂ =>
        rw [hf2] at h
        simp only [Option.map_some, Option.some.injEq] at h
        dsimp only
        rw [h]
  | .forallE n ty body m, d, ρ => by
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_env_ext henv hnat ty d ρ]
      cases hty : interpExpr V cval env₂ φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_env_ext henv hnat (body.instantiate1 (.fvar d n ty)) (d + 1) (updV V ρ d x)]
  | .lam n ty body m, d, ρ => by
    simp only [interpExpr]
    cases m.cod with
    | none => rfl
    | some v =>
      simp only []
      rw [interp_env_ext henv hnat ty d ρ]
      cases hty : interpExpr V cval env₂ φ d ρ ty with
      | none => rfl
      | some A =>
        simp only [Option.some.injEq]
        congr 1
        funext x
        rw [interp_env_ext henv hnat (body.instantiate1 (.fvar d n ty)) (d + 1) (updV V ρ d x)]
  | .app f a, d, ρ => by
    simp only [interpExpr]
    rw [interp_env_ext henv hnat f d ρ, interp_env_ext henv hnat a d ρ]
  | .bvar _, _, _ => by simp [interpExpr]
  | .letE _ _ _ _, _, _ => by simp [interpExpr]
  | .lit l, _, _ => by cases l <;> simp [interpExpr, hnat]
  | .proj s' i e, d, ρ => by
    simp only [interpExpr]
    rw [interp_env_ext henv hnat e d ρ]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

/-- The interpretation only reads what `ErasedEq` preserves. -/
theorem interp_erasedEq : ∀ {e₁ e₂ : Expr}, Expr.ErasedEq e₁ e₂ →
    ∀ (d : Nat) (ρ : Nat → V),
      interpExpr V cval env φ d ρ e₁ = interpExpr V cval env φ d ρ e₂
  | .bvar i, e₂, he, d, ρ => by
    match e₂, he with
    | .bvar j, he => obtain rfl : i = j := he; rfl
  | .fvar i n ty, e₂, he, d, ρ => by
    match e₂, he with
    | .fvar j n' ty', he =>
      obtain rfl : i = j := he
      simp [interpExpr]
  | .sort u, e₂, he, d, ρ => by
    match e₂, he with
    | .sort u', he => obtain rfl : u = u' := he; rfl
  | .const n us, e₂, he, d, ρ => by
    match e₂, he with
    | .const n' us', he =>
      obtain ⟨rfl, rfl⟩ : n = n' ∧ us = us' := he
      rfl
  | .app f a, e₂, he, d, ρ => by
    match e₂, he with
    | .app g b, he =>
      obtain ⟨h1, h2⟩ : Expr.ErasedEq f g ∧ Expr.ErasedEq a b := he
      simp only [interpExpr, interp_erasedEq h1 d ρ, interp_erasedEq h2 d ρ]
  | .forallE n ty body m, e₂, he, d, ρ => by
    match e₂, he with
    | .forallE n' ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ :
          m = m' ∧ Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [interpExpr]
      cases m.cod with
      | none => rfl
      | some v =>
        simp only []
        rw [interp_erasedEq h1 d ρ]
        cases hty : interpExpr V cval env φ d ρ ty' with
        | none => rfl
        | some A =>
          simp only [Option.some.injEq]
          congr 1
          funext x
          rw [interp_erasedEq
            (Expr.ErasedEq.instantiate1 h2 (show Expr.ErasedEq
              (.fvar d n ty) (.fvar d n' ty') from rfl))
            (d + 1) (updV V ρ d x)]
  | .lam n ty body m, e₂, he, d, ρ => by
    match e₂, he with
    | .lam n' ty' body' m', he =>
      obtain ⟨rfl, h1, h2⟩ :
          m = m' ∧ Expr.ErasedEq ty ty' ∧ Expr.ErasedEq body body' := he
      simp only [interpExpr]
      cases m.cod with
      | none => rfl
      | some v =>
        simp only []
        rw [interp_erasedEq h1 d ρ]
        cases hty : interpExpr V cval env φ d ρ ty' with
        | none => rfl
        | some A =>
          simp only [Option.some.injEq]
          congr 1
          funext x
          rw [interp_erasedEq
            (Expr.ErasedEq.instantiate1 h2 (show Expr.ErasedEq
              (.fvar d n ty) (.fvar d n' ty') from rfl))
            (d + 1) (updV V ρ d x)]
  | .letE n ty vl body, e₂, he, d, ρ => by
    match e₂, he with
    | .letE n' ty' vl' body', he => simp [interpExpr]
  | .lit l, e₂, he, d, ρ => by
    match e₂, he with
    | .lit l', he => obtain rfl : l = l' := he; rfl
  | .proj sn i pe, e₂, he, d, ρ => by
    match e₂, he with
    | .proj sn' i' pe', he =>
      obtain ⟨rfl, rfl, h⟩ :
          sn = sn' ∧ i = i' ∧ Expr.ErasedEq pe pe' := he
      simp only [interpExpr, interp_erasedEq h d ρ]
termination_by e₁ => e₁.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)
  | (simp [Expr.sizeB])

end Setlec
