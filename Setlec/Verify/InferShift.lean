import Setlec.Kernel.TypeChecker
import Setlec.Verify.Shift
import Setlec.Verify.InstLevels
import Setlec.Verify.EnvWF
import Setlec.Verify.InferLemmas

/-!
# Shift invariance of the type checker functions

Weakening on the implementation side: shifting the free variables of a
term from position `p` (and checking at depth `d + 1` instead of `d`)
commutes with `whnf`, `ensureSort` and `inferType`.  These lemmas let the
model's weakening lemma (`Setlec.Model.InterpLemmas`) step under binders,
where the interpretation internally re-runs inference to classify the
codomain sort.

Delta unfolding produces closed terms (under `EnvWF`), on which shifting
is the identity — hence the `EnvWF` hypotheses.
-/

-- The broad simp sets in this file's mechanical case analyses trip the
-- unused-simp-args linter case by case; not worth per-case curation.
set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

theorem whnf_shift {env : Env} (henv : EnvWF env) (p : Nat) :
    ∀ (fuel : Nat) (e : Expr),
      whnf env fuel (shiftFrom p e) = shiftFrom p <$> whnf env fuel e
  | 0, e => by simp [whnf, throw, throwThe, MonadExceptOf.throw, Functor.map, Except.map]
  | fuel + 1, e => by
    match e with
    | .sort u => simp [whnf, shiftFrom, Functor.map, Except.map, pure, Except.pure]
    | .fvar idx n ty =>
      simp only [shiftFrom]
      split <;>
        simp_all [whnf, shiftFrom, Functor.map, Except.map, pure, Except.pure]
    | .forallE n ty body bi =>
      simp [whnf, shiftFrom, Functor.map, Except.map, pure, Except.pure]
    | .const n ws =>
      simp only [shiftFrom, whnf]
      cases hf : env.find? n with
      | none => simp [Functor.map, Except.map, pure, Except.pure, shiftFrom]
      | some ci =>
        cases ci with
        | defnInfo cv value =>
          dsimp only
          split
          next hal =>
            obtain ⟨-, -, -, hval⟩ := henv _ (List.mem_of_find?_eq_some hf)
            obtain ⟨hvc, -, -⟩ := hval cv value rfl
            have hcl : (value.instantiateLevelParams cv.levelParams ws).hasFvar = false := by
              rw [hasFvar_instantiateLevelParams]; exact hvc
            cases hr : whnf env fuel (value.instantiateLevelParams cv.levelParams ws) with
            | error err => simp [Functor.map, Except.map]
            | ok w =>
              have hws := whnf_WScoped (d := 0) henv fuel hr (WScoped.of_not_hasFvar hcl)
              simp [Functor.map, Except.map,
                shiftFrom_eq_self (fvarsBelow_mono (Nat.zero_le p) hws.fvarsBelow)]
          next hal => simp [Functor.map, Except.map, pure, Except.pure, shiftFrom]
        | axiomInfo cv => simp [Functor.map, Except.map, pure, Except.pure, shiftFrom]
        | thmInfo cv value => simp [Functor.map, Except.map, pure, Except.pure, shiftFrom]
    | .bvar i => simp [whnf, shiftFrom, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .app f a => simp [whnf, shiftFrom, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .lam n ty body bi => simp [whnf, shiftFrom, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .letE n ty val body => simp [whnf, shiftFrom, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .lit l => simp [whnf, shiftFrom, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    | .proj s i e' => simp [whnf, shiftFrom, Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]

theorem ensureSort_shift {env : Env} (henv : EnvWF env) (p : Nat) (t : Expr) :
    ensureSort env (shiftFrom p t) = ensureSort env t := by
  unfold ensureSort
  rw [whnf_shift henv]
  cases h : whnf env whnfFuel t with
  | error e => rfl
  | ok w =>
    simp only [Functor.map, Except.map, Bind.bind, Except.bind]
    cases w with
    | fvar idx n ty =>
      simp only [shiftFrom]
      by_cases hip : p ≤ idx <;> simp [hip]
    | _ => rfl

theorem inferType_shift {env : Env} (henv : EnvWF env) :
    ∀ (e : Expr) {d p : Nat}, p ≤ d → WScoped d e →
      inferType env (d + 1) (shiftFrom p e) = shiftFrom p <$> inferType env d e
  | .sort u, _, _, _, _ => by
    simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure]
  | .fvar idx n' ty, d, p, hpd, hw => by
    simp only [WScoped] at hw
    simp only [shiftFrom]
    split
    · simp [inferType, Functor.map, Except.map, pure, Except.pure]
    · have : shiftFrom p ty = ty :=
        shiftFrom_eq_self (fvarsBelow_mono (by omega) hw.2.fvarsBelow)
      simp [inferType, Functor.map, Except.map, pure, Except.pure, this]
  | .const n' ws, d, p, hpd, hw => by
    simp only [shiftFrom, inferType]
    cases hf : env.find? n' with
    | none => simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    | some ci =>
      dsimp only
      split
      next hal =>
        obtain ⟨htc, -, -, -⟩ := henv _ (List.mem_of_find?_eq_some hf)
        have hcl : (ci.toConstantVal.type.instantiateLevelParams
            ci.toConstantVal.levelParams ws).hasFvar = false := by
          rw [hasFvar_instantiateLevelParams]; exact htc
        simp [Functor.map, Except.map, pure, Except.pure,
          shiftFrom_eq_self (fvarsBelow_mono (Nat.zero_le p)
            (WScoped.of_not_hasFvar (d := 0) hcl).fvarsBelow)]
      next hal => simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
  | .forallE n' ty body bi, d, p, hpd, hw => by
    simp only [WScoped] at hw
    simp only [shiftFrom, inferType]
    cases hc : bi.cod with
    | none => simp [Functor.map, Except.map, throw, throwThe, MonadExceptOf.throw]
    | some v =>
      dsimp only
      rw [inferType_shift henv ty hpd hw.1]
      cases hty : inferType env d ty with
      | error e => simp [Functor.map, Except.map, Bind.bind, Except.bind]
      | ok tty =>
        simp only [Functor.map, Except.map, Bind.bind, Except.bind, ensureSort_shift henv]
        cases hsty : ensureSort env tty <;>
          simp [Functor.map, Except.map, pure, Except.pure, shiftFrom]
  | .bvar i, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .app f a, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .lam n' ty body bi, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .letE n' ty val body, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .lit l, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .proj s i e', _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
termination_by e => e.sizeB
decreasing_by
  all_goals first
  | (simp [Expr.sizeB]; omega)
  | (rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega)

end Setlec
