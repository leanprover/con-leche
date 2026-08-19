import Setlec.Kernel.TypeChecker
import Setlec.Verify.Shift

/-!
# Shift invariance of the type checker functions

Weakening on the implementation side: shifting the free variables of a
term from position `p` (and checking at depth `d + 1` instead of `d`)
commutes with `whnf`, `ensureSort` and `inferType`.  These lemmas let the
model's weakening lemma (`Setlec.Model.InterpLemmas`) step under binders,
where the interpretation internally re-runs inference to classify the
codomain sort.
-/

-- The broad simp sets in this file's mechanical case analyses trip the
-- unused-simp-args linter case by case; not worth per-case curation.
set_option linter.unusedSimpArgs false

namespace Setlec

open Expr

theorem whnf_shift (env : Env) (p : Nat) (e : Expr) :
    whnf env (shiftFrom p e) = shiftFrom p <$> whnf env e := by
  cases e <;>
    first
    | (simp only [shiftFrom]
       split <;>
         simp_all [whnf, shiftFrom, Functor.map, Except.map, pure, Except.pure])
    | simp [whnf, shiftFrom, Functor.map, Except.map, throw, throwThe,
        MonadExceptOf.throw, pure, Except.pure]

theorem ensureSort_shift (env : Env) (p : Nat) (t : Expr) :
    ensureSort env (shiftFrom p t) = ensureSort env t := by
  unfold ensureSort
  rw [whnf_shift]
  cases h : whnf env t with
  | error e => rfl
  | ok w =>
    simp only [Functor.map, Except.map, Bind.bind, Except.bind]
    cases w with
    | fvar idx n ty =>
      simp only [shiftFrom]
      by_cases hip : p ≤ idx <;> simp [hip]
    | _ => rfl

theorem inferType_shift (env : Env) :
    ∀ (e : Expr) {d p : Nat}, p ≤ d → WScoped d e →
      inferType env (d + 1) (shiftFrom p e) = shiftFrom p <$> inferType env d e
  | .sort u, _, _, _, _ => by
    simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .fvar idx n' ty, d, p, hpd, hw => by
    simp only [WScoped] at hw
    simp only [shiftFrom]
    split
    · simp [inferType, Functor.map, Except.map, pure, Except.pure]
    · have : shiftFrom p ty = ty :=
        shiftFrom_eq_self (fvarsBelow_mono (by omega) hw.2.fvarsBelow)
      simp [inferType, Functor.map, Except.map, pure, Except.pure, this]
  | .forallE n' ty body bi, d, p, hpd, hw => by
    simp only [WScoped] at hw
    simp only [shiftFrom, inferType]
    rw [← shiftFrom_instantiate1 hpd]
    rw [inferType_shift env ty hpd hw.1,
        inferType_shift env (body.instantiate1 (.fvar d n' ty))
          (Nat.le_succ_of_le hpd) (hw.1.instantiate1 0 hw.2)]
    cases hty : inferType env d ty with
    | error e => simp [Functor.map, Except.map, Bind.bind, Except.bind]
    | ok tty =>
      simp only [Functor.map, Except.map, Bind.bind, Except.bind, ensureSort_shift]
      cases hsty : ensureSort env tty with
      | error e => simp
      | ok u =>
        simp only []
        cases hb : inferType env (d + 1) (body.instantiate1 (.fvar d n' ty)) with
        | error e => simp
        | ok tb =>
          simp only [ensureSort_shift]
          cases hsb : ensureSort env tb <;>
            simp [Functor.map, Except.map, pure, Except.pure, shiftFrom]
  | .bvar i, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .const n' us, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .app f a, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .lam n' ty body bi, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .letE n' ty val body, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .lit l, _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
  | .proj s i e', _, _, _, _ => by simp [inferType, shiftFrom, Functor.map, Except.map, pure, Except.pure, throw, throwThe, MonadExceptOf.throw]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

end Setlec
