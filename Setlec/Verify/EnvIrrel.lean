import Setlec.Kernel.TypeChecker

/-!
# Environment irrelevance (temporary)

In the current fragment `whnf`, `ensureSort` and `inferType` never consult
the environment, so they — and hence the interpretation — are invariant
under changing it.  Once constants and delta unfolding land (task 2),
these lemmas will be replaced by *monotonicity* under environment
extension.
-/

namespace Setlec

theorem whnf_env_irrel (env env' : Env) (e : Expr) : whnf env e = whnf env' e := by
  cases e <;> rfl

theorem ensureSort_env_irrel (env env' : Env) (t : Expr) :
    ensureSort env t = ensureSort env' t := by
  unfold ensureSort
  rw [whnf_env_irrel env env']

theorem inferType_env_irrel (env env' : Env) :
    ∀ (e : Expr) (d : Nat), inferType env d e = inferType env' d e
  | .sort u, d => by simp [inferType]
  | .fvar idx n ty, d => by simp [inferType]
  | .forallE n ty body bi, d => by
    simp only [inferType]
    rw [inferType_env_irrel env env' ty d,
      inferType_env_irrel env env' (body.instantiate1 (.fvar d n ty)) (d + 1)]
    simp only [ensureSort_env_irrel env env']
  | .bvar _, _ => by simp [inferType]
  | .const _ _, _ => by simp [inferType]
  | .app _ _, _ => by simp [inferType]
  | .lam _ _ _ _, _ => by simp [inferType]
  | .letE _ _ _ _, _ => by simp [inferType]
  | .lit _, _ => by simp [inferType]
  | .proj _ _ _, _ => by simp [inferType]
termination_by e => e.sizeB
decreasing_by
  · simp [Expr.sizeB]; omega
  · rw [Expr.sizeB_instantiate1 _ rfl]; simp [Expr.sizeB]; omega

end Setlec
