import Setlec.Kernel.TypeChecker
import Setlec.Model.Interp

/-!
# Soundness of the type checker functions

Soundness of `whnf`, `inferType` and `isDefEq` with respect to the set-model
interpretation `interpExpr`:

* `whnf_sound`: reduction preserves the interpretation.
* `inferType_sound`: if `inferType` succeeds then expression and inferred
  type are interpreted, and `⟦e⟧ ∈ ⟦t⟧`.
* `isDefEq_sound`: a positive `isDefEq` verdict means the interpretations
  agree (whenever both are defined).

Only success cases carry obligations; `throw`n errors reject or decline.
-/

namespace Setlec

variable {V : Type u} [SetTheory V]

open SetTheory

theorem whnf_sound {env : Env} {e e' : Expr} (h : whnf env e = .ok e') (φ : Name → Nat) :
    interpExpr V φ e' = interpExpr V φ e := by
  cases e <;> simp_all [whnf, pure, Except.pure]

theorem inferType_sound {env : Env} {e t : Expr} (h : inferType env e = .ok t) (φ : Name → Nat) :
    ∃ v tv, interpExpr V φ e = some v ∧ interpExpr V φ t = some tv ∧ v ∈ˢ tv := by
  cases e <;> simp only [inferType, pure, Except.pure] at h <;> first
  | contradiction
  | · obtain rfl := Except.ok.inj h
      exact ⟨univ (Level.eval φ _), univ (Level.eval φ _ + 1), rfl, rfl, univ_mem_univ _⟩

theorem isDefEq_sound {env : Env} {a b : Expr} (h : isDefEq env a b = .ok true)
    (φ : Name → Nat) {va vb : V}
    (ha : interpExpr V φ a = some va) (hb : interpExpr V φ b = some vb) : va = vb := by
  cases a <;> cases b <;> simp_all [isDefEq, whnf, interpExpr, bind, Except.bind, pure, Except.pure]
  case sort.sort u v =>
    obtain ⟨-, rfl⟩ := ha
    obtain ⟨-, rfl⟩ := hb
    have : Level.isEquiv u v = some true := by
      revert h
      cases hEq : Level.isEquiv u v with
      | none => simp [liftFueled]
      | some b => cases b <;> simp [liftFueled, pure, Except.pure]
    rw [Level.isEquiv_sound this φ]

end Setlec
