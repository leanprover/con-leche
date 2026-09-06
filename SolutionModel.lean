import Setlec.Verify.Cached.MainC

/-!
# Comparator solution: the model

`ChallengeModel.lean`'s theorems, proved from `model_exists_SPCD_P`
(`cfgOf .verified = cfgP` by `rfl`) and `SetP.Sem_functional`.  Must not
import `ChallengeModel`.
-/

namespace Setlec

open SetTheory

theorem model_exists (V : Type w) [SetTheory V]
    (h : Cached.checkDeclsSPCachedD cfgP ds = .ok env') :
    ∃ cval : Name → (Name → Nat) → V,
      (∀ (cv : ConstantVal) (value : Expr),
        ((∃ hint, ConstantInfo.defnInfo cv value hint ∈ env'.consts) ∨
          ConstantInfo.thmInfo cv value ∈ env'.consts) →
        ∀ (φ : Name → Nat) (ρ : Nat → V),
          Semantics.Sem cval env' φ 0 ρ value (cval cv.name φ)) ∧
      (∀ c ∈ env'.consts, ∀ (φ : Name → Nat) (ρ : Nat → V),
        ∃ T, Semantics.Sem cval env' φ 0 ρ c.toConstantVal.type T ∧ cval c.name φ ∈ˢ T) :=
  Cached.model_exists_SPCD_P V (μ := .verified) rfl h

theorem Sem_functional (V : Type w) [SetTheory V]
    (cval : Name → (Name → Nat) → V) (env : Env) (φ : Name → Nat)
    (d : Nat) (ρ : Nat → V) (e : Expr) {v w : V}
    (hv : Semantics.Sem cval env φ d ρ e v) (hw : Semantics.Sem cval env φ d ρ e w) :
    v = w :=
  SetP.Sem_functional hv hw
