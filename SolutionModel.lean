import Setlec.Verify.Cached.MainC

/-!
# Comparator solution: the model

`ChallengeModel.lean`'s theorem, proved from `model_exists_SPCD_P`
(`cfgOf .verified = cfgP` by `rfl`).  Must not import `ChallengeModel`.
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
          Semantics.sem cval env' φ 0 ρ value = cval cv.name φ) ∧
      (∀ c ∈ env'.consts, ∀ (φ : Name → Nat) (ρ : Nat → V),
        cval c.name φ ∈ˢ Semantics.sem cval env' φ 0 ρ c.toConstantVal.type) :=
  Cached.model_exists_SPCD_P V (μ := .verified) rfl h
