import Setlec.SetR.Annot.EnvS2

/-!
# `EnvS2U` — the environment invariant in uniqueness form (structure)

**Split from `Interp2/EnvS2U.lean` at seal 44, and the split is the
point.** The structure needs only `Annot/EnvS2`'s cone; the file it
came from imports `Step2/Whnf`, which put `EnvS2U` **strictly
downstream of the four quarters** that must be re-pointed into it —
`EnvS2U` → `Step2/Whnf` → `Dual2E` → `Claims2E`, an import Lean
rejects outright.

Only `EnvS2.toU` (which needs `denote2_fuelMono`) and the
`acval_defn_uniq_lam_ok` probe wanted that cone. They stay downstream;
the structure comes here, where the claims can see it.

*Seal 43's rule earned this file: before authorizing a re-point as "a
statement change", count the occurrences and check the import
direction.*
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name ConstantInfo ConstantVal
  ReducibilityHint)

universe w

variable (V : Type w) [SetTheory V]

/-- **The environment invariant, uniqueness form.**  Identical to
`EnvS2` except that the two `denote2` fields assert *identification*
rather than *existence*. -/
structure EnvS2U (env : Env) where
  /-- the collapse-lane invariant, contained -/
  base : EnvS V env
  /-- the canonical annotated valuation -/
  acval : Name → (Name → Nat) → AVExpr
  /-- it erases to the collapse-lane valuation -/
  acval_erase : ∀ (n : Name) (ψ : Name → Nat),
    (acval n ψ).erase = base.cval n ψ
  /-- every leaf is closed, as a lifting equation -/
  acval_closed : ∀ (n : Name) (ψ : Name → Nat) (k : Nat),
    (acval n ψ).liftN 1 k = acval n ψ
  /-- a leaf reads only its own level parameters -/
  acval_params : ∀ (n : Name) (ci : ConstantInfo),
    env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      acval n ψ₁ = acval n ψ₂
  /-- every leaf is truthful -/
  acval_ok2 : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOk2 V ρ (acval n ψ)
  /-- **uniqueness, not existence**: *if* a definition's value
  annotates, that annotation is the constant's own leaf -/
  acval_defn : ∀ (μ : CheckMode) (φ : Name → Nat) (F : Nat)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ {ra : AVExpr},
      denote2 μ acval env φ F 0 value = some ra →
      ra = acval cv.name φ
  /-- ditto for a theorem's proof value -/
  acval_thm : ∀ (μ : CheckMode) (φ : Name → Nat) (F : Nat)
    (cv : ConstantVal) (value : Expr),
    ConstantInfo.thmInfo cv value ∈ env.consts →
    ∀ {ra : AVExpr},
      denote2 μ acval env φ F 0 value = some ra →
      ra = acval cv.name φ
  /-- stored constants inhabit their annotated types -/
  mem_type2 : ∀ (μ : CheckMode) (φ : Name → Nat) (fuel : Nat),
    ∀ c ∈ env.consts, ∀ ta : AVExpr,
    denote2 μ acval env φ fuel 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, interp2 V ρ (acval c.name φ) ∈ˢ interp2 V ρ ta

end Setlec.SetR.Interp2
