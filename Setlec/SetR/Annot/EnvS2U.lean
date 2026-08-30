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

/-! ## The mode-indexed form

Seal 53 measured that **no consumer of `acval_defn`/`acval_thm` ever
reads the field at a mode other than the one it is working in**, and
ruled the all-mode quantification gratuitous: the front door makes one
run, in one mode, so the all-mode demand is what made the two fields
unsuppliable at a value install (`Denote2ModeAgree`, `Step2Cons.lean`).

**Why this is a new structure and not an edit.**  Re-indexing `EnvS2U`
in place is a *statement* change to every file that binds an
`EnvS2U V env`, and those include `Claims2U.lean` — which reads both
fields at a free `μ` (`whnfStep2_delta_U`, `whnfStep2_delta_thm_U`,
`acvalDefnInstU_noParams`) — and `Keys2.lean`, where `DeclStep2` is
`Nonempty (EnvS2U V env₂)`, i.e. the very conclusion the install lane
produces.  So the de-generalization lands the way seal 18 rules such
amendments land: **new definition plus bridge**, with the old form
untouched and every claim lane still green.

*Nothing is lost by the weakening and the bridge shows it*: an
`EnvS2U` yields an `EnvS2UM` at **every** mode. -/

/-- **The environment invariant, uniqueness form, at one mode.**
Identical to `EnvS2U` except that the two `denote2` fields speak about
the install's own mode `μ` and no other.  Strictly weaker (see
`EnvS2U.toM`), and it is the form a single checker run can supply. -/
structure EnvS2UM (μ : CheckMode) (env : Env) where
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
  /-- **uniqueness at the install's mode**: *if* a definition's value
  annotates *in `μ`*, that annotation is the constant's own leaf -/
  acval_defn : ∀ (φ : Name → Nat) (F : Nat)
    (cv : ConstantVal) (value : Expr) (hint : ReducibilityHint),
    ConstantInfo.defnInfo cv value hint ∈ env.consts →
    ∀ {ra : AVExpr},
      denote2 μ acval env φ F 0 value = some ra →
      ra = acval cv.name φ
  /-- ditto for a theorem's proof value -/
  acval_thm : ∀ (φ : Name → Nat) (F : Nat)
    (cv : ConstantVal) (value : Expr),
    ConstantInfo.thmInfo cv value ∈ env.consts →
    ∀ {ra : AVExpr},
      denote2 μ acval env φ F 0 value = some ra →
      ra = acval cv.name φ
  /-- stored constants inhabit their annotated types.  **Not** indexed:
  seal 53's measurement is about the two `denote2` body fields, and
  `mem_type2`'s consumers were not measured. -/
  mem_type2 : ∀ (ν : CheckMode) (φ : Name → Nat) (fuel : Nat),
    ∀ c ∈ env.consts, ∀ ta : AVExpr,
    denote2 ν acval env φ fuel 0 c.toConstantVal.type = some ta →
    ∀ ρ : Nat → V, interp2 V ρ (acval c.name φ) ∈ˢ interp2 V ρ ta

/-- **The bridge, and the direction is the whole point.**  The
mode-indexed form is a *weakening*, so an all-mode invariant supplies
one at every mode by dropping the quantifier.

The converse is **not claimed false** — no countermodel is exhibited
here — but nothing supplies it: recovering the all-mode fields from
one mode's is exactly the crossing `Denote2ModeAgree`
(`Step2Cons.lean`) names, and the front door makes one run. -/
def EnvS2U.toM {env : Env} (m : EnvS2U V env) (μ : CheckMode) :
    EnvS2UM V μ env where
  base := m.base
  acval := m.acval
  acval_erase := m.acval_erase
  acval_closed := m.acval_closed
  acval_params := m.acval_params
  acval_ok2 := m.acval_ok2
  acval_defn := m.acval_defn μ
  acval_thm := m.acval_thm μ
  mem_type2 := m.mem_type2

end Setlec.SetR.Interp2
