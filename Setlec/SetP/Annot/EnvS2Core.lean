import Setlec.SetR.Annot.EnvS2U

/-!
# `EnvS2Core` — the denote2-free carrier (task #161, P4 — a FINDING)

**The finding.**  The P quarters are stated over `EnvS2UM`, but the P
declaration fold can never *supply* one: the fold must store each new
constant's leaf as its **`denoteP` reading** (bit numerals — otherwise
`DeltaP`, "unfolding does not move the reading", would be false), while
`EnvS2UM.acval_defn`/`acval_thm` insist a successful **`denote2`**
reading of the value *is* the leaf — and the two readings differ in
every binder numeral a sort evaluates above `1`.  One valuation cannot
satisfy both currencies.

**The measurement that makes the fix cheap**: the entire P surface
reads NONE of the denote2-currency fields — no `acval_defn`, no
`acval_thm`, no `mem_type2`, no relational bridge — only the six
denote2-free fields below.  So the carrier slims instead of the
quarters changing content: `EnvS2Core` is `EnvS2U` minus the three
denote2 fields (and minus the mode index, which existed only for
them), `toCore` projects, and the P surface is restated over the core
by a mechanical signature sweep (batch 8).  Canonical helpers the P
surface consumed at the fat carrier are transposed body-for-body, each
next to its consumer and leaving the canonical file untouched:

* `AcvalParams2`/`acvalParams2` (`Step2/DefEqRun.lean`) → `AcvalParamsP`
  /`acvalParamsP`, below;
* `acval_isEmpty`/`acval_oneParam`/`acval_scalar`/`acval_one`/
  `acval_natPair` (`Step2/Levels.lean`) → the `…P` names in
  `Step2/BitLevels.lean`, the level crossing's own file;
* `NatHeads2` (`Step2/InferQ.lean`) → `NatHeadsP` in `Step2/InferP.lean`.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr EnvS)
open Setlec (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable (V : Type w) [SetTheory V]

/-- **The denote2-free environment carrier** (see the module
docstring): exactly the fields the P surface reads. -/
structure EnvS2Core (env : Env) where
  /-- the collapse-lane invariant, contained -/
  base : EnvS V env
  /-- the annotated valuation -/
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

variable {V}

/-- Every mode-indexed invariant projects to the core. -/
def EnvS2UM.toCore {μ : CheckMode} {env : Env}
    (m : EnvS2UM V μ env) : EnvS2Core V env where
  base := m.base
  acval := m.acval
  acval_erase := m.acval_erase
  acval_closed := m.acval_closed
  acval_params := m.acval_params
  acval_ok2 := m.acval_ok2

/-- The all-mode invariant projects to the core. -/
def EnvS2U.toCore {env : Env} (m : EnvS2U V env) : EnvS2Core V env where
  base := m.base
  acval := m.acval
  acval_erase := m.acval_erase
  acval_closed := m.acval_closed
  acval_params := m.acval_params
  acval_ok2 := m.acval_ok2

/-! ### `AcvalParams2`, transposed to the core (batch 8)

`AcvalParams2`/`acvalParams2` (`Step2/DefEqRun.lean`) are stated over
`EnvS2UM`; the P surface consumes them at a carrier that has no mode
index and no `denote2` fields.  The statement is a fact about `acval`
and two valuations only, so it transposes verbatim. -/

/-- **Residue 8, over the core**: the annotated valuation is
level-insensitive (the `EnvS2Core` reading of `AcvalParams2`). -/
def AcvalParamsP {env : Env} (m : EnvS2Core V env) : Prop :=
  ∀ n ci, env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      m.acval n ψ₁ = m.acval n ψ₂

/-- **Residue 8 is discharged over the core** — it is the
`acval_params` field, exactly as in the canonical lane. -/
theorem acvalParamsP {env : Env} (m : EnvS2Core V env) :
    AcvalParamsP m :=
  m.acval_params

end Setlec.SetR.Interp2
