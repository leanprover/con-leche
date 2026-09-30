module

public import ConLeche.Semantics.WellDenoted
import ConLeche.Verify.EnvWF
public import ConLeche.Verify.Denote.Pinned

public section

/-!
# `EnvModel` — the environment carrier (task #161, P4)

The leaf valuation `acval` with the facts the model tier reads of it:
the fold stores each new constant's leaf as its **`denoteMeta`
reading** (bit numerals, so that unfolding does not move the
reading), and the carrier holds only the
syntactic, `V`-free facts about the environment plus the leaves'
closedness, parameter footprint and truthfulness.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable (V : Type w) [SetTheory V]

/-- **The environment carrier** (see the module docstring): exactly the
fields the P surface reads.  The syntactic facts come from the shared
model-free base — `EnvWF` (`Verify/EnvWF`), `BasisPinnedTT`
(`Verify/Denote/Pinned`), `ProjOkT`/`RecCtorsStored` (`Verify/EnvPreds`)
— and the erased valuation is *recovered* rather than stored:
`cvalE = erase ∘ acval`, so `acval_erase` is `rfl`. -/
structure EnvModel (env : Env) where
  /-- the shared, model-free environment well-formedness -/
  wf : EnvWF env
  /-- the annotated valuation -/
  acval : Name → (Name → Nat) → AnnotTerm
  /-- every erased leaf is closed; consumers read the `cvalE`-spelled `cval_closed` below -/
  cval_closedL : ∀ (n : Name) (ψ : Name → Nat),
    Term.Closed ((acval n ψ).erase)
  /-- the reserved basis constants are the pinned declarations, valued
  by their direct pins (V-free); consumers
  read the `cvalE`-spelled `basis_pinned` below -/
  basis_pinnedL : BasisPinnedTT env (fun n ψ => (acval n ψ).erase)
  /-- every stored native projection-table entry is a pinned pair
  entry with its block stored (V-free, shared) -/
  proj_ok : ProjOkT env
  /-- every stored recursor rule's constructor is stored (V-free,
  shared) -/
  rec_ctors : RecCtorsStored env
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
  acval_wellDenoted : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    WellDenoted V ρ (acval n ψ)

variable {V}

/-- **The erased valuation, recovered**: `AnnotTerm.erase` is a total
syntactic function the carrier already owns. -/
@[expose] def EnvModel.cvalE {env : Env} (m : EnvModel V env) : TConstVal :=
  fun n ψ => (m.acval n ψ).erase

/-- **`acval_erase` is `rfl`** — with `cvalE` derived it is a
definitional identity, consumed as a rewriting equation. -/
theorem EnvModel.acval_erase {env : Env} (m : EnvModel V env) :
    ∀ (n : Name) (ψ : Name → Nat), (m.acval n ψ).erase = m.cvalE n ψ :=
  fun _ _ => rfl

/-- `cval_closedL` at the `cvalE` spelling — the form every consumer
reads.  The field is stated at the
literal erasure so that the carrier can be built without naming
`cvalE`; the two are definitionally the same fact, and only the
*spelling* matters to `rw`. -/
theorem EnvModel.cval_closed {env : Env} (m : EnvModel V env) :
    ∀ (n : Name) (ψ : Name → Nat), Term.Closed (m.cvalE n ψ) :=
  m.cval_closedL

/-- `basis_pinnedL` at the `cvalE` spelling. -/
theorem EnvModel.basis_pinned {env : Env} (m : EnvModel V env) :
    BasisPinnedTT env m.cvalE :=
  m.basis_pinnedL

/-- **A pinned constant's leaf is its direct pin**: `basis_pinnedL`'s
second component. -/
theorem EnvModel.cvalE_pinned {env : Env} (m : EnvModel V env)
    {n : Name} (hres : ConLeche.reservedBasisNames.contains n = true)
    (hst : (env.find? n).isSome = true) (ψ : Name → Nat) {t : Term}
    (hpin : ConLeche.Verify.pinnedStructT n ψ = some t) :
    m.cvalE n ψ = t := by
  cases hf : env.find? n with
  | none => rw [hf] at hst; exact nomatch hst
  | some ci => exact (m.basis_pinned n ci hf hres).2 t ψ hpin

/-- The empty environment's core: the leaf is the bare `.const .empty
[0]` at every name, and every syntactic field is vacuous over `env.consts = []`. -/
@[expose] def EnvModel.empty : EnvModel V Env.empty where
  wf := by intro c hc; cases hc
  acval := fun _ _ => .const .empty [0]
  cval_closedL := fun _ _ => trivial
  basis_pinnedL := BasisPinnedTT.empty _
  proj_ok := ProjOkT.empty
  rec_ctors := RecCtorsStored.empty
  acval_closed := fun _ _ _ => rfl
  acval_params := fun _ _ _ _ _ _ => rfl
  acval_wellDenoted := fun _ _ _ => by simp

/-! ### Level-insensitivity of the leaf valuation -/

/-- **Residue 8**: the annotated valuation is level-insensitive. -/
@[expose] def AcvalParams {env : Env} (m : EnvModel V env) : Prop :=
  ∀ n ci, env.find? n = some ci →
    ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ p ∈ ci.toConstantVal.levelParams, ψ₁ p = ψ₂ p) →
      m.acval n ψ₁ = m.acval n ψ₂

/-- **Residue 8 is discharged** — it is the `acval_params` field. -/
theorem acvalParams {env : Env} (m : EnvModel V env) :
    AcvalParams m :=
  m.acval_params

end ConLeche.Model
