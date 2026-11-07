module

public import ConLeche.Semantics.WellDenoted
public import ConLeche.Verify.Denote.Pinned

public section

/-!
# `EnvModel` — the environment carrier (task #161, P4)

The leaf valuation `acval` with the facts the model tier reads of it:
the fold stores each new constant's leaf as its **`denote`
reading** (so that unfolding does not move the reading), and the carrier holds only the
syntactic, `V`-free facts about the environment plus the leaves'
closedness, parameter footprint and truthfulness.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable (V : Type w) [SetTheory V]

/-- **The environment carrier** (see the module docstring): exactly the
fields the P surface reads.  The syntactic facts come from the shared
model-free base — `EnvWF` (`Verify/EnvWF`), `BasisPinnedTT`
(`Verify/Denote/Pinned`), `ProjOkT`/`RecCtorsStored` (`Verify/EnvPreds`)
— and the leaf valuation `acval`. -/
structure EnvModel (env : Env) where
  /-- the shared, model-free environment well-formedness -/
  wf : EnvWF env
  /-- the leaf valuation: each constant's reading at a level assignment -/
  acval : Name → (Name → Nat) → Term
  /-- every leaf is closed -/
  cval_closed : ∀ (n : Name) (ψ : Name → Nat),
    Term.Closed (acval n ψ)
  /-- the reserved basis constants are the pinned declarations, valued
  by their direct pins (V-free) -/
  basis_pinned : BasisPinnedTT env acval
  /-- every stored native projection-table entry is a pinned pair
  entry with its block stored (V-free, shared) -/
  proj_ok : ProjOkT env
  /-- every stored recursor rule's constructor is stored (V-free,
  shared) -/
  rec_ctors : RecCtorsStored env
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

/-- **A pinned constant's leaf is its direct pin**, where that reads no
level parameter: `basis_pinned`'s last component. -/
theorem EnvModel.acval_pinned_free {env : Env} (m : EnvModel V env)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hres : ConLeche.reservedBasisNames.contains n = true)
    {ψ : Name → Nat} {t : Term}
    (hpin : ∀ ψ' : Name → Nat, ConLeche.Verify.pinnedStructT n ψ' = some t) :
    m.acval n ψ = t :=
  (m.basis_pinned n ci hf hres).2.2 t ψ (hpin _)

/-- **A pinned constant's leaf is its direct pin**, at a constant stored
at the pin's own level-parameter names. -/
theorem EnvModel.acval_pinned {env : Env} (m : EnvModel V env)
    {n : Name} {ci : ConstantInfo} (hf : env.find? n = some ci)
    (hres : ConLeche.reservedBasisNames.contains n = true)
    {ψ : Name → Nat} {t : Term}
    (hpin : ConLeche.Verify.pinnedStructT n ψ = some t)
    (hl : (ConLeche.pinnedInfo n).toConstantVal.levelParams
      = ci.toConstantVal.levelParams := by rfl) :
    m.acval n ψ = t :=
  (m.basis_pinned n ci hf hres).2.2 t ψ (by
    rw [ConLeche.Verify.pinVal, hl, Level.substFn_param_self]; exact hpin)

/-- **Every leaf is lift-invariant**: `cval_closed` at every cut. -/
theorem EnvModel.acval_closed {env : Env} (m : EnvModel V env)
    (n : Name) (ψ : Name → Nat) (k : Nat) :
    (m.acval n ψ).liftN 1 k = m.acval n ψ :=
  Term.liftN_eq_self (Term.bvarsBelow.mono (Nat.zero_le k) (m.cval_closed n ψ)) 1

/-- The empty environment's core: the leaf is the bare `.const .empty
[0]` at every name, and every syntactic field is vacuous over `env.consts = []`. -/
@[expose] def EnvModel.empty : EnvModel V Env.empty where
  wf := ⟨fun c hc => (by cases hc), fun c hc => (by cases hc), fun t ht => (by cases ht)⟩
  acval := fun _ _ => .const .empty [0]
  cval_closed := fun _ _ => trivial
  basis_pinned := BasisPinnedTT.empty _
  proj_ok := ProjOkT.empty
  rec_ctors := RecCtorsStored.empty
  acval_params := fun _ _ _ _ _ _ => rfl
  acval_wellDenoted := fun _ _ _ => by simp

end ConLeche.Model
