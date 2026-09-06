import Setlec.Semantics.Ok2
import Setlec.Verify.EnvWF
import Setlec.Verify.Denote.Pinned

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

namespace Setlec.SetP
open Setlec.Semantics
open Setlec.SetModel

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.Semantics (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo)

universe w

variable (V : Type w) [SetTheory V]

/-- **The denote2-free environment carrier** (see the module
docstring): exactly the fields the P surface reads.

**De-based at task #161 S3** (THE SEPARATION, spec point 2).  The
carrier used to *contain* the collapsed-lane invariant (`base : EnvS`)
and to borrow five syntactic facts from it.  It now carries them
itself, from the shared model-free base — `EnvWF` (`Verify/EnvWF`),
`BasisPinnedTT` (`Verify/Denote/Pinned`), `ProjOkT`/`RecCtorsStored`
(`Verify/EnvPreds`) — and the collapsed valuation is *recovered*
rather than stored: `cvalE = erase ∘ acval`, so `acval_erase` is
`rfl`.  The census measured the whole borrowing at 458 sites and found
every one of them syntactic; nothing of the collapsed model crosses. -/
structure EnvS2Core (env : Env) where
  /-- the shared, model-free environment well-formedness -/
  wf : EnvWF env
  /-- the annotated valuation -/
  acval : Name → (Name → Nat) → AVExpr
  /-- every erased leaf is closed (`EnvS.cval_closed`, at `cvalE`);
  consumers read the `cvalE`-spelled `cval_closed` below -/
  cval_closedL : ∀ (n : Name) (ψ : Name → Nat),
    VExpr.Closed ((acval n ψ).erase)
  /-- the reserved basis constants are the pinned declarations, valued
  by their direct pins (V-free, shared with the TT lane); consumers
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
  acval_ok2 : ∀ (n : Name) (ψ : Name → Nat) (ρ : Nat → V),
    AnnotOk2 V ρ (acval n ψ)

variable {V}

/-- **The collapsed valuation, recovered** — the re-supply the census
measured at 135 sites (§1.2).  `AVExpr.erase` is a total syntactic
function the carrier already owns, so no model content is
transported. -/
def EnvS2Core.cvalE {env : Env} (m : EnvS2Core V env) : TConstVal :=
  fun n ψ => (m.acval n ψ).erase

/-- **`acval_erase` is now `rfl`** — it used to be the field tying the
annotated valuation to the contained `EnvS`'s; with `cvalE` derived it
is a definitional identity.  Kept under its old name because 81 P-lane
sites consume it as a rewriting equation. -/
theorem EnvS2Core.acval_erase {env : Env} (m : EnvS2Core V env) :
    ∀ (n : Name) (ψ : Name → Nat), (m.acval n ψ).erase = m.cvalE n ψ :=
  fun _ _ => rfl

/-- `cval_closedL` at the `cvalE` spelling — the form every consumer
reads (`EnvS.cval_closed`'s successor).  The field is stated at the
literal erasure so that the carrier can be built without naming
`cvalE`; the two are definitionally the same fact, and only the
*spelling* matters to `rw`. -/
theorem EnvS2Core.cval_closed {env : Env} (m : EnvS2Core V env) :
    ∀ (n : Name) (ψ : Name → Nat), VExpr.Closed (m.cvalE n ψ) :=
  m.cval_closedL

/-- `basis_pinnedL` at the `cvalE` spelling (`EnvS.basis_pinned`'s
successor). -/
theorem EnvS2Core.basis_pinned {env : Env} (m : EnvS2Core V env) :
    BasisPinnedTT env m.cvalE :=
  m.basis_pinnedL

/-- **A pinned constant's leaf is its direct pin** — `cvalS_pinned`'s
model-free twin (task #161 S7, Wall C step (a)).  The fact is
`basis_pinnedL`'s second component; the `EnvS` form existed only
because the carrier used to borrow the field. -/
theorem EnvS2Core.cvalE_pinned {env : Env} (m : EnvS2Core V env)
    {n : Name} (hres : Setlec.reservedBasisNames.contains n = true)
    (hst : (env.find? n).isSome = true) (ψ : Name → Nat) {t : VExpr}
    (hpin : Setlec.TTVerify.pinnedDirectT n ψ = some t) :
    m.cvalE n ψ = t := by
  cases hf : env.find? n with
  | none => rw [hf] at hst; exact nomatch hst
  | some ci => exact (m.basis_pinned n ci hf hres).2 t ψ hpin

/-- The empty environment's core: the leaf is the bare `.const .empty
[0]` at every name (`EnvS2.empty`'s valuation, one currency over), and
every syntactic field is vacuous over `env.consts = []`. -/
def EnvS2Core.empty : EnvS2Core V Env.empty where
  wf := by intro c hc; cases hc
  acval := fun _ _ => .const .empty [0]
  cval_closedL := fun _ _ => trivial
  basis_pinnedL := BasisPinnedTT.empty _
  proj_ok := ProjOkT.empty
  rec_ctors := RecCtorsStored.empty
  acval_closed := fun _ _ _ => rfl
  acval_params := fun _ _ _ _ _ _ => rfl
  acval_ok2 := fun _ _ _ => by simp

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

end Setlec.SetP
