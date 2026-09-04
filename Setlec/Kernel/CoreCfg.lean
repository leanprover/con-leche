import Setlec.Kernel.Env

/-!
# `CoreCfg` — the body template's parameter (task #172, batch B2)

The tri-core order's ratified mechanism (DESIGN.md, task #172 census
part 2 §3 and part 8 §1) is **one body template, three named flag-free
concrete cores**, under the census's own rule:

> *A configuration value may survive only where it is (i) universally
> quantified in a proof, or (ii) definitionally eliminated in a shipped
> core.  It may never be read at a branch in a shipped core.*

`CheckMode` (`Setlec/Kernel/Env.lean`) is the thing being retired: it
is a *flag*, read at branches inside the shipped cores.  `CoreCfg` is
its replacement as a **template parameter** — a record whose every
field computes away by `rfl` at each named concrete core, so that the
core's branches disappear rather than collapse.

## The `rfl`-eliminability requirement (census part 6 §5 item 2)

This is the whole mechanism, and it is why the fields are shaped the
way they are:

* `betaSkip` is a **function** field, not a `Bool`-valued gate applied
  to a wrapper.  At `cfgR` it is `fun _ => false`, so
  `cfgR.betaSkip pw` reduces to `false` and the gated `if` *is* its
  `else` arm, definitionally.  At `cfgP` it is `PropWhen.isNever`, so
  the surviving branch reads the **validated annotation datum** — data,
  not a flag, which is exactly the census's finding 2 distinction;
* every field of `cfgOf mode` is a *projection of a literal
  constructor*, so `(cfgOf mode).betaSkip pw` is `betaGateFires mode
  pw` by `rfl` for a **variable** `mode` too.  That is what lets the
  template be introduced without disturbing a single mode-parametric
  statement in the towers (`cfgOf_betaSkip`, `Verify/BetaGate.lean`).

## `iotaMode` — the transitional field, named on purpose

B2 slices the `whnfCore` clause family.  The ι cone below it
(`iotaRec` → `majorToCtor` → `structEtaCertWith`) still takes a
`CheckMode`, and its *only* read is `CheckMode.ttChecks`, which the
census proved uninhabited-true (part 8 §3(a): `ttChecks = true` has no
inhabitant, so no theorem can consume it).  Rather than pretend the
residue is not there, it is a **named field**: `iotaMode` carries the
mode the ι cone still wants, and at each concrete core it is a literal
(`cfgR.iotaMode = .setModel` by `rfl`), so the downstream `ttChecks`
branch is *definitionally eliminated* — the rule's clause (ii), and
the reason the concrete cores are flag-free today even though the ι
cone has not been templated yet.

`iotaMode` retires with the `ttChecks` row (census part 8 §3(c),
sequenced with B3/B4), at which point the ι cone loses its parameter
outright.  The cost of doing it now instead was measured at B2 and is
reported in the batch's seal.
-/

namespace Setlec

/-- **The body template's configuration record.**  One value per core;
every field must compute away by `rfl` at each named core (see the
module docstring). -/
structure CoreCfg where
  /-- The β-certificate skip predicate, read at `whnfCore`'s β site.
  `fun _ => false` runs the per-redex argument certificate always; at
  the P core it is `PropWhen.isNever`, i.e. the skip is licensed by the
  redex's own *validated* annotation datum (`AnnotOkP_beta_gate`,
  `SetP/Step2/GateP.lean`). -/
  betaSkip : PropWhen → Bool
  /-- The verified lanes' extra checks: the λ-codomain sort check and
  the ∀/λ annotation validation.  Carried by the record from B2 on;
  the clauses that read it are `inferBody`'s and `defeqStep`'s, which
  B3/B4 template. -/
  verified : Bool
  /-- **TRANSITIONAL** (see the module docstring): the `CheckMode` the
  not-yet-templated ι cone still takes.  Retires with the `ttChecks`
  row. -/
  iotaMode : CheckMode

/-- **The R core's configuration**: every certificate unconditional.
No gate, no skip — the census's part 2 §2(b) core. -/
def cfgR : CoreCfg where
  betaSkip := fun _ => false
  verified := true
  iotaMode := .setModel

/-- **The P core's configuration**: the β skip at `pw = .never` baked
in, reading the validated annotation datum (census part 2 §2(c)1).
Every other certificate is `cfgR`'s — the establishment/consumption
asymmetry fence (`gate_zero_kind_unreachable`) is why. -/
def cfgP : CoreCfg where
  betaSkip := PropWhen.isNever
  verified := true
  iotaMode := .setModelP

/-- The transition map from the retiring flag to the template's
parameter.  Every field is written so that the projection of
`cfgOf mode` is the old accessor **definitionally**, for a *variable*
`mode` — that is what makes the template's introduction invisible to
the mode-parametric towers. -/
def cfgOf (mode : CheckMode) : CoreCfg where
  betaSkip := fun pw => mode.betaGate && pw.isNever
  verified := mode.verified
  iotaMode := mode

/-- `cfgOf` at `.setModel` **is** the R core's config — by `rfl`, which
is the census's finding 1 (the flag-free core is already available
definitionally) at the record level. -/
theorem cfgOf_setModel : cfgOf .setModel = cfgR := rfl

/-- `cfgOf` at `.setModelP` **is** the P core's config, by `rfl`. -/
theorem cfgOf_setModelP : cfgOf .setModelP = cfgP := rfl

/-! ## The three fields, eliminated at each core

Census stop condition 2 (*"the config's fields do not compute away by
`rfl` at some core"*) checked, field by field, at both cores B2
scopes.  Every one is `rfl`. -/

@[simp] theorem cfgR_betaSkip (pw : PropWhen) : cfgR.betaSkip pw = false := rfl
@[simp] theorem cfgP_betaSkip (pw : PropWhen) :
    cfgP.betaSkip pw = pw.isNever := rfl
@[simp] theorem cfgR_verified : cfgR.verified = true := rfl
@[simp] theorem cfgP_verified : cfgP.verified = true := rfl
@[simp] theorem cfgR_iotaMode : cfgR.iotaMode = .setModel := rfl
@[simp] theorem cfgP_iotaMode : cfgP.iotaMode = .setModelP := rfl

/-- The transitional field's downstream read is eliminated at the R
core: `ttChecks` is uninhabited-true, so the ι cone's one branch is
gone by `rfl`, not by a lemma. -/
theorem cfgR_iotaMode_ttChecks : cfgR.iotaMode.ttChecks = false := rfl

/-- …and at the P core. -/
theorem cfgP_iotaMode_ttChecks : cfgP.iotaMode.ttChecks = false := rfl

end Setlec
