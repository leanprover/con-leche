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

* the β field is a **pure early-return gate**, not a wrapper around
  the certificate's `Bool`.  At `cfgR` the read `cfgR.betaSkip pw`
  reduces to `false`, so the gated `if` *is* its `else` arm —
  definitionally, and the `else` arm is the pre-gate clause
  byte-for-byte.  At `cfgP` the read reduces to `pw.isNever`, so the
  surviving branch inspects the **validated annotation datum** — data,
  not a flag, which is exactly the census's finding 2 distinction.
  (The field itself is a `Bool` and `betaSkip` a definition over it;
  a field of *function* type eliminates just as well but is a closure
  at every β site — measured at B2, +0.36 % on `init-prelude`.);
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
  /-- Is the β-certificate skip on?  Read (through `betaSkip`) at
  `whnfCore`'s β site.  `false` runs the per-redex argument
  certificate always; at the P core it is `true`, and then the branch
  reads the redex's own *validated* annotation datum
  (`AnnotOkP_beta_gate`, `SetP/Step2/GateP.lean`).

  **A `Bool` and not a `PropWhen → Bool`, on measured grounds.**  Both
  shapes satisfy the `rfl`-eliminability requirement, but a function
  field is a closure at every β site: measured at B2, the function
  shape cost **+0.36 % instructions on `init-prelude`** (β-heavy
  `app-lam` was unmoved).  The `Bool` field's codegen is the retiring
  flag's, exactly. -/
  betaGate : Bool
  /-- Is the **io-grade knot slot** the io body (task #170 / #172 B4)?
  Read once per knot level to select what the internal inference call
  sites run: at `false` the io slot is the full inference body,
  verbatim (the flag is ignored — the R core and the parity core); at
  `true` it is `inferBodyIO`, whose application clause skips the
  per-argument certificate exactly at a validated `.never` binder
  under the graph-regime license (`Setlec/SetP/IOLicenseP.lean`).
  Maps to the same mode bit as `betaGate` (`cfgOf` reads
  `mode.betaGate` for both) — the two skips are sibling licenses of
  the one validated-annotation regime — but is its own field so an
  attribution probe can flip one without the other. -/
  ioGate : Bool
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
  betaGate := false
  ioGate := false
  verified := true
  iotaMode := .setModel

/-- **The P core's configuration**: the β skip at `pw = .never` baked
in, reading the validated annotation datum (census part 2 §2(c)1).
Every other certificate is `cfgR`'s — the establishment/consumption
asymmetry fence (`gate_zero_kind_unreachable`) is why. -/
def cfgP : CoreCfg where
  betaGate := true
  ioGate := true
  verified := true
  iotaMode := .setModelP

/-- **The R core, at the pure tier** (task #172, batch B3).

`Kernel/Core.lean`'s reference body is still parameterized by
`CheckMode` — it is what the whole shared base library
(`Verify/*`, most of `SetBase/*`) is stated over, generically, and
census part 2 finding 2 keeps it there: *genericity* in a proof is not
a flag.  What the tri-core order retires is the R **tower**'s
quantification over it, and this is the name the tower instantiates
at.

`modeR` is an `abbrev`, so it is reducible and every accessor
computes: `modeR.betaGate = false` and `modeR.verified = true` are
`rfl`, which is exactly how the R capstones' `(hg : μ.betaGate =
false)` hypotheses were discharged away — not by a lemma, by the
constructor.  `cfgOf modeR = cfgR` is `rfl` too (`cfgOf_setModel`), so
the pure-tier name and the templated-core config are the same
selection said twice.

The precedent is in the tree: `SetR/Annot/PremiseLadder.lean` has
carried `μ0 : CheckMode := .setModel` since the refutation ladder was
built, for the same reason — a lane's proofs run at that lane's
concrete mode. -/
abbrev modeR : CheckMode := .setModel

/-- `modeR`'s gate is off, by the constructor.  This is the R
capstones' retired hypothesis, as a `rfl`. -/
theorem modeR_betaGate : modeR.betaGate = false := rfl

/-- `modeR` is a verified mode, by the constructor. -/
theorem modeR_verified : modeR.verified = true := rfl

/-- **The production-parity core's configuration** (task #172, batch
B3).  Not a third *verified* core — the parity core is unproven-sound
by the user's own order — but a named config all the same, because
`Cached/CoreNC.lean`'s cross-calls into the shared helpers have to say
which configuration they mean, and `.noModel` is no longer a thing a
templated helper can take.

Its `verified := false` is the *whole* content of the parity lane's
divergence at these seven sites: the λ-codomain sort check and the ∀/λ
annotation validation are off, which is census class 1
(acceptance-only guard drops) and is what makes the lane
official-shaped.  `cfgNC.betaGate` is `false` for the same reason the
R core's is: there is no validated datum at parity, so there is
nothing a gate could read.

B5/B6 retire `Cached/CoreNC.lean` into a full instantiation at this
config; until then it is the residual sharing's name, and naming it is
route C's own discipline (*the config record's fields are the
divergence list*) applied to the parity side. -/
def cfgNC : CoreCfg where
  betaGate := false
  ioGate := false
  verified := false
  iotaMode := .noModel

/-- The transition map from the retiring flag to the template's
parameter.  Every field is written so that the projection of
`cfgOf mode` is the old accessor **definitionally**, for a *variable*
`mode` — that is what makes the template's introduction invisible to
the mode-parametric towers. -/
def cfgOf (mode : CheckMode) : CoreCfg where
  betaGate := mode.betaGate
  ioGate := mode.betaGate
  verified := mode.verified
  iotaMode := mode

/-- **The β site's read.**  Spelled as a definition over the `Bool`
field rather than as a field of function type, so that a core's β site
compiles to the retiring flag's own two field reads and no closure
(see `CoreCfg.betaGate`).  The elimination is unchanged: at `cfgR` the
conjunction's left operand is the literal `false`, so the whole read is
`false` by `rfl`, and at `cfgP` it is the annotation datum. -/
@[inline] def CoreCfg.betaSkip (cfg : CoreCfg) (pw : PropWhen) : Bool :=
  cfg.betaGate && pw.isNever

/-- `cfgOf` at `.setModel` **is** the R core's config — by `rfl`, which
is the census's finding 1 (the flag-free core is already available
definitionally) at the record level. -/
theorem cfgOf_setModel : cfgOf .setModel = cfgR := rfl

/-- `cfgOf` at `modeR` **is** the R core's config, by `rfl` — the
pure tier's name and the template's config are one selection said
twice. -/
theorem cfgOf_modeR : cfgOf modeR = cfgR := rfl

/-- `cfgOf` at `.setModelP` **is** the P core's config, by `rfl`. -/
theorem cfgOf_setModelP : cfgOf .setModelP = cfgP := rfl

/-- `cfgOf` at `.noModel` **is** the parity core's config, by `rfl` —
so the seven parity cross-calls into the shared helpers are, still,
the mode-parametric helper at the mode they always meant. -/
theorem cfgOf_noModel : cfgOf .noModel = cfgNC := rfl

/-! ## The three fields, eliminated at each core

Census stop condition 2 (*"the config's fields do not compute away by
`rfl` at some core"*) checked, field by field, at both cores B2
scopes.  Every one is `rfl`. -/

@[simp] theorem cfgR_betaSkip (pw : PropWhen) : cfgR.betaSkip pw = false := rfl
@[simp] theorem cfgP_betaSkip (pw : PropWhen) :
    cfgP.betaSkip pw = pw.isNever := rfl
@[simp] theorem cfgR_betaGate : cfgR.betaGate = false := rfl
@[simp] theorem cfgR_ioGate : cfgR.ioGate = false := rfl
@[simp] theorem cfgP_ioGate : cfgP.ioGate = true := rfl
@[simp] theorem cfgNC_ioGate : cfgNC.ioGate = false := rfl
theorem cfgOf_ioGate (mode : CheckMode) :
    (cfgOf mode).ioGate = mode.betaGate := rfl
@[simp] theorem cfgP_betaGate : cfgP.betaGate = true := rfl
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
