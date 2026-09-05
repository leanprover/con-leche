import Setlec.Kernel.Env

/-!
# `CoreCfg` — the body template's parameter (task #172, batch B2)

The tri-core order's ratified mechanism (DESIGN.md, task #172 census
part 2 §3 and part 8 §1) was **one body template, three named
flag-free concrete cores**; since the R core's retirement
(2026-09-05) there are **two** — the verified graded core and the
unverified parity one — under the census's own rule:

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
  the certificate's `Bool`.  At a `betaGate := false` config the read
  `cfg.betaSkip pw` reduces to `false`, so the gated `if` *is* its
  `else` arm — definitionally, and the `else` arm is the pre-gate
  clause byte-for-byte (that was the retired `cfgR`, and it is still
  `cfgNC`).  At `cfgP` the read reduces to `pw.isNever`, so the
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
(`cfgP.iotaMode = .setModelP` by `rfl`), so the downstream `ttChecks`
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

/-- **The P core's configuration** — since 2026-09-05 the checker's
only *verified* one: the β skip at `pw = .never` baked in, reading the
validated annotation datum (census part 2 §2(c)1), and the io-graded
knot slot on.  Every other certificate is unconditional — the
establishment/consumption asymmetry fence
(`gate_zero_kind_unreachable`) is why. -/
def cfgP : CoreCfg where
  betaGate := true
  ioGate := true
  verified := true
  iotaMode := .setModelP

/-- **The concrete verified mode the shared declaration bridge is
instantiated at** (task #172 batch B3, as `modeR`; re-read 2026-09-05).

`Kernel/Core.lean`'s reference body is parameterized by `CheckMode` —
it is what the whole shared base library (`Verify/*`, most of
`SetBase/*`) is stated over, generically, and census part 2 finding 2
keeps it there: *genericity* in a proof is not a flag.  This is the
name a tower instantiates that genericity at.

`modeR` is an `abbrev`, so it is reducible and every accessor
computes: `modeR.betaGate = false` and `modeR.verified = true` are
`rfl`.  That is what `SetBase/Bridge/*`'s derivation tier needs —
`checkBridge` is premised on `mode.betaGate = false` — and it is why
the bridge cannot simply be re-pointed at `.setModelP`.

**WHAT CHANGED AT THE SetR REMOVAL** (2026-09-05).  `modeR` was named
for the R core, and the R core is gone: `cfgR`, the four `…RC` bodies
and the `--set-model=r` spelling retired with the collapsed-model
consistency proof they were the subject of.  What survives under this
name is *not* a core selection but a **proof-tier constant**: the mode
at which `SetBase/Bridge/{Main,Decl,DeclInd}` states the derivation
bridge.  Measured (`_tmp/setr-b/Probe.lean`): `modeR`, `cfgR`,
`checkBridge`, `declDefnR` and `checkDeclR_ofEnvRE` are **absent** from
both surviving capstones' proof-term closures and from the run route
(`checkDeclRun_ofEnvRE`, `declIndRunRR`) the graded fold actually
calls — so this whole tier is off the shipped path, and its deletion is
a separate, larger question than the core's (it retires four of
`tests/proofdeps.sh`'s ten targets, which is the campaign's own
instrument). Flagged, not taken. -/
abbrev modeR : CheckMode := .setModel

/-- `modeR`'s gate is off, by the constructor — the premise
`SetBase/Bridge/Main.lean`'s `checkBridge` takes, as a `rfl`. -/
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
(see `CoreCfg.betaGate`).  The elimination is unchanged: at a
`betaGate := false` config (`cfgNC`) the conjunction's left operand is
the literal `false`, so the whole read is `false` by `rfl`, and at
`cfgP` it is the annotation datum. -/
@[inline] def CoreCfg.betaSkip (cfg : CoreCfg) (pw : PropWhen) : Bool :=
  cfg.betaGate && pw.isNever

/-- `cfgOf` at `.setModelP` **is** the P core's config — by `rfl`,
which is the census's finding 1 (the flag-free core is already
available definitionally) at the record level. -/
theorem cfgOf_setModelP : cfgOf .setModelP = cfgP := rfl

/-- `cfgOf` at `.noModel` **is** the parity core's config, by `rfl` —
so the seven parity cross-calls into the shared helpers are, still,
the mode-parametric helper at the mode they always meant. -/
theorem cfgOf_noModel : cfgOf .noModel = cfgNC := rfl

/-! ## The three fields, eliminated at the core

Census stop condition 2 (*"the config's fields do not compute away by
`rfl` at some core"*) checked, field by field.  Every one is `rfl`.
The `cfgR_*` half of this table retired with `cfgR` (2026-09-05): a
row whose subject no longer exists is not a loosening. -/

@[simp] theorem cfgP_betaSkip (pw : PropWhen) :
    cfgP.betaSkip pw = pw.isNever := rfl
@[simp] theorem cfgP_ioGate : cfgP.ioGate = true := rfl
@[simp] theorem cfgNC_ioGate : cfgNC.ioGate = false := rfl
theorem cfgOf_ioGate (mode : CheckMode) :
    (cfgOf mode).ioGate = mode.betaGate := rfl
@[simp] theorem cfgP_betaGate : cfgP.betaGate = true := rfl
@[simp] theorem cfgP_verified : cfgP.verified = true := rfl
@[simp] theorem cfgP_iotaMode : cfgP.iotaMode = .setModelP := rfl

/-- The transitional field's downstream read is eliminated at the P
core: `ttChecks` is uninhabited-true, so the ι cone's one branch is
gone by `rfl`, not by a lemma. -/
theorem cfgP_iotaMode_ttChecks : cfgP.iotaMode.ttChecks = false := rfl

end Setlec
