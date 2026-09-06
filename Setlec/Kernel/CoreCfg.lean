import Setlec.Kernel.Env

/-!
# `CoreCfg` — the body template's parameter (task #172, batch B2)

The tri-core order's ratified mechanism (DESIGN.md, task #172 census
part 2 §3 and part 8 §1) was **one body template, three named
flag-free concrete cores**; since the R core's retirement
(2026-09-05) there are **two** — the verified graded core and the
unverified trusted one — under the census's own rule:

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
  clause byte-for-byte (that was the retired `cfgR`, and today only
  `cfgOf .trusted` spells it).  At `cfgP` **and at `cfgT`** the read reduces
  to `pw.isNever`, so the surviving branch inspects the **annotation
  datum** — data, not a flag, which is exactly the census's finding 2
  distinction.  (Since the licence ruling of 2026-09-06 the two
  shipped configs agree on this field; what `cfgT` drops is the
  *validation* of the datum, not the licence that reads it.)
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
(`cfgP.iotaMode = .verified` by `rfl`), so the downstream `ttChecks`
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
  certificate always; at **both shipped cores** it is `true`, and then
  the branch reads the redex's own annotation datum — validated at
  `cfgP` (`AnnotOkP_beta_gate`, `SetP/Step2/GateP.lean`),
  unvalidated at `cfgT`, which is the licence ruling of 2026-09-06
  ("trust the writer, skip the validation").

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
  verbatim (the retired R core, and the retiring `cfgOf .trusted`); at
  `true` it is `inferBodyIO`, whose application clause skips the
  per-argument certificate exactly at a `.never` binder under the
  graph-regime license (`Setlec/SetP/IOLicenseP.lean`).  **`true` at
  both shipped configs since the licence ruling of 2026-09-06**; it is
  its own field, and not merged with `betaGate`, so an attribution
  probe can flip one without the other.  `cfgOf` still maps it to
  `mode.betaGate`, which is what keeps the mode-parametric towers
  intact. -/
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
  iotaMode := .verified

/-- **The trusted core's configuration** (task #172, batch B3; the
licence ruling of 2026-09-06).  Not a second *verified* core — the
trusted core is unproven-sound by the user's own order — but a named
config all the same, because `Cached/CoreT.lean`'s cross-calls into
the shared helpers have to say which configuration they mean, and
`.trusted` is no longer a thing a templated helper can take.

**`cfgT` is `cfgP` with the certification-only bit off, and nothing
else** (`cfgT_eq_cfgP_verified_off` below).  That is the definition of
the mode: the user's ruling of 2026-09-06 reads the omission table's
group B — `betaGate`, `ioGate` — as *licences*, i.e. skips of work
whose correctness rests on an annotation datum that the verified mode
validates.  In the trusted mode the **validation** is omitted (that is
group A, `verified := false`); the licence itself must still apply, or
the mode would be *slower* than the mode it is defined as a subset of.
So both licence fields are `true` here, exactly as at `cfgP`, and what
`cfgT` skips is the group-A validation — the λ-codomain sort check and
the ∀/λ annotation validation — which is census class 1
(acceptance-only guard drops) and is what makes the lane
official-shaped.  Trust the writer, skip the validation.

`iotaMode` is the only other field that differs, and it is inert:
`ttChecks` is `false` at both modes (`cfgP_iotaMode_ttChecks`,
`cfgT_iotaMode_ttChecks`), so the ι cone's one branch is eliminated at
either value.

**`cfgT` is therefore no longer in the image of `cfgOf`**
(`cfgOf_trusted_ne_cfgT`): `cfgOf` maps the *mode-parametric* towers'
`CheckMode` and keeps `mode.betaGate` there, where the P tier's
dead-branch collapse and the establishment/consumption fence live.
Nothing is proved about `cfgT`, so nothing is lost; the divergence is
recorded rather than papered over.

B5/B6 retire `Cached/CoreT.lean` into a full instantiation at this
config; until then it is the residual sharing's name, and naming it is
route C's own discipline (*the config record's fields are the
divergence list*) applied to the trusted side. -/
def cfgT : CoreCfg where
  betaGate := true
  ioGate := true
  verified := false
  iotaMode := .trusted

/-- The transition map from the retiring flag to the template's
parameter.  Every field is written so that the projection of
`cfgOf mode` is the old accessor **definitionally**, for a *variable*
`mode` — that is what makes the template's introduction invisible to
the mode-parametric towers. -/
def cfgOf (mode : CheckMode) : CoreCfg where
  betaGate := mode.betaGate
  ioGate := mode.betaGate
  verified := mode.verifiedChecks
  iotaMode := mode

/-- **The β site's read.**  Spelled as a definition over the `Bool`
field rather than as a field of function type, so that a core's β site
compiles to the retiring flag's own two field reads and no closure
(see `CoreCfg.betaGate`).  The elimination is unchanged: at a
`betaGate := false` config (`cfgOf .trusted`) the conjunction's left
operand is the literal `false`, so the whole read is `false` by `rfl`;
at `cfgP` and at `cfgT` it is the annotation datum. -/
@[inline] def CoreCfg.betaSkip (cfg : CoreCfg) (pw : PropWhen) : Bool :=
  cfg.betaGate && pw.isNever

/-- `cfgOf` at `.verified` **is** the P core's config — by `rfl`,
which is the census's finding 1 (the flag-free core is already
available definitionally) at the record level.  This is the whole
transition map now: `cfgOf` exists for the *mode-parametric* towers,
whose only inhabited instance is the verified one. -/
theorem cfgOf_verified_eq_cfgP : cfgOf .verified = cfgP := rfl

/-- **The trusted config is `cfgP` with the certification-only bit
off** — the licence ruling of 2026-09-06, as one `rfl`.  Read it as
the definition of the mode: `verified` is group A (dropped), and the
only other difference is the inert `iotaMode`. -/
theorem cfgT_eq_cfgP_verified_off :
    cfgT = { cfgP with verified := false, iotaMode := .trusted } := rfl

/-- **`cfgOf .trusted` is NOT `cfgT` any more**, and that is the
ruling's one structural consequence, recorded rather than hidden.

Until 2026-09-06 the two agreed by `rfl` and `Cached/CoreT.lean`'s
cross-calls were "the mode-parametric helper at the mode they always
meant".  With the group-B licences turned on in the trusted mode they
disagree at `betaGate`/`ioGate`: `cfgOf` must keep mapping those to
`mode.betaGate`, because that is where the P tier's dead-branch
collapse (`betaGateFires_off`) and its establishment/consumption fence
(`verified_isNever_of_betaGateFires`) live, and both would be *false*
at a `.trusted` whose gates were on.  `cfgT` is the shipped trusted
core's config; `cfgOf .trusted` is a mode-parametric spelling nothing
ships.  Nothing is proved about either of them, so the split costs no
theorem. -/
theorem cfgOf_trusted_ne_cfgT : cfgOf .trusted ≠ cfgT := fun h =>
  Bool.noConfusion (congrArg CoreCfg.betaGate h)

/-! ## The three fields, eliminated at the core

Census stop condition 2 (*"the config's fields do not compute away by
`rfl` at some core"*) checked, field by field.  Every one is `rfl`.
The `cfgR_*` half of this table retired with `cfgR` (2026-09-05): a
row whose subject no longer exists is not a loosening. -/

@[simp] theorem cfgP_betaSkip (pw : PropWhen) :
    cfgP.betaSkip pw = pw.isNever := rfl
@[simp] theorem cfgP_ioGate : cfgP.ioGate = true := rfl
theorem cfgOf_ioGate (mode : CheckMode) :
    (cfgOf mode).ioGate = mode.betaGate := rfl
@[simp] theorem cfgP_betaGate : cfgP.betaGate = true := rfl
@[simp] theorem cfgP_verified : cfgP.verified = true := rfl
@[simp] theorem cfgP_iotaMode : cfgP.iotaMode = .verified := rfl

/-- The transitional field's downstream read is eliminated at the P
core: `ttChecks` is uninhabited-true, so the ι cone's one branch is
gone by `rfl`, not by a lemma. -/
theorem cfgP_iotaMode_ttChecks : cfgP.iotaMode.ttChecks = false := rfl

/-! ### The same table at `cfgT` (the licence ruling, 2026-09-06)

The trusted core is unverified, so these rows carry no proof
obligation — they are the *statement* of what the mode is, checked by
the elaborator.  Group B is on; group A is off; `iotaMode` is inert. -/

/-- The β licence, ON in the trusted core: the read is the annotation
datum, exactly as at `cfgP` — unvalidated, by design. -/
@[simp] theorem cfgT_betaSkip (pw : PropWhen) :
    cfgT.betaSkip pw = pw.isNever := rfl
@[simp] theorem cfgT_betaGate : cfgT.betaGate = true := rfl
/-- The io licence, ON in the trusted core. -/
@[simp] theorem cfgT_ioGate : cfgT.ioGate = true := rfl
/-- **Group A, the whole mode**: the certification-only checks are the
one thing the trusted core drops. -/
@[simp] theorem cfgT_verified : cfgT.verified = false := rfl
/-- The transitional field is inert at `cfgT` too. -/
theorem cfgT_iotaMode_ttChecks : cfgT.iotaMode.ttChecks = false := rfl

end Setlec
