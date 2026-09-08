module

public import ConLeche.Kernel.Expr

@[expose] public section

/-!
# Declarations and the global environment

Input declarations mirror `Lean.Declaration` (only the kinds the checker
supports so far are present; more are added feature by feature).

The environment is, for now, a simple association list of checked constants.
This is the *verified* reference representation; a faster indexed structure
can replace it later, with a proof that it refines this one.
-/

namespace ConLeche

/-- **The checker's mode setting** — two values since the R core's
retirement (2026-09-05), validated once at startup and threaded as
configuration, never re-read at runtime (the `structsEnabled`
discipline).

* `.verified` (the default, `--verified`): the verified lane.  The
  surface the **graded** set-theoretic
  model proves — `no_proof_of_Empty_cached`
  (`ConLeche/Verify/Cached/MainC.lean`) is its letter over the driver
  this binary runs.  The seven TT-lane checks (tasks #126, #129, #130,
  #135, #136, #137, #146) are off; the β-certificate gate is on — at a
  λ-binder whose **validated** annotation is `.never` the per-redex
  argument certificate is skipped (`betaTest`,
  `ConLeche/Kernel/Core.lean`) — and the io-graded knot slot skips the
  per-argument application certificate under the same licence.  Every
  other certificate family runs unconditionally.
* `.trusted` (`--trusted`): the unverified lane — the same checker
  with the work that exists **for certification only** omitted.
  What must not be dropped is everything believed necessary for
  *soundness* (which is different from "necessary for our soundness
  proof to go through"), so the lane is never optimized on its own:
  it is the real mode with certain steps omitted (DESIGN.md, "MODE
  RENAME").  Since 2026-09-06 it is literally that: the one cached
  driver (`ConLeche/Cached/ParsedC.lean`) at `.trusted`, where
  `verifiedChecks` and `certs` are `false` — so what it omits is
  exactly what those two functions gate in `ConLeche/Cached/CoreC.lean`
  (DESIGN.md, "CORET RETIRED").

**The mode is the cores' only parameter** (task #185, 2026-09-06).
The configuration record that stood between the mode and the
shipped cores from task #172 B2 to task #185 is gone: every field it
carried is a function on `CheckMode` below (`ttChecks`,
`verifiedChecks`, `betaGate`, `ioGate`, `certs`), each a `match` on
the two constructors, so each read reduces by `rfl` at either mode —
the record's `rfl`-eliminability argument, at the enum itself.

**HISTORY, because the spelling moved twice.**  There were three
values until 2026-09-05: `.setModel` at `--set-model=r` (the R lane —
every certificate unconditional), `.setModelP` at `--set-model=p` (the
graded lane) and `.noModel`.  The user's ruling removed the
collapsed-model consistency proof, and the R core went with the proof
it was the subject of, the acceptance delta between the two verified
lanes having measured **zero**; the graded value then took the retired
one's name, `.setModel`.  On 2026-09-06 the *vocabulary* was renamed
to say what the two modes are for rather than which artefact proves
them: `.setModel` → `.verified` (`--set-model`/`--set-model=p` →
`--verified`) and `.noModel` → `.trusted` (`--no-model` →
`--trusted`).  Every retired spelling is a hard error naming its
successor, never a silent alias (DESIGN.md, "MODE RENAME"). -/
inductive CheckMode where
  | verified
  | trusted
  deriving DecidableEq, Repr, Inhabited

/-- Are the seven TT-lane checks enabled?  The one accessor the kernel
branches on — **constantly `false` since task #148 T7b**, when the
declarative verification lane and its `.ttModel` mode were retired
together.  The gated call sites are kept, statically unreachable, so
that the checks themselves survive as reviewed code and the accessor
stays the single place a future lane would turn them back on. -/
def CheckMode.ttChecks : CheckMode → Bool
  | _ => false

/-- Are the *verified* mode's extra checks enabled — the checks the
model lane wants and the trusted lane must not run, because they are
needed for the soundness *proof* rather than for soundness?  The
second accessor the kernel branches on
(task #152: the λ-rule's codomain-sort check, `inferBody`'s `.lam`
clause).  This is deliberately **not** `ttChecks`: the λ codomain sort
is a premise of the set lane's annotation pass (`ConLeche/Model`), so it
must run at `.verified`; and it is a check the reference kernel's
`infer_lambda` does not run, so it must not run at `.trusted`. -/
def CheckMode.verifiedChecks : CheckMode → Bool
  | .trusted => false
  | _ => true

/-- Is the **β-certificate gate** on (task #161)?  The third accessor
the kernel branches on: at a λ-binder whose validated annotation datum
is `.never` the per-redex argument certificate is skipped (`betaTest`,
`ConLeche/Kernel/Core.lean`).

Two disciplines ride on this accessor being a *mode* accessor rather
than a second knot:

* **the establishment/consumption asymmetry fence** — the gate reads a
  *validated* annotation (only meaningful where
  `verifiedChecks = true`) and
  wraps the **test** only, so no certificate a possibly-zero datum
  needs is ever skipped;
* **the dead-branch collapse** — at `betaGate = false` the gated test
  is definitionally the ungated one (`betaTest_of_gate_off`), which is
  what keeps the trusted lane's proofs one rewrite away from their
  pre-gate form.

Since the R core's retirement the gate is on at the *only* verified
mode, so `betaGate` and `verifiedChecks` now agree except at
`.trusted`.
They stay two accessors because they gate different checks and the
kernel reads them at different sites. -/
def CheckMode.betaGate : CheckMode → Bool
  | .verified => true
  | _ => false

/-- Is the **io-grade knot slot** the io body (task #170 / #172 B4)?
Read once per knot level by the cached knot (`coreKnotI`,
`ConLeche/Cached/CoreC.lean`) to select what the internal inference call
sites run: the io body, whose application clause skips the
per-argument certificate at a `.never` binder under the graph-regime
licence (`ConLeche/Model/IOLicense.lean`) — official's `infer_only`.
**`true` at both modes** since the licence ruling of 2026-09-06 (the
trusted mode is defined as the verified one minus certification-only
work, and the io grade is a *licence*, not a certificate; the retired
trusted configuration record had it `true` too).  It is its own
function, and not `betaGate`, so that an attribution probe can flip
one without the other; the
mode-parametric spec knot (`coreKnot`, `ConLeche/Kernel/Core.lean`)
selects its io slot on `betaGate`, the P tier's own bit, so the two
agree exactly at `.verified` — the one instance the simulation tower
is stated at (`memoEI_inferIO_sim`, `ConLeche/Verify/Cached/KnotC.lean`).
Spelled with a wildcard so it is the literal `true` at a *variable*
mode too. -/
def CheckMode.ioGate : CheckMode → Bool
  | _ => true

/-- **The certificate families** (task #76's skip list; the twin's
retirement, 2026-09-06): the work the checker does *only* so the
soundness proof can consume it, and that the reference kernel does not
do — the β-redex argument certificate (`whnfAppI`/`betaPeelI`, through
`betaSkip`), the io-grade application argument certificate
(`inferSpineIOI`, through `ioSkip`), the recursor/constructor telescope
certificates and the canonical-index comparison of ι (`iotaRecI`), the
plain-rule parameter re-comparison, the type-former and per-projection
telescope certificates of structure η and unit-like conversion
(`structEtaCertWithI`, `structUnitCertI`), and the K/η rescue's
synthetic-spine and proof-irrelevance certificates (`majorToCtorI`).
Read through `ConLeche/Cached/CoreC.lean`'s `certAtI`/`certUnlessI` and
the two skip predicates below; `true` runs them, `false` (the trusted
mode) skips them outright.

**Why a second function beside `verifiedChecks`**, when the two agree
at both constructors.  Both are certification-only work; they differ
in what the proof towers need of them.  `verifiedChecks` gates checks
the P tier's *premises* rest on (the λ-codomain sort, the annotation
validations), so the mode-parametric spec (`ConLeche/Kernel/Core.lean`)
reads it at the same sites the cached core does.  The certificate
families have **no switch in the spec** — no proved instance ever
omits them — so the cached core's reads of `certs` are what the
simulation tower (`ConLeche/Verify/Cached/*`) must see through: it is
stated under `hμ : mode.verifiedChecks = true`, and
`certs_of_verifiedChecks` (`ConLeche/Verify/BetaGate.lean`) turns every
read into the literal `true` there.  The `.trusted` instance of the
cached-vs-spec simulation is false, deliberately: the trusted core
skips what the spec runs. -/
def CheckMode.certs : CheckMode → Bool
  | .verified => true
  | .trusted => false

/-- **The β site's read** (`whnfAppI`/`betaPeelI`): skip the per-redex
argument certificate wholesale when the certificate families are off,
else exactly when the β gate is on and the (validated) annotation
datum is `.never`.  At `.verified` it is the datum (`pw.isNever`, the
same predicate as the spec's `betaGateFires .verified pw`); at
`.trusted` the literal `true` — the β certificate is a certificate
family, skipped outright, so the licence is moot there. -/
@[inline] def CheckMode.betaSkip (mode : CheckMode) (pw : PropWhen) : Bool :=
  !mode.certs || (mode.betaGate && pw.isNever)

/-- **The io site's read** (`inferSpineIOI`): skip the per-argument
application certificate at a `.never` binder (the graph-regime
licence, `ConLeche/Model/IOLicense.lean`), or wholesale when the
certificate families are off.  At `.verified` it is `pw.isNever` — the
licence reads the datum and nothing else, as the licence ruling of
2026-09-06 has it — and at `.trusted` it is `true`. -/
@[inline] def CheckMode.ioSkip (mode : CheckMode) (pw : PropWhen) : Bool :=
  !mode.certs || pw.isNever

/-- Data common to all constants: name, universe parameters, type. -/
structure ConstantVal where
  name : Name
  levelParams : List Name
  type : Expr
  deriving DecidableEq, Repr, Inhabited

/-- How a stored recursor rule may fire (install-computed; parse
placeholder `.inert`).

* `.plain` — a canonical rule (`Expr.recRulePlain`): the constructor's
  parameters are the recursor's leading arguments and its levels link
  to the recursor's by name.
* `.nested lvls pins` — a certified nested-auxiliary rule: the
  constructor's levels and parameters are *fixed instantiations*, read
  at install off the recursor type's major-premise domain — `lvls`
  are levels over the recursor's level parameters, `pins` expressions
  in the recursor's `rulePrefix`-binder telescope context (index
  premises between the prefix and the major are supported: the shape
  certification lowers the stored instantiations out of the
  `majorIdx`-binder context after checking that no index variable
  occurs in them).  At fire time the constructor's levels and
  parameters are checked against these, instantiated at the recursor's
  actual level and leading-argument spine.
* `.inert` — never fires; a *matched* inert rule is a positive
  decline in `iotaRec` (an uncertified nested auxiliary rule).

**Why the fire compares parameters, levels and indices at all** (the
official kernel's `inductive_reduce_rec` and lean4lean fire by
constructor name plus `nfields` and compare nothing — typing justifies
it).  Our soundness argument for a fire is the stored rule law
(`RecRuleLaw`) at the recursor's own parameters, and the P lane has no
typing derivation in hand: the redex is only `WellDenotedV`, and since the
ι-slot licence (2026-09-05) the major slot of a data-motive recursor is
not even inferred, so nothing but these comparisons relates the
constructor's `p⃗'`/`idx'` to the recursor's `p⃗`/`idx`.  Moving them
into a licence was investigated (2026-09-06, `_tmp/iota-uniform/`):
for *indices* it is refuted at the squash regime (`Acc.rec.{1}` on a
cross-index `Acc.intro`: the licensed major's membership in `{pt}`
carries no information, so the uniform fire's law is false); for
*parameters* on the modeled route it needs parameter-independence of
the `_model` constructor values — a set-level fact about model bodies
with no Lean-typed spelling, which the public-interface-only ruling
forbids.  Only the tuple-tower route could fire uniformly (its values
ignore parameters by construction); a route-keyed uniform fire is the
option once that route owns recursive and multi-constructor families.
Stake: ≤ 0.8 % of init-full instructions. -/
inductive RecRuleFire where
  | inert
  | plain
  | nested (lvls : List Level) (pins : List Expr)
  deriving DecidableEq, Repr, Inhabited

/-- One iota rule of a recursor: applying the recursor (with its
parameters, motives and minors) to a `ctor`-headed major premise reduces
to `rhs` applied to the parameters, motives, minors and the constructor's
`nfields` fields.  `ctorParams` (the constructor's parameter count) and
`fire` (the canonical/nested/inert firing mode), and the two rescue
bits `k`/`eta` are *computed at install* from the stored constructor,
its inductive's capabilities and the recursor type — input rules carry
the parse placeholders `0`/`.inert`/`false`; reduction reads only the
installed values, never re-deriving them per fire. -/
structure RecRule where
  ctor : Name
  nfields : Nat
  /-- The constructor's parameter count (install-computed; parse
  placeholder `0`). -/
  ctorParams : Nat
  /-- The firing mode (install-computed, parse placeholder `.inert`):
  `.plain` for canonical rules (`Expr.recRulePlain`), `.nested` for
  certified nested-auxiliary rules, `.inert` otherwise. -/
  fire : RecRuleFire
  rhs : Expr
  /-- **The K bit** (install-computed, parse placeholder `false`;
  official `recursor_val::is_k`): this rule is its recursor's only
  one, its constructor has no fields, and that constructor's
  inductive is stored with the K capability — the standing condition
  of `majorToCtor`'s K rescue, decided once at the block's install
  instead of at every recursor application. -/
  k : Bool := false
  /-- **The η-rescue bit** (install-computed, parse placeholder
  `false`): this rule is its recursor's only one, its constructor is
  the η constructor of a stored η-capable inductive, and the recursor
  is not itself a projection function (whose rescue would loop) — the
  standing condition of `majorToCtor`'s structure-η rescue. -/
  eta : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- Reducibility hint of a definition, mirroring Lean's
`ReducibilityHints`: `abbrev` unfolds first, `opaque` last, `regular`
definitions compare by their definitional height.  The hints steer only
the *order* of lazy delta unfolding in `isDefEq` — never whether two
terms are definitionally equal — so the model and all soundness proofs
are independent of them. -/
inductive ReducibilityHint where
  | «opaque»
  | «abbrev»
  | regular (height : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace ReducibilityHint

/-- `h₁.lt h₂`: `h₁` is strictly less eager to unfold than `h₂` (the
lazy delta step unfolds the greater side to bring the two closer;
`opaque < regular h < abbrev`, regular heights compare by `<`). -/
def lt : ReducibilityHint → ReducibilityHint → Bool
  | _, .opaque => false
  | .abbrev, _ => false
  | .opaque, _ => true
  | _, .abbrev => true
  | .regular h₁, .regular h₂ => h₁ < h₂

/-- Both hints are `regular` at the *same* height — the only situation
in which the reference kernels (nanoda `try_eq_const_app`, the official
kernel) attempt the same-head congruence short-circuit instead of
unfolding.  Deliberately NOT generalized to other equal hints: proof
authors rely on `abbrev` definitions unfolding eagerly, and trying
spine defeq first on `abbrev`-headed applications risks reduction bombs
(spines that are only equal after reduction, retried at every
congruence level). -/
def sameRegular : ReducibilityHint → ReducibilityHint → Bool
  | .regular h₁, .regular h₂ => h₁ == h₂
  | _, _ => false

end ReducibilityHint

/-- The trusted basis inductives (hand-written set models; a modelled
block's `_model` family is built over these). -/
inductive BasisKind where
  | eqK | natK | punitK | emptyK | falseK | quotK
  deriving DecidableEq, Repr, Inhabited


/-- Definitional capabilities of a stored inductive type, recorded at
install: structural eta for its (single-constructor) values, unit-like
collapse (all inhabitants definitionally equal), and rule K for its
recursor.  The pinned basis blocks carry pinned capabilities; modeled
blocks earn them from checked `_model` theorems. -/
structure IndCaps where
  eta : Bool := false
  /-- The single constructor the eta law reconstructs through
  (meaningful only when `eta`). -/
  etaCtor : Name := .anonymous
  /-- Its parameter count (meaningful only when `eta`). -/
  etaParams : Nat := 0
  /-- Its field count (meaningful only when `eta`). -/
  etaFields : Nat := 0
  unitlike : Bool := false
  /-- The parameter count of the unit-like family (meaningful only
  when `unitlike`). -/
  unitParams : Nat := 0
  ruleK : Bool := false
  deriving DecidableEq, Repr, Inhabited

/-- **One structure's projection table** (task #175 S1, 2026-09-06):
everything the checker's `.proj` rules consume about a structure `T`,
stored once at the structure's install as ONE constant (keyed on the
structure: `projTableName structName`; see `Env.findProj?`).

A table is installed by the direct simple-structure install alone.
The `.proj T i` node is first-class — typed by `bodies[i]`, the
field's result-type **body** `F_i[p⃗ ↦ bvars, f_j ↦ .proj T j (bvar
0)]`, scoped at `numParams + 1` (the parameters and the subject are
loose `bvar`s, the subject at `bvar 0`, the earlier fields already
spelled as projections of the subject), instantiated at a use by ONE
`instantiateList` along the subject type's arguments and the subject
(`ProjEntry.typeAt`); reduced by the generic structural rule `proj_i
(ctor p⃗ x⃗) ↦ x_i`, guarded at possibly-Prop instances by the stored
`guards[i]`/`structSort` levels.  The bodies are taken from the
annotated constructor type by substitution alone (`structProjBodies`)
— no annotate, no infer, no pins: a slot with no legal instantiation
simply fails the guard at every use.

**Table-kind flag retired** (task #175 tower-flag, 2026-09-06): the
modeled route installs no table at all — a family without a table IS
a modeled one, and `findProj? = none` already says so at every
`.proj` site.  So *every* stored table carries bodies, types its
nodes and fires its rule, and the projection typing and iota laws
hold uniformly over every entry of every stored table. -/
structure ProjTable where
  structName : Name
  /-- the parent type former's level parameters -/
  levelParams : List Name
  /-- the parent's parameter count -/
  numParams : Nat
  /-- the single constructor (the structural rule's head) -/
  ctor : Name
  /-- its field count -/
  numFields : Nat
  /-- the parent's result sort -/
  structSort : Level
  /-- per field, the projection's result-type body (see above) -/
  bodies : Array Expr
  /-- per field, **the projection's `Prop` guard level**: the
  projected field's sort joined with the sorts of the earlier fields
  that a later field's type uses — exactly the sorts the official
  `infer_proj` requires to be `Prop` when projecting from a
  propositional structure (task #175 W4c/O4, `structProjGuards`); the
  infer branch checks it at every use of a `Prop`-declared
  structure. -/
  guards : List Level
  /-- **The projection offset** (task #210 Part A): the position of
  field `0` in the carrier's pair chain — `0` at a bare tuple tower
  (the direct structure route's carrier, `mkTower fs`), `1` at the
  TAGGED tower of the fixpoint route (`inj 0 (mkTower (fs ++ [pt]))`,
  the tag in front), so that the model reads `.proj T i` as
  `projS (i + off)`.  Syntactic to the kernel: the typing, iota and
  eta rules never look at it. -/
  off : Nat
  deriving DecidableEq, Repr, Inhabited

/-- **One projection-table entry** — the per-field VIEW of a
`ProjTable` (`ProjTable.entry`), what `Env.findProj? T i` returns:
the table's data at field `idx`.  `body` is `bodies[idx]` and
`fieldSort` is `guards[idx]`. -/
structure ProjEntry where
  structName : Name
  idx : Nat
  levelParams : List Name
  numParams : Nat
  ctor : Name
  numFields : Nat
  /-- the projection's result-type body, scoped at `numParams + 1`
  (see `ProjTable.bodies`) -/
  body : Expr
  /-- the projection's `Prop` guard level (see `ProjTable.guards`) -/
  fieldSort : Level
  structSort : Level
  /-- the table's projection offset (see `ProjTable.off`) -/
  off : Nat
  deriving DecidableEq, Repr, Inhabited

/-- The per-field view of a table at field `i` (meaningful for `i <
numFields`). -/
def ProjTable.entry (tbl : ProjTable) (i : Nat) : ProjEntry :=
  ⟨tbl.structName, i, tbl.levelParams, tbl.numParams, tbl.ctor, tbl.numFields,
    tbl.bodies.getD i default, tbl.guards.getD i .zero, tbl.structSort, tbl.off⟩

/-- Information stored about an accepted constant. -/
inductive ConstantInfo where
  | axiomInfo (val : ConstantVal)
  | defnInfo (val : ConstantVal) (value : Expr) (hint : ReducibilityHint)
  | thmInfo (val : ConstantVal) (value : Expr)
  /-- An inductive type former (whnf-stuck) with its capabilities. -/
  | indInfo (val : ConstantVal) (caps : IndCaps)
  /-- A basis constructor (whnf-stuck; the iota target). -/
  | ctorInfo (val : ConstantVal) (numParams numFields : Nat)
  /-- A basis recursor with its iota rules.  Only the two sums the
  firing path reads are stored: `majorIdx` (= numParams + numMotives +
  numMinors + numIndices, the major premise's argument position) and
  `rulePrefix` (= numParams + numMotives + numMinors, the length of the
  argument prefix a rule's rhs is applied to).  The individual counts
  are consumed at install time only and are not stored. -/
  | recInfo (val : ConstantVal) (majorIdx rulePrefix : Nat)
      (rules : List RecRule)
  /-- A structure's projection table (see `ProjTable`), stored under
  the reserved name `projTableName tbl.structName` so lookups,
  freshness and environment extension are uniform with constants.  Its
  `toConstantVal` carries the closed dummy type `Sort 1` (the table is
  not a term: no `.const` names it, `inferTypeCore` rejects one), so
  the environment well-formedness and model machinery cover the
  constant uniformly; the bodies' own well-formedness is `EnvWF`'s
  table clause. -/
  | projInfo (tbl : ProjTable)
  deriving DecidableEq, Repr, Inhabited

/-- A declaration presented to the checker. -/
inductive Declaration where
  | axiomDecl (val : ConstantVal)
  | defnDecl (val : ConstantVal) (value : Expr) (hint : ReducibilityHint)
  | thmDecl (val : ConstantVal) (value : Expr)
  /-- An `opaque` declaration: exactly a theorem check without the
  is-a-proposition requirement — the value is checked against the
  type as a realizability witness and then discarded (stored as an
  `axiomInfo`): the constant is never delta-unfolded, matching the
  official kernel's `is_delta`, which unfolds theorems but never
  opaques. -/
  | opaqueDecl (val : ConstantVal) (value : Expr)
  | basisDecl (kind : BasisKind)
  /-- An inductive block: type formers, constructors and recursors,
  with **the parameter count the stream DECLARES** (task #228).
  Installed by a direct route, or — the modeled route — opaquely
  after checking each member against its `_model` counterpart.

  The count is official's own declaration shape: `add_inductive`
  takes `Declaration.inductDecl lparams nparams types` with ONE
  `nparams` for the whole block (the replay reads it off an inductive
  record's `numParams` field, `Lean4Checker/Replay.lean`), checks
  every former and every constructor against it and generates the
  recursor with it.  It is checked here by `indParamsOk` and used as
  the block's parameter count by both routes — before task #228 the
  count was read OFF the constructors, which agrees on every valid
  stream and cannot see a declaration that lies. -/
  | indDecl (block : List ConstantInfo) (numParams : Nat)
  deriving DecidableEq, Repr, Inhabited

namespace Declaration

/-- The name of a non-basis declaration (basis blocks install several). -/
def name : Declaration → Name
  | .axiomDecl v | .defnDecl v _ _ | .thmDecl v _ | .opaqueDecl v _ => v.name
  | .basisDecl _ | .indDecl _ _ => .anonymous

end Declaration

/-- **The length of a syntactic Π-telescope ending in a SORT**:
`some n` when the expression is `n` Π binders with a `.sort`
residual, `none` when the residual is anything else — a constant that
only *unfolds* to a telescope, say (task #195).  A spine walk: one
child per step, never a tree.

The distinction is what makes `indParamsOk` one-sided.  Official's
telescope loop (`check_inductive_types`, `inductive.cpp`) reduces the
residual to weak head normal form before every binder; at a `.sort`
residual that reduction is the identity and no further binder can
appear, so `n` is exactly the number of binders official counts. -/
def Expr.piSortTeleLen? : Expr → Option Nat
  | .forallE _ body _ => (Expr.piSortTeleLen? body).map (· + 1)
  | .sort _ => some 0
  | _ => none

/-- **The stream's declared parameter count, checked as official
checks it** (task #228).  Official trusts the count the declaration
carries and checks the block AGAINST it, in two places:

* `check_inductive_types` peels `nparams` Π binders off every type
  former, reducing to weak head normal form before each, and throws
  *"number of parameters mismatch in inductive datatype declaration"*
  when the telescope runs out first;
* the replay compares every exported constructor record with the one
  the kernel GENERATES, whose `numParams` field is `nparams`, so a
  constructor record declaring a different count is *"Invalid
  constructor"* (`checkPostponedConstructors`).

Both halves are below, and both are ONE-SIDED on purpose: `false`
means official rejects, never merely that this checker cannot see
why.  A former whose declared type is a Π-telescope ending in a sort
and shorter than `nP` is one official cannot peel `nP` binders off
(`Expr.piSortTeleLen?`); a former with any other residual may still
unfold to a longer telescope and is left to the install stages, which
peel it with `whnf` exactly as official does (`whnfTelescope`).

The exported `numIndices` is deliberately NOT checked: nothing ever
compares an inductive record against the generated `InductiveVal`
(only constructors and recursors are postponed and compared), so a
declared index count is not input official reads, and checking it
would reject blocks official accepts. -/
def indParamsOk (nP : Nat) (block : List ConstantInfo) : Bool :=
  block.all fun ci => match ci with
    | .indInfo cvT _ =>
      match cvT.type.piSortTeleLen? with
      | some n => decide (nP ≤ n)
      | none => true
    | .ctorInfo _ nPc _ => nPc == nP
    | _ => true

/-- The public projection-*function* name for field `i` of structure
`T` — the modeled path's degenerate-recursor projection functions
(`checkProjFn`; a `Nat` component keeps it out of the way of exported
identifiers; installs are duplicate-checked regardless).  Since task
#175 S1 no table entry lives under this name: the direct install's
table is one constant per structure, `projTableName`. -/
def projFnName (T : Name) (i : Nat) : Name := (T.str "proj").num i

/-- The reserved name of structure `T`'s projection table (task #175
S1): one constant per structure, a `Nat` component keeping it out of
the way of exported identifiers (the front door rejects the shape,
`Name.isProjFnShape`), distinct from every `projFnName` name. -/
def projTableName (T : Name) : Name := (T.str "projTable").num 0

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v _ => v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => v
  | .projInfo tbl => ⟨projTableName tbl.structName, tbl.levelParams, .sort (.succ .zero)⟩

def name (c : ConstantInfo) : Name := c.toConstantVal.name

/-- A projection table (task #175 W4c): a table, not a term — no
`.const` node names it (`inferTypeCore` rejects one), so the model
owes it no leaf. -/
def isTowerEntry : ConstantInfo → Bool
  | .projInfo _ => true
  | _ => false

def type (c : ConstantInfo) : Expr := c.toConstantVal.type

end ConstantInfo

/-- The global environment: the list of constants accepted so far, newest
first.  Names are unique (the checker rejects duplicates), so the order is
irrelevant for lookup. -/
structure Env where
  consts : List ConstantInfo
  deriving Repr, Inhabited

namespace Env

/-- The empty environment; the starting point of every checker run. -/
def empty : Env := ⟨[]⟩

def find? (env : Env) (n : Name) : Option ConstantInfo :=
  env.consts.find? (·.name == n)

/-- Look up the projection-table entry for field `i` of `T`: the
structure's table (`projTableName T`), viewed at field `i` (task #175
S1; `none` beyond the table's field count). -/
def findProj? (env : Env) (T : Name) (i : Nat) : Option ProjEntry :=
  match env.find? (projTableName T) with
  | some (.projInfo tbl) => if i < tbl.numFields then some (tbl.entry i) else none
  | _ => none

end Env

end ConLeche
