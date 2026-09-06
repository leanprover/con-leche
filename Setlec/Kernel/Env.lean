import Setlec.Kernel.Expr

/-!
# Declarations and the global environment

Input declarations mirror `Lean.Declaration` (only the kinds the checker
supports so far are present; more are added feature by feature).

The environment is, for now, a simple association list of checked constants.
This is the *verified* reference representation; a faster indexed structure
can replace it later, with a proof that it refines this one.
-/

namespace Setlec

/-- **The checker's mode setting** — two values since the R core's
retirement (2026-09-05), validated once at startup and threaded as
configuration, never re-read at runtime (the `directStructsEnabled`
discipline).

* `.verified` (the default, `--verified`): the verified lane.  The
  surface the **graded** set-theoretic
  model proves — `no_proof_of_Empty_SPCD_P`
  (`Setlec/Verify/Cached/MainC.lean`) is its letter over the driver
  this binary runs.  The seven TT-lane checks (tasks #126, #129, #130,
  #135, #136, #137, #146) are off; the β-certificate gate is on — at a
  λ-binder whose **validated** annotation is `.never` the per-redex
  argument certificate is skipped (`betaTest`,
  `Setlec/Kernel/Core.lean`) — and the io-graded knot slot skips the
  per-argument application certificate under the same licence.  Every
  other certificate family runs unconditionally.
* `.trusted` (`--trusted`): the unverified lane — the same checker
  with the work that exists **for certification only** omitted.
  What must not be dropped is everything believed necessary for
  *soundness* (which is different from "necessary for our soundness
  proof to go through"), so the lane is never optimized on its own:
  it is the real mode with certain steps omitted (DESIGN.md, "MODE
  RENAME").  Since 2026-09-06 it is literally that: the one cached
  driver at `cfgT` — `cfgP` with `verified := false` and `certs :=
  false` (`Setlec/Kernel/CoreCfg.lean`), so what it omits is exactly
  what `cfg.verified` and `cfg.certs` gate in
  `Setlec/Cached/CoreC.lean` (DESIGN.md, "CORET RETIRED").
  `Main.lean` maps the mode to the config; the cached tier never sees
  a `CheckMode` except through the inert `CoreCfg.iotaMode`.

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
is a premise of the set lane's annotation pass (`Setlec/SetP`), so it
must run at `.verified`; and it is a check the reference kernel's
`infer_lambda` does not run, so it must not run at `.trusted`. -/
def CheckMode.verifiedChecks : CheckMode → Bool
  | .trusted => false
  | _ => true

/-- Is the **β-certificate gate** on (task #161)?  The third accessor
the kernel branches on: at a λ-binder whose validated annotation datum
is `.never` the per-redex argument certificate is skipped (`betaTest`,
`Setlec/Kernel/Core.lean`).

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
(`RecRuleLawP`) at the recursor's own parameters, and the P lane has no
typing derivation in hand: the redex is only `AnnotOkP`, and since the
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
`fire` (the canonical/nested/inert firing mode) are *computed at
install* from the stored constructor and recursor type — input rules
carry the parse placeholders `0`/`.inert`; reduction reads only the
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

/-- The trusted basis inductives (hand-written set models; everything
else is reduced to these by the lean-inductive-models preprocessor). -/
inductive BasisKind where
  | eqK | natK | punitK | emptyK | quotK
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
annotated constructor type by substitution alone (`directProjBodies`)
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
  propositional structure (task #175 W4c/O4, `directProjGuards`); the
  infer branch checks it at every use of a `Prop`-declared
  structure. -/
  guards : List Level
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
  deriving DecidableEq, Repr, Inhabited

/-- The per-field view of a table at field `i` (meaningful for `i <
numFields`). -/
def ProjTable.entry (tbl : ProjTable) (i : Nat) : ProjEntry :=
  ⟨tbl.structName, i, tbl.levelParams, tbl.numParams, tbl.ctor, tbl.numFields,
    tbl.bodies.getD i default, tbl.guards.getD i .zero, tbl.structSort⟩

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
  /-- A preprocessed (modeled) inductive block: type formers,
  constructors and recursors, installed opaquely after checking each
  member against its `_model` counterpart. -/
  | indDecl (block : List ConstantInfo)
  deriving DecidableEq, Repr, Inhabited

namespace Declaration

/-- The name of a non-basis declaration (basis blocks install several). -/
def name : Declaration → Name
  | .axiomDecl v | .defnDecl v _ _ | .thmDecl v _ | .opaqueDecl v _ => v.name
  | .basisDecl _ | .indDecl _ => .anonymous

end Declaration

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

/-- The index count of a recursor (majorIdx − rulePrefix; junk
elsewhere). -/
def recNi : ConstantInfo → Nat
  | .recInfo _ mI rP _ => mI - rP
  | _ => 0

/-- The iota rules of a recursor (junk elsewhere). -/
def recRules : ConstantInfo → List RecRule
  | .recInfo _ _ _ rs => rs
  | _ => []

/-- The parameter count of a constructor (junk elsewhere). -/
def ctorNP : ConstantInfo → Nat
  | .ctorInfo _ nP _ => nP
  | _ => 0

/-- The field count of a constructor (junk elsewhere). -/
def ctorNF : ConstantInfo → Nat
  | .ctorInfo _ _ nF => nF
  | _ => 0

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

end Setlec
