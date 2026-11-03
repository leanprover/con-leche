module

public import ConLeche.Kernel.Expr
public import ConLeche.Kernel.PropWhen

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

/-- **The checker's mode setting** — two values, validated once at
startup and threaded as configuration, never re-read at runtime.

* `.verified` (the default, `--verified`): the verified lane.  The
  surface the **graded** set-theoretic
  model proves — `no_proof_of_Empty_cached`
  (`ConLeche/Verify/Cached/MainC.lean`) is its letter over the driver
  this binary runs.  The seven TT-lane checks (tasks #126, #129, #130,
  #135, #136, #137, #146) are off; the λ and η checks (task #342) run,
  and every certificate family runs.
* `.trusted` (`--trusted`): the unverified lane — the same checker
  with the work that exists **for certification only** omitted.
  What must not be dropped is everything believed necessary for
  *soundness* (which is different from "necessary for our soundness
  proof to go through"), so the lane is never optimized on its own:
  it is the real mode with certain steps omitted (DESIGN.md, "MODE
  RENAME").  Since 2026-09-06 it is literally that: the one cached
  driver (`ConLeche/Cached/ParsedC.lean`) at `.trusted`, where
  `verifiedChecks` is `false` — so what it omits is exactly what that
  function gates in `ConLeche/Cached/CoreC.lean` (DESIGN.md, "CORET
  RETIRED").

**The mode is the cores' only parameter** (task #185, 2026-09-06).
The configuration record that stood between the mode and the
shipped cores from task #172 B2 to task #185 is gone: what it
carried is the function `verifiedChecks` below, a `match` on the two
constructors, so each read reduces by `rfl` at either mode — the
record's `rfl`-eliminability argument, at the enum itself.

The two values are spelled `--verified` and `--trusted` on the command
line, and they say what the modes are FOR rather than which artefact
proves them.

**The eager variants** (task #353): `.verifiedEager` and `.trustedEager`
are the two modes with the official kernel's `m_eager_reduce` flag set
— the knot's *eager tower* (`CoreFns.defeqE`, `coreKnot`), which runs
the comparison of an `eagerReduce _ _` argument's type with its
domain and everything beneath it.  The flag is read at two places of
definitional equality (`CheckMode.eager`: the `Bool.true` shortcut and
the lazy-delta literal fold fire with free variables present), and
`verifiedChecks` is the base mode's.  No command line selects them. -/
inductive CheckMode where
  | verified
  | trusted
  | verifiedEager
  | trustedEager
  deriving DecidableEq, Repr, Inhabited

/-- Are the *verified* mode's extra checks enabled — the work the
model lane needs and the trusted lane must not run, because it is
needed for the soundness *proof* rather than for soundness, and the
reference kernel does not do it?  Two kinds of work read it:

* checks the rules tier's premises rest on (`ConLeche/Rules`): the
  λ-rule's codomain-sort check (`inferBody`'s `.lam` clause), the η
  body-type comparison and the λ/λ body-type comparison of
  `defeqLams`.  The mode-parametric spec (`ConLeche/Kernel/Core.lean`)
  reads it at the same sites the cached core does.
* the certificate families, which the spec runs unconditionally: the
  K and `And` rescues' proof-irrelevance run, ι's case-3 parameter
  comparison and its case-3 telescope and index certificates.  The
  cached core reads them through `certAtI`
  (`ConLeche/Cached/CoreC.lean`); the simulation tower
  (`ConLeche/Verify/Cached/*`), stated under
  `hμ : mode.verifiedChecks = true`, sees through them.  The `.trusted`
  instance of the cached-vs-spec simulation is false, deliberately: the
  trusted core skips what the spec runs. -/
def CheckMode.verifiedChecks : CheckMode → Bool
  | .trusted => false
  | .trustedEager => false
  | _ => true

/-- **Is this the `--verified` mode itself** — `.verified`, not its eager
tower (task #353)?  The model tier (`ConLeche/Model/*`) is stated at
the top-level mode a run is started in, under `hμ : μ.isVerified = true`
(`CheckMode.eq_verified`); the simulation tower and the bridges, which
also run inside the eager tower, are stated under the weaker
`verifiedChecks`. -/
def CheckMode.isVerified : CheckMode → Bool
  | .verified => true
  | _ => false

/-- The official kernel's `m_eager_reduce` flag (task #353): set while
an `eagerReduce _ _` argument's type is compared with its domain
(official `infer_app`, `type_checker.cpp`), for that comparison and
everything it calls.  Read by `defeqBody` (the `Bool.true` shortcut
ignores free variables) and `lazyDeltaReduction` (the Nat-literal
fold ignores free variables). -/
@[inline] def CheckMode.eager : CheckMode → Bool
  | .verifiedEager => true
  | .trustedEager => true
  | _ => false

/-- The mode with the eager flag set: the eager tower's mode
(`coreKnot`'s `defeqE` slot). -/
def CheckMode.toEager : CheckMode → CheckMode
  | .verified => .verifiedEager
  | .trusted => .trustedEager
  | m => m

/-- Data common to all constants: name, universe parameters, type. -/
structure ConstantVal where
  name : Name
  levelParams : List Name
  type : Expr
  deriving DecidableEq, Repr, Inhabited

/-- How a stored recursor rule fires (install-computed; parse
placeholder `.plain`).  The official kernel fires a rule by constructor
name and field count and compares nothing; the fire here compares what
the rule's law (`RecRuleLaw`) is stated at, and only at a case-3 redex
(`iotaCase3`: not K, and the family may be `Prop` at the comparand
levels): the levels, the parameters and the indices.  There the
constructor application may be the point, and at a `Prop` valuation
nothing else ties the constructor's levels and parameters to the
comparands; elsewhere the major's membership in the family at the
comparands ties its fields, and the law reads nothing else of the
constructor's levels or parameters.

* `.plain` — the installer's rule at a member major: the comparands
  are the recursor's own instantiation and leading arguments (the
  constructor's levels are the recursor's, by name, and its parameters
  the recursor's leading arguments).
* `.nested lvls pins` — an auxiliary recursor's rule at an outside
  major (a nested block): the comparands are fixed instantiations,
  the class's levels and parameters the generated recursor type's major
  domain applies the container to (`auxRuleFire`) — `lvls` are levels
  over the recursor's level parameters, `pins` expressions in the
  recursor's rule-prefix context, instantiated at the redex's levels and
  leading arguments. -/
inductive RecRuleFire where
  | plain
  | nested (lvls : List Level) (pins : List Expr)
  deriving DecidableEq, Repr, Inhabited

/-- One iota rule of a recursor: applying the recursor (with its
parameters, motives and minors) to a `ctor`-headed major premise reduces
to `rhs` applied to the parameters, motives, minors and the constructor's
`nfields` fields.  `ctorParams` (the constructor's parameter count) and
`fire` (the plain/nested firing mode) and the two rescue
bits `k`/`eta` are *computed at install* from the stored constructor,
its inductive's capabilities and the recursor type — input rules carry
the parse placeholders `0`/`.plain`/`false`; reduction reads only the
installed values, never re-deriving them per fire. -/
structure RecRule where
  ctor : Name
  nfields : Nat
  /-- The constructor's parameter count (install-computed; parse
  placeholder `0`). -/
  ctorParams : Nat
  /-- The firing mode (install-computed, parse placeholder `.plain`):
  `.plain` at a member major, `.nested` at an outside one. -/
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
  `false`): this rule is its recursor's only one and its constructor
  is the η constructor of a stored η-capable inductive — the standing
  condition of `majorToCtor`'s structure-η rescue. -/
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

/-- The trusted basis inductives (hand-written set models). -/
inductive BasisKind where
  | eqK | natK | emptyK | falseK | quotK
  deriving DecidableEq, Repr, Inhabited

/-- Definitional capabilities of a stored inductive type, recorded at
install: structural eta for its (single-constructor) values, unit-like
collapse (all inhabitants definitionally equal), and rule K for its
recursor.  The pinned basis blocks carry pinned capabilities. -/
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
  /-- **The family's result-sort zero-ness datum** (install-computed
  from the stored type; the default `ifAllZero []` reads
  "zero at every valuation", which no rescue passes).  The structure-η
  rescue fires only where the official kernel's `is_never_zero` holds
  of the *instantiated* result sort, and this datum decides that at a
  use by one level substitution (`capsNeverZero`) instead of a walk
  down the family's type at every rescue. -/
  sortZ : PropWhen := .ifAllZero []
  /-- **The block's members** (official's `all`): the formers installed
  together with this one, in block
  order, itself included.  Read by nested positivity alone — a container
  frame's restart (`nestFrame`) abstracts only group-mates listed here,
  so an accepted frame's holes are members of ONE recorded block (a pinned
  basis type records `[T]`, as official does; `Quot` alone keeps `[]`). -/
  all : List Name := []
  /-- **The family's parameter count** (official's `inductive_val.nparams`):
  the block's declared parameter count, recorded at every install
  (uniform: `BlockShape.nP`; basis: the pin's).  Read by nested positivity
  alone, and only for a
  container WITHOUT constructors (`nestContainer`), whose parameter count
  no constructor record carries. -/
  nparams : Nat := 0
  /-- **The family's constructors, in declaration order** (official's
  `inductive_val.cnstrs`): recorded at install (uniform: the member's
  constructors; basis: the pin's).  Read by nested positivity alone
  (`nestContainer`): a container's constructors are looked up by name,
  never by a scan of the environment.  `Quot` records none (it is no
  container). -/
  ctors : List Name := []
  deriving DecidableEq, Repr, Inhabited

/-- **One structure's projection table** (task #175 S1, 2026-09-06):
everything the checker's `.proj` rules consume about a structure `T`,
stored once at the structure's install in the environment's table
component (`Env.tables`, keyed on the structure's name: `Env.findTable?`,
`Env.findProj?`; task #362).

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
stored constructor type by substitution alone (`structProjBodies`)
— no inference, no pins: a slot with no legal instantiation
simply fails the guard at every use.

**No table kinds** (task #175 tower-flag): every stored table carries
bodies, types its nodes and fires its rule, and the projection typing and iota laws
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
  | thmInfo (val : ConstantVal)
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
  deriving DecidableEq, Repr, Inhabited

/-- **Which of the four quotient constants a `#QUOT` record declares**
(task #293): the `kind` field of the export record, decoded.  The
order is the pinned block's (`quotBasis`): `Quot`, `Quot.mk`,
`Quot.lift`, `Quot.ind`. -/
inductive QuotKind where
  | type | ctor | lift | ind
  /-- `Quot.sound`, which the export writes as an ordinary axiom record
  beside the four `#QUOT` ones: not a `kind` the decoder ever reads, but
  a slot of the pinned block, and the kind `preparePrelude` gives that
  record when it is not the pinned one. -/
  | sound
  deriving DecidableEq, Repr, Inhabited

/-- The quotient constant's position in the pinned block
(`BasisKind.quotK.decls`). -/
def QuotKind.slot : QuotKind → Nat
  | .type => 0 | .ctor => 1 | .lift => 2 | .ind => 3 | .sound => 4

/-- A declaration presented to the checker. -/
inductive Declaration where
  | axiomDecl (val : ConstantVal)
  | defnDecl (val : ConstantVal) (value : Expr) (hint : ReducibilityHint)
  | thmDecl (val : ConstantVal) (value : Expr)
  /-- An `opaque` declaration: exactly a theorem check without the
  is-a-proposition requirement — the value is checked against the
  type as a realizability witness and then discarded (stored as an
  `axiomInfo`): the constant is never delta-unfolded, as the official
  kernel's `is_delta` never unfolds an opaque.  (A theorem is the
  same here — stored by its statement, never unfolded — where
  official still unfolds theorems until
  https://github.com/leanprover/lean4/pull/14896.) -/
  | opaqueDecl (val : ConstantVal) (value : Expr)
  /-- **The fold's own record for "install the pinned basis block"**
  (task #293).  No frontend function produces one: the decoder emits
  the file's records, `preparePrelude` reorders them, and it is
  `checkDecl`'s `.indDecl` arm that RECOGNISES a block as one of the
  five pinned ones (`basisPinHit`, up to `ConstantInfo.canon`) and its
  `.quotDecl` arm that recognises the quotient package, both of which
  install through this kind.  It stays a constructor of `Declaration`
  because the install and every proof about it are written over the
  kind. -/
  | basisDecl (kind : BasisKind)
  /-- An inductive block: type formers, constructors and recursors,
  with **the parameter count the stream DECLARES** (task #228).
  Installed by the inductive installer (`checkBlock`).

  The count is official's own declaration shape: `add_inductive`
  takes `Declaration.inductDecl lparams nparams types` with ONE
  `nparams` for the whole block (the replay reads it off an inductive
  record's `numParams` field, `Lean4Checker/Replay.lean`), checks
  every former and every constructor against it and generates the
  recursor with it.  It is checked here by `indParamsOk` and used as
  the block's parameter count by the installer — before task #228 the
  count was read OFF the constructors, which agrees on every valid
  stream and cannot see a declaration that lies. -/
  | indDecl (block : List ConstantInfo) (numParams : Nat)
  /-- **A quotient declaration record, as the file declares it** (task
  #293).  `lean4export` writes the quotient package as four records —
  one per constant, each tagged with its `kind` — and the decoder emits
  one `quotDecl` per record: the constant the file declares and the
  slot it declares it at, and nothing else.  It mirrors official's
  `Declaration.quotDecl`, which is likewise the record's own kind and
  not a basis decision.

  What reaches the FOLD under this constructor is a quotient record
  that is **not** the pinned package: `preparePrelude`
  (`ConLeche/Frontend/Prepare.lean`) retags a record matching its pin
  to `basisDecl .quotK`, so `checkDecl`'s arm here is the mismatch —
  a positively detected unsupported feature, the decline the parser
  used to issue. -/
  | quotDecl (kind : QuotKind) (val : ConstantVal)
  deriving DecidableEq, Repr, Inhabited

namespace Declaration

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
  | .forallE _ body => (Expr.piSortTeleLen? body).map (· + 1)
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

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v => v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => v

def name (c : ConstantInfo) : Name := c.toConstantVal.name

end ConstantInfo

namespace Declaration

/-- **The names a declaration record declares**: the hoist's name index
and `preparePrelude`'s lookup of the stream's own copy of a prelude
declaration read it (`ConLeche/Frontend/{NatOpGround,Prepare}.lean`).
A quotient record declares the one constant it carries — the other
three constants of the pinned block are other records' — and a
`basisDecl`, which no frontend function produces (it is the fold's own
record for "install the pinned block"), declares the pin's. -/
def names : Declaration → List Name
  | .axiomDecl cv | .defnDecl cv .. | .thmDecl cv .. | .opaqueDecl cv .. => [cv.name]
  | .quotDecl _ cv => [cv.name]
  | .indDecl block _ => block.map (·.name)
  | .basisDecl _ => []

end Declaration

/-- The global environment: the constants accepted so far and the
structures' projection tables, each list newest first.  Names are
unique (the checker rejects duplicates), so the order is irrelevant for
lookup; so are the tables' structure names (a block installs a table
only for its own, fresh, structure-like members).

The tables are not constants (task #362): no `.const` names one, they
are read by `.proj` nodes alone, keyed on the structure's name
(`findTable?`). -/
structure Env where
  consts : List ConstantInfo
  tables : List ProjTable
  deriving Repr, Inhabited

namespace Env

/-- The empty environment; the starting point of every checker run. -/
def empty : Env := ⟨[], []⟩

def find? (env : Env) (n : Name) : Option ConstantInfo :=
  env.consts.find? (·.name == n)

/-- The projection table of structure `T`, visible where `T` is (a block
installs a table only for its own structures, so on every environment
the checker builds the gate passes exactly where a table is stored; it
makes a view that hides a structure hide its table, `FEnv.findTable?`). -/
def findTable? (env : Env) (T : Name) : Option ProjTable :=
  if (env.find? T).isSome then env.tables.find? (·.structName == T) else none

/-- Look up the projection-table entry for field `i` of `T`: the
structure's table, viewed at field `i` (task #175 S1; `none` beyond the
table's field count). -/
def findProj? (env : Env) (T : Name) (i : Nat) : Option ProjEntry :=
  match env.findTable? T with
  | some tbl => if i < tbl.numFields then some (tbl.entry i) else none
  | none => none

end Env

end ConLeche
