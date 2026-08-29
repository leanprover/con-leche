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

/-- The checker's mode setting (task #147; two modes since the
declarative lane's retirement at task #148 T7b), validated once at
startup and threaded as configuration — never re-read at runtime (the
`directStructsEnabled` discipline).

* `.setModel` (the default, `--set-model`): the surface the
  set-theoretic model proves.  The seven TT-lane checks (tasks #126,
  #129, #130, #135, #136, #137, #146) are **off**; every always-on
  certificate family (per-redex beta, per-argument application,
  proof-irrelevance chains, `etaCert`, `iotaCerts`, `projCert`) keeps
  running.
* `.noModel` (`--no-model`): the unverified lane — full front-door
  check per declaration (official-kernel parity), infer-only internal
  discipline (task #134), and **no certificate families at all**
  (task #76).  Selected by a different driver stack
  (`Setlec/Kernel/CheckerNM.lean`). -/
inductive CheckMode where
  | setModel
  | noModel
  deriving DecidableEq, Repr, Inhabited

/-- Are the seven TT-lane checks enabled?  The one accessor the kernel
branches on — **constantly `false` since task #148 T7b**, when the
declarative verification lane and its `.ttModel` mode were retired
together.  The gated call sites are kept, statically unreachable, so
that the checks themselves survive as reviewed code and the accessor
stays the single place a future lane would turn them back on. -/
def CheckMode.ttChecks : CheckMode → Bool
  | _ => false

/-- Are the *verified* modes' extra checks enabled — the checks both
model lanes want and the unverified lane must not run, because it is
the official-parity lane?  The second accessor the kernel branches on
(task #152: the λ-rule's codomain-sort check, `inferBody`'s `.lam`
clause).  This is deliberately **not** `ttChecks`: the λ codomain sort
is a premise of the *set* lane's annotation pass (`Setlec/SetR`), so it
must run at `.setModel` too; and it is a check the reference kernel's
`infer_lambda` does not run, so it must not run at `.noModel`. -/
def CheckMode.verified : CheckMode → Bool
  | .noModel => false
  | _ => true

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
  decline in `iotaRec` (an uncertified nested auxiliary rule). -/
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
  | eqK | natK | psigmaK | punitK | emptyK | quotK
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

/-- One projection-table entry, keyed by (type former × field index):
everything the checker's `.proj` rules consume, stored once at install
(the key is encoded in the entry's stored *name*, `projFnName
structName idx`; see `Env.findProj?`).

* `native = true`: the `.proj` node is first-class — typed by the
  level-parametric `ty` (`∀ p⃗ (t : T p⃗), F_i`, earlier fields spelled
  as `.proj` nodes of the subject) and reduced by the generic
  structural rule `proj_i (ctor p⃗ x⃗) ↦ x_i`, guarded at possibly-Prop
  instances by the stored `fieldSort`/`structSort` levels.  Installed
  by the pinned `PSigma'` basis block.
* `native = false`: the Prop-structure elimination-template entry —
  per-declaration shape facts for the permanent recursor-inlining
  fallback (`annotateProjRec`), whose per-instantiation typing check
  remains at use; `ty` is the closed junk `Prop` and
  `fieldSort`/`structSort` are unused. -/
structure ProjEntry where
  structName : Name
  idx : Nat
  /-- the parent type former's level parameters -/
  levelParams : List Name
  /-- the parent's parameter count -/
  numParams : Nat
  /-- the single constructor (the structural rule's head) -/
  ctor : Name
  /-- its field count -/
  numFields : Nat
  /-- the projection's level-parametric type (native entries only) -/
  ty : Expr
  /-- the projected field's sort (native entries only) -/
  fieldSort : Level
  /-- the parent's result sort (native entries only) -/
  structSort : Level
  native : Bool
  /-- the parent's recursor carries a motive-sort level parameter in
  front of the parent's own (template entries only) -/
  recExtraLevel : Bool
  deriving DecidableEq, Repr, Inhabited

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
  /-- A projection-table entry (see `ProjEntry`), stored under the
  reserved name `projFnName entry.structName entry.idx` so lookups,
  freshness and environment extension are uniform with constants.  Its
  `toConstantVal` carries the entry's projection type (`ty`; template
  entries carry the closed junk `Prop` there), so the environment
  well-formedness and model machinery cover the entry uniformly. -/
  | projInfo (entry : ProjEntry)
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

/-- The public projection-table name for field `i` of structure `T` (a
`Nat` component keeps it out of the way of exported identifiers;
installs are duplicate-checked regardless). -/
def projFnName (T : Name) (i : Nat) : Name := (T.str "proj").num i

namespace ConstantInfo

def toConstantVal : ConstantInfo → ConstantVal
  | .axiomInfo v | .defnInfo v _ _ | .thmInfo v _ => v
  | .indInfo v _ | .ctorInfo v _ _ | .recInfo v _ _ _ => v
  | .projInfo e => ⟨projFnName e.structName e.idx, e.levelParams, e.ty⟩

def name (c : ConstantInfo) : Name := c.toConstantVal.name

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

/-- Look up the projection-table entry for field `i` of `T`. -/
def findProj? (env : Env) (T : Name) (i : Nat) : Option ProjEntry :=
  match env.find? (projFnName T i) with
  | some (.projInfo e) => some e
  | _ => none

end Env

end Setlec
