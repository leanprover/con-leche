module

public import ConLeche.Cached.Decls
public import ConLeche.Modular.Generic

@[expose] public section

/-!
# Modular checking: modules, keys, the local checks

The statement half of modular checking, in the style of `ConLeche/Denotes.lean`: definitions only,
importing the checker and nothing of the proof tiers.  The abstract argument is
`ConLeche/Modular/Generic.lean` (the whitepaper fragment's `ModularSemantics.lean`); what this file
adds is what a module is for con-leche and what its checks are.

* A **development** is a family of modules `dev : Nat → Module`, a module's imports earlier than it.
  A module has its own records (`decls`) and its **context** (`ctx`): the records it is checked
  against, each one a record an earlier module presents (`iface`).  The context's environment is
  what those records install (`Module.context`, `streamEnv`), its own environment the context with its
  own records installed (`Module.own`).  For every name the context stores, `src` is the module it is
  read from, and `key` says what identifies the name across modules.
* A **key** (`Key Stmt`) is the module that declared a constant (its **home**), or, for a proof, its
  statement: two proofs of one name and statement are one constant (the model gives every proof the
  point), whatever their bodies or homes.  No name is ever renamed, and there is no merged
  environment: two modules may declare one name and never be loaded together.
* A **presentation** (`Presents`) of an own record is a record that installs the same constants (in
  any order) and tables, or the record's statement (`stmtOf`): a definition, theorem or opaque constant as an axiom
  of its name, level parameters and type.  An inductive group is presented as its record, so it
  reaches an importer whole.
* A **proof** (`ProofDecl`) is a theorem record, a definition or opaque record whose value passes
  the theorem record's check at the environment it is installed at, or an axiom record whose type
  is inferred to be a proposition there (`TypeIsProp`): the copies Lean's own merge rule identifies
  (`subsumesInfo`, whose `isPropCheap` is a sufficient test of the same).

**The local checks** split by who runs them:
1. at the home, once (`InterfaceOk`): every presentation the module offers presents one of its own
   records;
2. at the importer (`ImportOk`): the imports and sources come earlier; the context stores each name
   once; every context record is read from one module and is a presentation of it; what a context
   record's constants read is stored in the context and read as that module reads it, under one key
   (`RecordScoped` over `readsAlike`); the own records are accepted from the context, one after
   another, each by the fold's own step (`DeclsRun`); a name flagged a proof is declared by a proof;
   and the keys are the sources' for context names and the module's own for its own names.

The context need not be everything the module loads: any part of it closed under what its records
read is a context in this sense, which is why a worker may check a module over the reach of its own
records.

**The statement these checks are for** (proved for con-leche's models by task #463):

```
theorem modular_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (dev : Nat → Modular.Module) (i : Nat)
    (hok : ∀ j ≤ i, Modular.LocalOk .verified pins dev j) :
    ∃ m : ∀ j ≤ i, Model V (dev j).own,
      (∀ j hj j' hj' n, ((dev j).own.find? n).isSome = true →
        ((dev j').own.find? n).isSome = true → (dev j).key n = (dev j').key n →
        (m j hj).cval n = (m j' hj').cval n) ∧
      ∀ j hj n s, ((dev j).own.find? n).isSome = true → (dev j).key n = .proof s →
        (m j hj).cval n = fun _ => pt
```

a compatible family of models of the own environments: two modules that store a name under one key
give it one value, and every proof the point.  Its corollary is that no own environment stores a
constant of type `False`.
-/

namespace ConLeche.Modular

open ConLeche.Cached

/-- **A proof's statement**: its level parameters and type. -/
abbrev Stmt := List Name × Expr

/-! ## Records and their presentations -/

/-- **The statement of a record**: a definition, theorem or opaque record as the axiom of its name,
level parameters and type; any other record itself. -/
def stmtOf : Declaration → Declaration
  | .defnDecl cv _ _ => .axiomDecl cv
  | .thmDecl cv _ => .axiomDecl cv
  | .opaqueDecl cv _ => .axiomDecl cv
  | d => d

/-- **A presentation of an own record**: a record installing the same constants, in any order,
and the same tables (a theorem record, whatever value it carries, installs its statement), or the
record's statement.  The order is free because a record installs its constants as a set, its
names distinct: an inductive group read from its home's exported part lists its recursors in that
part's order, which is sorted by name, where the home's own record lists them in declaration
order.  A record at a `reduce*` name is presented as itself: the compiler-trust axioms
(`ofReduceNat`, `ofReduceBool`) are accepted at an importer by that name's pinned statement, which
is true only of the identity its home's opaque install certified. -/
def Presents (e p : Declaration) : Prop :=
  ((declConstants e).Perm (declConstants p) ∧ declTables e = declTables p) ∨
    (e = stmtOf p ∧ ∀ n ∈ (declConstants p).map (·.toConstantVal.name), n ∉ reduceOpNames)

/-- The names a record installs. -/
def declNames (d : Declaration) : List Name :=
  (declConstants d).map (·.toConstantVal.name)

/-! ## What a record reads -/

/-- **The names a pinned constant's fast path reads**, beyond its own type and value: a certified
`Nat` operation's dependencies, the `Nat` basis and, for the `Bool`-valued and `ble`-guarded ones,
the `Bool` type and constructors; a `reduce*` opaque's element type. -/
def pinFootprint (n : Name) : List Name :=
  (if natOpNames.contains n || natDivModNames.contains n then
    natOpDeps n ++ [natName, natZeroName, natSuccName] ++
      (if n = natBeqName || n = natBleName || natDivModNames.contains n then
        [boolName, boolTrueName, boolFalseName] else [])
   else []) ++
  (if reduceOpNames.contains n then [reduceElemName n] else [])

/-- **What a constant's laws read is stored in `R`**: the constants of its type, a definition's
value, a recursor's rules (right-hand sides, nested pins, constructors), a type former's block
members and η constructor, and the names its fast path reads.  A projection's structure and a
literal's constants are among a term's constants (`Expr.constsResolve`). -/
def EntryScoped (R : Env) (ci : ConstantInfo) : Prop :=
  ci.toConstantVal.type.constsResolve R = true ∧
  (∀ cv v h, ci = .defnInfo cv v h → v.constsResolve R = true) ∧
  (∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
    r.rhs.constsResolve R = true ∧ (R.find? r.ctor).isSome = true ∧
    ∀ lvls pins, r.fire = .nested lvls pins → ∀ p ∈ pins, p.constsResolve R = true) ∧
  (∀ cv caps, ci = .indInfo cv caps →
    (∀ m ∈ caps.all, (R.find? m).isSome = true) ∧
    (caps.eta = true → (R.find? caps.etaCtor).isSome = true)) ∧
  ∀ d ∈ pinFootprint ci.toConstantVal.name, (R.find? d).isSome = true

/-- **What a record reads is stored in `R`**: its constants' laws and its tables (a table's
constructor and bodies). -/
def RecordScoped (R : Env) (d : Declaration) : Prop :=
  (∀ ci ∈ declConstants d, EntryScoped R ci) ∧
  ∀ t ∈ declTables d, (R.find? t.ctor).isSome = true ∧ ∀ b ∈ t.bodies.toList, b.constsResolve R = true

/-! ## Proofs -/

/-- **A type the kernel infers to be a proposition** at `E`: the theorem record's check of its type
(its type's type reduces to a sort of level zero), at some fuel. -/
def TypeIsProp (mode : CheckMode) (E : Env) (ty : Expr) : Prop :=
  ∃ F stype u, inferTypeCore mode false E F 0 ty = .ok stype ∧
    ensureSortCore mode false E F 0 stype = .ok u ∧ Level.isEquiv u .zero = some true

/-- **A proof**: a theorem record, a definition or opaque record whose value passes the theorem
record's check at `E`, the environment it is installed at (its type a proposition, its value of
that type), or an axiom record whose type is a proposition at `E`.  An opaque record at a
`reduce*` name is never one: its install pins it to the identity on `Nat` or `Bool`, and its leaf
is that function. -/
def ProofDecl (mode : CheckMode) (pins : List NatOpPinSet) (E : Env) : Declaration → Prop
  | .thmDecl .. => True
  | .defnDecl cv v _ => ∃ r, checkDeclStepC mode pins (mkFEnv E) (.thmDecl cv v) {} = .ok r
  | .opaqueDecl cv v => reduceOpNames.contains cv.name = false ∧
    ∃ r, checkDeclStepC mode pins (mkFEnv E) (.thmDecl cv v) {} = .ok r
  | .axiomDecl cv => TypeIsProp mode E cv.type
  | _ => False

/-- **The proof flags of a list of records installed from `E`**: every name a record installs that
is flagged is installed by a proof, at the environment before that record. -/
inductive FlagsOk (mode : CheckMode) (pins : List NatOpPinSet) (proofs : Name → Bool) :
    Env → List Declaration → Prop where
  | nil (E : Env) : FlagsOk mode pins proofs E []
  | cons {E : Env} {d : Declaration} {ds : List Declaration}
      (hflag : ∀ n ∈ declNames d, proofs n = true → ProofDecl mode pins E d)
      (rest : FlagsOk mode pins proofs (streamEnv [d] E) ds) :
      FlagsOk mode pins proofs E (d :: ds)

/-! ## Modules -/

/-- **A module** (see the module docstring). -/
structure Module where
  imports : List Nat
  /-- the records it is checked against, each one an earlier module's presentation -/
  ctx : List Declaration
  /-- its own records -/
  decls : List Declaration
  /-- for each name the context stores, the module it is read from -/
  src : Name → Nat
  /-- what identifies each name it stores across modules -/
  key : Name → Key Stmt
  /-- which of its own names it records as proofs -/
  proofs : Name → Bool
  /-- the records it presents to its importers -/
  iface : List Declaration

/-- **A module's context**: what its context records install. -/
def Module.context (m : Module) : Env := streamEnv m.ctx

/-- **A module's own environment**: its context with its own records installed. -/
def Module.own (m : Module) : Env := streamEnv m.decls m.context

/-- The key of a new own constant of module `i`: its statement if it is flagged a proof, the module
otherwise. -/
def Module.ownKey (m : Module) (i : Nat) (n : Name) (ci : ConstantInfo) : Key Stmt :=
  if m.proofs n then .proof (ci.toConstantVal.levelParams, ci.toConstantVal.type) else .home i

/-- **The part of module `b`'s own environment that module `i` reads as `b` does**: its constants
whose names `i`'s context stores and `i` and `b` give one key. -/
def readsAlike (dev : Nat → Module) (i b : Nat) : Env :=
  ⟨(dev b).own.consts.filter fun c =>
    ((dev i).context.find? c.toConstantVal.name).isSome &&
      (dev i).key c.toConstantVal.name == (dev b).key c.toConstantVal.name, []⟩

/-! ## The local checks -/

/-- **A module's interface is checked once, at the module**: every record it presents is a
presentation of one of its own records. -/
structure InterfaceOk (dev : Nat → Module) (b : Nat) : Prop where
  presents : ∀ e ∈ (dev b).iface, ∃ p ∈ (dev b).decls, Presents e p

/-- **An importer's checks** (at module `i`; see the module docstring). -/
structure ImportOk (mode : CheckMode) (pins : List NatOpPinSet) (dev : Nat → Module) (i : Nat) :
    Prop where
  below : ∀ b ∈ (dev i).imports, b < i
  src_lt : ∀ n, ((dev i).context.find? n).isSome = true → (dev i).src n < i
  nodup : ((dev i).context.consts.map (·.toConstantVal.name)).Nodup
  /-- every context record is a presentation of the module its names are read from -/
  presented : ∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, d ∈ (dev ((dev i).src n)).iface
  /-- a context record is read from one module: its names have one source -/
  one_src : ∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, ∀ n' ∈ declNames d,
    (dev i).src n = (dev i).src n'
  /-- what a context record reads is stored in the context, read as its source reads it -/
  reads : ∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, RecordScoped (readsAlike dev i ((dev i).src n)) d
  /-- the own records, accepted from the context by the fold's step -/
  accepted : ∃ q, DeclsRun mode pins (dev i).decls ((dev i).ctx.length, mkFEnv (dev i).context) q
  flags : FlagsOk mode pins (dev i).proofs (dev i).context (dev i).decls
  key_context : ∀ n, ((dev i).context.find? n).isSome = true →
    (dev i).key n = (dev ((dev i).src n)).key n
  key_own : ∀ n ci, (dev i).own.find? n = some ci → (dev i).context.find? n = none →
    (dev i).key n = (dev i).ownKey i n ci

/-- **The local checks at module `i`**: its own interface's, and its checks as an importer.  A
development every module of which passes them is the hypothesis of the modular theorem. -/
structure LocalOk (mode : CheckMode) (pins : List NatOpPinSet) (dev : Nat → Module) (i : Nat) :
    Prop where
  iface : InterfaceOk dev i
  importOk : ImportOk mode pins dev i

end ConLeche.Modular
