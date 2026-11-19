module

public import ConLeche.Cached.Decls
public import ConLeche.Modular.Generic

@[expose] public section

/-!
# Modular checking: modules, agreement, the local checks

The statement half of modular checking, in the style of `ConLeche/Denotes.lean`: definitions only,
importing the checker and nothing of the proof tiers.  The abstract argument is
`ConLeche/Modular/Generic.lean` (the whitepaper fragment's `ModularSemantics.lean`); what this file
adds is what a module is for con-leche and what its checks are.

* A **development** is a family of modules `dev : Nat → Module`, a module's imports earlier than it.
  A module has its own records (`decls`) and its **context** (`ctx`): the records it is checked
  against, each one a record an earlier module presents (`iface`).  The context's environment is
  what those records install (`Module.context`, `streamEnv`), its own environment the context with its
  own records installed (`Module.own`).  For every name the context stores, `src` is the module it is
  read from.  No name is ever renamed, and there is no merged environment: two modules may declare
  one name and never be loaded together.
* A **presentation** (`Presents`) of an own record is a record that installs the same constants (in
  any order) and tables, or the record's statement (`stmtOf`): a definition, theorem or opaque constant as an axiom
  of its name, level parameters and type.  An inductive group is presented as its record, so it
  reaches an importer whole.
* **Agreement** (`Agree dev i b n`): module `b`'s copy of a name of `i`'s context stands for the
  copy `i` reads, because `b` is the module `i` reads it from, or `b` reads it and an earlier
  module's copy agrees both with `b`'s and with `i`'s (one record, loaded through two paths), or
  both copies are proofs of one statement whose names agree: a statement of which an earlier
  module's copy, its names agreeing too, is a theorem (a theorem's type is a proposition), or else
  one `i` infers to be a proposition over the part of its context below the name (`Module.part`,
  the records before the name's).  Every model gives agreeing copies one value; no module records anything about its
  names for others to read.

**The local checks** split by who runs them:
1. at the home, once (`InterfaceOk`): every presentation the module offers presents one of its own
   records;
2. at the importer (`ImportOk`): the imports and sources come earlier; the context stores each name
   once; every context record is read from one module and is a presentation of it; what a context
   record's constants read is stored in the context and agrees with that module's copy
   (`RecordScoped` over `readsAlike`); every context record reads only itself and earlier records
   (`ordered`); and the own records are accepted from the context, one after another, each by the
   fold's own step (`DeclsRun`).

The context need not be everything the module loads: any part of it closed under what its records
read is a context in this sense, which is why a worker may check a module over the reach of its own
records.

**The statement these checks are for** (proved for con-leche's models by task #463):

```
theorem modular_model_exists (V : Type w) [SetTheory V]
    (pins : List NatOpPinSet) (maxNatSize : Nat) (dev : Nat → Modular.Module) (i : Nat)
    (hok : ∀ j ≤ i, Modular.LocalOk .verified pins maxNatSize dev j) :
    ∃ m : ∀ j ≤ i, Model V (dev j).own,
      (∀ j hj n, ((dev j).context.find? n).isSome = true →
        ∃ h : (dev j).src n ≤ i, (m j hj).cval n = (m ((dev j).src n) h).cval n) ∧
      ∀ j hj n cv, (dev j).own.find? n = some (.thmInfo cv) →
        (m j hj).cval n = fun _ => pt
```

a compatible family of models of the own environments: every module gives each name of its
context the value the module it is read from gives it, and every theorem the point.  Its corollary is that no own environment
stores a constant of type `False`.
-/

namespace ConLeche.Modular

open ConLeche.Cached

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

/-- **What a constant's laws read is stored in `R`**: the constants of its type, a definition's
value, a recursor's rules (right-hand sides, nested pins, constructors), a type former's block
members, and the names its fast path reads.  A projection's structure and a
literal's constants are among a term's constants (`Expr.constsResolve`). -/
def EntryScoped (R : Env) (ci : ConstantInfo) : Prop :=
  ci.toConstantVal.type.constsResolve R = true ∧
  (∀ cv v h, ci = .defnInfo cv v h → v.constsResolve R = true) ∧
  (∀ cv mI rP isK rules, ci = .recInfo cv mI rP isK rules → ∀ r ∈ rules,
    r.rhs.constsResolve R = true ∧ (R.find? r.ctor).isSome = true ∧
    ∀ lvls pins, r.fire = .nested lvls pins → ∀ p ∈ pins, p.constsResolve R = true) ∧
  (∀ cv caps, ci = .indInfo cv caps → ∀ m ∈ caps.all, (R.find? m).isSome = true) ∧
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

/-- **The names an expression reads**: its constants, a literal's support names and a
projection's structure (the names `Expr.constsResolve` asks stored). -/
def _root_.ConLeche.Expr.readNames : Expr → List Name
  | .bvar _ | .sort _ => []
  | .lit (.natVal _) => [natName, natZeroName, natSuccName]
  | .lit (.strVal _) =>
    [natName, natZeroName, natSuccName, stringName, stringOfListName, listName, listNilName,
      listConsName, charName, charOfNatName]
  | .const n _ => [n]
  | .fvar _ ty => ty.readNames
  | .app f a => f.readNames ++ a.readNames
  | .lam ty body | .forallE ty body => ty.readNames ++ body.readNames
  | .letE ty val body => ty.readNames ++ val.readNames ++ body.readNames
  | .proj s _ e => s :: e.readNames

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
  /-- the records it presents to its importers -/
  iface : List Declaration

/-- **A module's context**: what its context records install. -/
def Module.context (m : Module) : Env := streamEnv m.ctx

/-- **A module's own environment**: its context with its own records installed. -/
def Module.own (m : Module) : Env := streamEnv m.decls m.context

/-- **A context name's rank**: the position of the context record installing it. -/
def Module.rank (m : Module) (n : Name) : Nat := m.ctx.findIdx fun d => (declNames d).contains n

/-- **The part of the context below a name**: the records before the one installing it. -/
def Module.part (m : Module) (n : Name) : Env := streamEnv (m.ctx.take (m.rank n))

/-- **Module `b`'s copy of `n` agrees with the one module `i` reads** (see the module docstring). -/
inductive Agree (dev : Nat → Module) : Nat → Nat → Name → Prop
  /-- `b` is the module `i` reads `n` from -/
  | same {i b : Nat} {n : Name} : b = (dev i).src n → Agree dev i b n
  /-- `b` reads `n`, and an earlier module's copy agrees both with `b`'s and with `i`'s: one
  record, loaded through two paths -/
  | via {i b t : Nat} {n : Name} : ((dev b).context.find? n).isSome = true → t < b →
      Agree dev b t n → Agree dev i t n → Agree dev i b n
  /-- two proofs of one statement, whose names agree: `i` infers it to be a proposition over the
  part of its context below `n` -/
  | proof {i b : Nat} {n : Name} {ci ci' : ConstantInfo} :
      (dev i).context.find? n = some ci → (dev b).own.find? n = some ci' →
      ci'.toConstantVal = ci.toConstantVal → ci.isStmtKind = true → ci'.isStmtKind = true →
      (∀ c ∈ ci.toConstantVal.type.readNames, Agree dev i b c) →
      ci.toConstantVal.type.constsResolve ((dev i).part n) = true →
      TypeIsProp .verified ((dev i).part n) ci.toConstantVal.type → Agree dev i b n
  /-- two proofs of one statement, whose names agree: an earlier module `t` stores it as a
  theorem, whose names agree too (a theorem's type is a proposition) -/
  | thm {i b t : Nat} {n : Name} {ci ci' : ConstantInfo} {cv : ConstantVal} :
      (dev i).context.find? n = some ci → (dev b).own.find? n = some ci' →
      ci'.toConstantVal = ci.toConstantVal → ci.isStmtKind = true → ci'.isStmtKind = true →
      (∀ c ∈ ci.toConstantVal.type.readNames, Agree dev i b c) →
      ci.toConstantVal.type.constsResolve ((dev i).part n) = true →
      t < i → (dev t).own.find? n = some (.thmInfo cv) → cv = ci.toConstantVal →
      (∀ c ∈ ci.toConstantVal.type.readNames, Agree dev i t c) → Agree dev i b n

open Classical in
/-- **The part of module `b`'s own environment that module `i` reads as `b` does**: its constants
whose names `i`'s context stores and whose copies agree with `i`'s. -/
noncomputable def readsAlike (dev : Nat → Module) (i b : Nat) : Env :=
  ⟨(dev b).own.consts.filter fun c =>
    decide (((dev i).context.find? c.toConstantVal.name).isSome = true ∧
      Agree dev i b c.toConstantVal.name), []⟩

/-! ## The local checks -/

/-- **A module's interface is checked once, at the module**: every record it presents is a
presentation of one of its own records. -/
structure InterfaceOk (dev : Nat → Module) (b : Nat) : Prop where
  presents : ∀ e ∈ (dev b).iface, ∃ p ∈ (dev b).decls, Presents e p

/-- **An importer's checks** (at module `i`; see the module docstring). -/
structure ImportOk (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat)
    (dev : Nat → Module) (i : Nat) : Prop where
  below : ∀ b ∈ (dev i).imports, b < i
  src_lt : ∀ n, ((dev i).context.find? n).isSome = true → (dev i).src n < i
  nodup : ((dev i).context.consts.map (·.toConstantVal.name)).Nodup
  /-- every context record is a presentation of the module its names are read from -/
  presented : ∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, d ∈ (dev ((dev i).src n)).iface
  /-- a context record is read from one module: its names have one source -/
  one_src : ∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, ∀ n' ∈ declNames d,
    (dev i).src n = (dev i).src n'
  /-- what a context record reads is stored in the context, and agrees with its source's copy -/
  reads : ∀ d ∈ (dev i).ctx, ∀ n ∈ declNames d, RecordScoped (readsAlike dev i ((dev i).src n)) d
  /-- a context record reads only itself and the records before it -/
  ordered : ∀ k (h : k < (dev i).ctx.length),
    RecordScoped (streamEnv ((dev i).ctx.take (k + 1))) (dev i).ctx[k]
  /-- the own records, accepted from the context by the fold's step -/
  accepted : ∃ q, DeclsRun mode pins maxNatSize none (dev i).decls
    ((dev i).ctx.length, mkFEnv (dev i).context) q

/-- **The local checks at module `i`**: its own interface's, and its checks as an importer.  A
development every module of which passes them is the hypothesis of the modular theorem. -/
structure LocalOk (mode : CheckMode) (pins : List NatOpPinSet) (maxNatSize : Nat)
    (dev : Nat → Module) (i : Nat) : Prop where
  iface : InterfaceOk dev i
  importOk : ImportOk mode pins maxNatSize dev i

end ConLeche.Modular
