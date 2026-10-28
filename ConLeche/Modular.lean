module

public import ConLeche.Cached.Installed
public import ConLeche.Modular.Generic

@[expose] public section

/-!
# Modular checking: modules, keys, the local checks

The statement half of the modular theorem (`ConLeche.modular_model_exists`,
`ConLeche/MainTheorem.lean`), in the style of `ConLeche/Denotes.lean`:
definitions only, importing the checker and nothing of the proof tiers,
so that the challenge (`ConLeche/Challenge.lean`) and the driver can
both read it.

* A **development** is a family of modules `dev : Nat → Module`, a
  module's imports earlier than it.  A module has its declarations
  (`decls`), its **context** (the environment its declarations are
  checked against), its **own environment** (`own`: the context with its
  declarations installed), for each context name the earlier module it
  is read from (`src`), which of its own constants are proofs (`proofs`), and the
  **key** of every name it stores (`key`).
* A **key** (`Key Stmt`, `ConLeche/Modular/Generic.lean`) is what
  identifies a constant across modules, beside its name: for an ordinary
  constant its **home**, the module that declares it; for a proof its
  statement, level parameters and type (`Stmt`): two proofs of one
  name and statement are one constant (the model gives every proof the
  point), whatever their bodies or homes.  No name is ever renamed.
* **The local checks** (`LocalOk`) read the module and the own
  environments and keys of the earlier modules its context is
  read from, nothing else:
  1. the imports come earlier, every context name is read from an
     earlier module (its source: in practice the constant's home), the
     context stores each name once (`below`, `src_lt`, `nodup`);
  2. the declarations are accepted from the context (a compared
     module's own environment is its context instead: it is validated
     by refinement alone, its own names read from its solution), one
     at a time,
     each by the fold's own install step and record check at the
     canonical index of the environment so far, and a constant flagged
     a proof is a theorem, or a definition or opaque constant that also
     passes the theorem check (its type is a proposition)
     (`accepted`, `AcceptedFrom`);
  3. every context constant refines the constant of the own
     environment of the earlier module it is read from (`context_le`,
     `Refines`: equal, or an assumption with the same level parameters
     and type, never at a pinned name), and what its laws read — the
     constants of its type and value, its rules' right-hand sides and
     constructors, its block's members and constructors, its
     projection table, the pinned names its fast path reads — is stored
     in that module's own environment and in the context, under one
     key in both (`scoping`, `EntryScoped`, `readsAlike`); the
     projections it reads are of type formers of the context
     (`projs`); an inductive kind comes with its block as the context
     presents it (`blocks`); a type former's table is
     that module's, and nothing else has one (`tables`, `tables_mem`);
  4. a context name has the key the module it is read from gives it, a
     new own name the module itself, or, flagged a proof, its level
     parameters and statement (`key_context`, `key_own`).
  The context's constant is the one scoped, not the source's: a
  module that sees a definition as an assumption reads only its type.

**The local checks, split** (`LocalOk.of_interface`,
`ConLeche/Verify/Modular/Interface.lean`): `LocalOk` is derived from a
check of every module's **interface** (`iface`: per name, the
presentations — the constant or the assumption of its statement, its
table, its footprint) done once at the module (`InterfaceOk`: the
presentations refine its own constants, and what their laws read is
stored in its own environment and listed in the footprint) and the
checks of each **importer** (`ImportOk`: its context consists of its
sources' presentations, each footprint stored in the context under the
source's keys; plus 1, 2, 4 and the context-internal parts of 3).  In the Lean mapping a presentation is a constant at a level of
its home (private: the installed constant; exported: its exported
presentation, the value hidden when its value gate is closed), and the
importer's footprint check is evaluating the presentation's gates.
-/

namespace ConLeche.Modular

open ConLeche.Cached

/-- **A proof's statement**: its level parameters and type. -/
abbrev Stmt := List Name × Expr

/-- **A presented constant**: one way a module's interface presents one
of its constants to importers — the constant (the module's own, or the
assumption of its statement), its projection table, and what its laws
read (`reads`, its footprint). -/
structure Presented where
  ci : ConstantInfo
  table : Option ProjTable
  reads : List Name

/-- **A module** (see the module docstring). -/
structure Module where
  imports : List Nat
  decls : List Declaration
  context : Env
  own : Env
  src : Name → Nat
  proofs : Name → Bool
  key : Name → Key Stmt
  /-- **a compared module** (a challenge): validated not by checking its
  declarations but by refinement — its own environment is read, name by
  name, from earlier modules (its own names from its solution), as a
  context is -/
  compared : Bool := false
  /-- **its interface**: per name, the presentations its importers may
  read the constant stored under it as -/
  iface : Name → List Presented := fun _ => []

/-- The key of a new own constant of module `i`: its statement if it is
flagged a proof, the module otherwise. -/
def Module.ownKey (m : Module) (i : Nat) (n : Name) (ci : ConstantInfo) : Key Stmt :=
  if m.proofs n then .proof (ci.toConstantVal.levelParams, ci.toConstantVal.type) else .home i

/-- **The pinned names**: names whose stored kind the checker's fast
paths and the model's laws read (the reserved basis, the certified
`Nat` operations, the `reduce*` opaques).  A context never presents
one of them as an assumption of something else. -/
def pinnedNames : List Name :=
  reservedBasisNames ++ natOpNames ++ natDivModNames ++ reduceOpNames

/-- **The names a pinned constant's fast path reads**, beyond its own
type and value: a certified `Nat` operation's dependencies, the `Nat`
basis and (for the `Bool`-valued and `ble`-guarded ones) the `Bool`
type and constructors; a `reduce*` opaque's element type. -/
def pinFootprint (n : Name) : List Name :=
  (if natOpNames.contains n || natDivModNames.contains n then
    natOpDeps n ++ [natName, natZeroName, natSuccName] ++
      (if n = natBeqName || n = natBleName || natDivModNames.contains n then
        [boolName, boolTrueName, boolFalseName] else [])
   else []) ++
  (if reduceOpNames.contains n then [reduceElemName n] else [])

/-- **Refinement of a constant** stored under `n`: the same constant,
or, at a name that is not pinned, an assumption with the same name,
level parameters and type (read through its type only: a constructor,
recursor or type former presented so needs nothing of its block). -/
def Refines (n : Name) (ci ci' : ConstantInfo) : Prop :=
  ci = ci' ∨ (n ∉ pinnedNames ∧ ci = .axiomInfo ci'.toConstantVal)

/-- **Every projection an expression reads is of a type former stored in
`C`** (a projection is read through its structure's table, which only
an inductive type former carries). -/
def Expr.projsFormer (C : Env) : Expr → Bool
  | .proj s _ e =>
    (match C.find? s with | some (.indInfo ..) => true | _ => false) && Expr.projsFormer C e
  | .app f a => Expr.projsFormer C f && Expr.projsFormer C a
  | .lam ty b | .forallE ty b => Expr.projsFormer C ty && Expr.projsFormer C b
  | .letE ty v b => Expr.projsFormer C ty && Expr.projsFormer C v && Expr.projsFormer C b
  | _ => true

/-- **The projections a context constant's data read are of type formers
of the context**: its type, a definition's value, a recursor's rules,
an inductive type's projection table. -/
def EntryProjs (C : Env) (n : Name) (ci : ConstantInfo) : Prop :=
  Expr.projsFormer C ci.toConstantVal.type = true ∧
  (∀ cv v h, ci = .defnInfo cv v h → Expr.projsFormer C v = true) ∧
  (∀ cv mI rP rules, ci = .recInfo cv mI rP rules → ∀ r ∈ rules,
    Expr.projsFormer C r.rhs = true ∧
    ∀ lvls pins, r.fire = .nested lvls pins → ∀ p ∈ pins, Expr.projsFormer C p = true) ∧
  ∀ cv caps, ci = .indInfo cv caps → ∀ t, C.findTable? n = some t →
    ∀ b ∈ t.bodies.toList, Expr.projsFormer C b = true

/-- **An inductive kind comes with its block**, as the context presents
it: a type former with its block's members as type formers, its
constructors, η constructor and table constructor as constructors; a
constructor with its result family as a type former; a recursor with
its rules' constructors as constructors. -/
def BlockIn (C : Env) (n : Name) : ConstantInfo → Prop
  | .indInfo _ caps =>
    (∀ m ∈ caps.all, ∃ cv caps', C.find? m = some (.indInfo cv caps')) ∧
    (∀ c ∈ caps.ctors, ∃ cv nP nF, C.find? c = some (.ctorInfo cv nP nF)) ∧
    (caps.eta = true → ∃ cv nP nF, C.find? caps.etaCtor = some (.ctorInfo cv nP nF)) ∧
    ∀ t, C.findTable? n = some t → ∃ cv nP nF, C.find? t.ctor = some (.ctorInfo cv nP nF)
  | .ctorInfo cv _ _ => ∀ T us, cv.type.piResult.getAppFn = .const T us →
    ∃ cvT capsT, C.find? T = some (.indInfo cvT capsT)
  | .recInfo _ _ _ rules => ∀ r ∈ rules, ∃ cv nP nF, C.find? r.ctor = some (.ctorInfo cv nP nF)
  | _ => True

/-- **The part of module `b`'s own environment that module `i` reads as
`b` does**: its constants whose names `i`'s context stores and `i` and
`b` give one key (`b` the module a context constant is read from). -/
def readsAlike (dev : Nat → Module) (i b : Nat) : Env :=
  ⟨(dev b).own.consts.filter fun c =>
    ((dev i).context.find? c.name).isSome && (dev i).key c.name == (dev b).key c.name, []⟩

/-- **What a context constant's laws read is stored and read alike**
(check 3): `R` is the part of the own environment of the module the constant is
read from that the context stores under that module's keys (`readsAlike`), `C` the
context.  The constants of the
type (and of a definition's value), a recursor's rules (right-hand
sides, nested pins, constructors), an inductive type's block members,
constructors, η constructor and projection table, and the names a
pinned constant's fast path reads (`pinFootprint`). -/
def EntryScoped (R C : Env) (n : Name) (ci : ConstantInfo) : Prop :=
  ci.toConstantVal.type.constsResolve R = true ∧
  (∀ cv v h, ci = .defnInfo cv v h → v.constsResolve R = true) ∧
  (∀ cv mI rP rules, ci = .recInfo cv mI rP rules → ∀ r ∈ rules,
    r.rhs.constsResolve R = true ∧ (R.find? r.ctor).isSome = true ∧
    ∀ lvls pins, r.fire = .nested lvls pins → ∀ p ∈ pins, p.constsResolve R = true) ∧
  (∀ cv caps, ci = .indInfo cv caps →
    (∀ m ∈ caps.all, (R.find? m).isSome = true) ∧
    (∀ c ∈ caps.ctors, (R.find? c).isSome = true) ∧
    (caps.eta = true → (R.find? caps.etaCtor).isSome = true) ∧
    ∀ t, C.findTable? n = some t →
      (R.find? t.ctor).isSome = true ∧ ∀ b ∈ t.bodies.toList, b.constsResolve R = true) ∧
  ∀ d ∈ pinFootprint n, (R.find? d).isSome = true

/-- **A flagged declaration is a proof**: a theorem, or a definition or
opaque constant at a name that is not pinned whose value also passes
the theorem record's check at the environment it is installed at (its
type a proposition, its value of that type). -/
def ProofDecl (mode : CheckMode) (E : Env) : Declaration → Prop
  | .thmDecl cv _ => cv.name ∉ pinnedNames
  | .defnDecl cv v _ | .opaqueDecl cv v =>
    cv.name ∉ pinnedNames ∧
      ∃ s, checkPending mode (mkFEnv E) ⟨⟨.thm, cv, v⟩, 0, (mkFEnv E).visibleBelow⟩ {}
        = .ok ((), s)
  | _ => False

/-- **A declaration list accepted from an environment** (check 2): each
declaration installed by the fold's step (`installDeclStep`) at the
canonical index of the environment so far, its record (if any) checked
(`checkPending`), and a flagged name the step stores is stored by a
proof (`ProofDecl`);
the next declaration starts at the environment the step produced. -/
inductive AcceptedFrom (mode : CheckMode) (pins : List NatOpPinSet) (proofs : Name → Bool) :
    Env → List Declaration → Env → Prop where
  | nil (E : Env) : AcceptedFrom mode pins proofs E [] E
  | cons {E E' : Env} {d : Declaration} {ds : List Declaration} {i : Nat} {fe : FEnv}
      {pend : Array PendingCheck}
      (hstep : installDeclStep mode pins (i, mkFEnv E, #[]) d = .ok (i + 1, fe, pend))
      (hrec : ∀ pc ∈ pend.toList, ∃ s, checkPending mode fe pc {} = .ok ((), s))
      (hflag : ∀ n, proofs n = true → E.find? n = none → (fe.env.find? n).isSome = true →
        ProofDecl mode E d)
      (rest : AcceptedFrom mode pins proofs fe.env ds E') :
      AcceptedFrom mode pins proofs E (d :: ds) E'

/-- **The local checks at module `i`** (see the module docstring). -/
structure LocalOk (mode : CheckMode) (pins : List NatOpPinSet) (dev : Nat → Module) (i : Nat) :
    Prop where
  below : ∀ b ∈ (dev i).imports, b < i
  src_lt : ∀ n, ((dev i).context.find? n).isSome = true → (dev i).src n < i
  nodup : ((dev i).context.consts.map (·.name)).Nodup
  accepted : (dev i).compared = false →
    AcceptedFrom mode pins (dev i).proofs (dev i).context (dev i).decls (dev i).own
  /-- a compared module's own environment is its context: every name of
  it, its own included, refines the constant of the earlier module it is
  read from (its solution, for its own names) -/
  compared_own : (dev i).compared = true → (dev i).own = (dev i).context
  context_le : ∀ n ci, (dev i).context.find? n = some ci →
    ∃ ci', (dev ((dev i).src n)).own.find? n = some ci' ∧ Refines n ci ci'
  scoping : ∀ n ci, (dev i).context.find? n = some ci →
    EntryScoped (readsAlike dev i ((dev i).src n)) (dev i).context n ci
  /-- a type former's table is its source's; nothing else has one (an
  assumed former included) -/
  tables : ∀ T ci, (dev i).context.find? T = some ci →
    (dev i).context.findTable? T =
      match ci with
      | .indInfo .. => (dev ((dev i).src T)).own.findTable? T
      | _ => none
  projs : ∀ n ci, (dev i).context.find? n = some ci → EntryProjs (dev i).context n ci
  blocks : ∀ n ci, (dev i).context.find? n = some ci → BlockIn (dev i).context n ci
  /-- a recursor's source module stores its rules' constructors'
  families as type formers -/
  recFam : ∀ n cv mI rP rules, (dev i).context.find? n = some (.recInfo cv mI rP rules) →
    ∀ r ∈ rules, ∀ cvj nP nF,
      (dev ((dev i).src n)).own.find? r.ctor = some (.ctorInfo cvj nP nF) →
      ∀ T us, cvj.type.piResult.getAppFn = .const T us →
      ∃ cvT capsT, (dev ((dev i).src n)).own.find? T = some (.indInfo cvT capsT)
  tables_mem : ∀ t ∈ (dev i).context.tables, (dev i).context.findTable? t.structName = some t
  key_context : ∀ n, ((dev i).context.find? n).isSome = true →
    (dev i).key n = (dev ((dev i).src n)).key n
  key_own : ∀ n ci, (dev i).own.find? n = some ci → (dev i).context.find? n = none →
    (dev i).key n = (dev i).ownKey i n ci

/-! ## The local checks, split: once per interface, then per importer -/

/-- **The part of `E` a footprint names.** -/
def readsIn (E : Env) (ns : List Name) : Env :=
  ⟨E.consts.filter fun c => ns.contains c.name, []⟩

/-- The table a context gives a presented constant: the presentation's,
for a type former; none otherwise. -/
def formerTable (ci : ConstantInfo) (t : Option ProjTable) : Option ProjTable :=
  match ci with
  | .indInfo .. => t
  | _ => none

/-- **A module's interface is checked once** (at module `b`): every
presentation of a name refines the constant `b`'s own environment stores
under it; a presented type former's table is `b`'s own table; what its laws read is stored in `b`'s own environment and
listed in its footprint; and a presented recursor's rules are of
constructors of type formers `b`'s own environment stores. -/
structure InterfaceOk (dev : Nat → Module) (b : Nat) : Prop where
  refines : ∀ n e, e ∈ (dev b).iface n →
    ∃ ci', (dev b).own.find? n = some ci' ∧ Refines n e.ci ci'
  table : ∀ n e, e ∈ (dev b).iface n → ∀ cv caps, e.ci = .indInfo cv caps →
    e.table = (dev b).own.findTable? n
  reads : ∀ n e, e ∈ (dev b).iface n →
    EntryScoped (readsIn (dev b).own e.reads) (dev b).own n e.ci
  recFam : ∀ n e, e ∈ (dev b).iface n → ∀ cv mI rP rules, e.ci = .recInfo cv mI rP rules →
    ∀ r ∈ rules, ∀ cvj nP nF, (dev b).own.find? r.ctor = some (.ctorInfo cvj nP nF) →
      ∀ T us, cvj.type.piResult.getAppFn = .const T us →
      ∃ cvT capsT, (dev b).own.find? T = some (.indInfo cvT capsT)

/-- **An importer's checks** (at module `i`): its context consists of
presentations from its sources' interfaces — every context constant is
a presentation of the interface of the module it is read from, a type
former with that presentation's table and nothing else with one, and every name of its footprint is stored in the
context under that module's keys — together with the checks that
concern the importer alone: its imports and sources are earlier, its
names unique, its declarations accepted (or, compared, its own
environment its context), its context's projections and blocks within
it, its tables listed once, and its keys its sources' for context names
and its own for its own names. -/
structure ImportOk (mode : CheckMode) (pins : List NatOpPinSet) (dev : Nat → Module) (i : Nat) :
    Prop where
  below : ∀ b ∈ (dev i).imports, b < i
  src_lt : ∀ n, ((dev i).context.find? n).isSome = true → (dev i).src n < i
  nodup : ((dev i).context.consts.map (·.name)).Nodup
  accepted : (dev i).compared = false →
    AcceptedFrom mode pins (dev i).proofs (dev i).context (dev i).decls (dev i).own
  compared_own : (dev i).compared = true → (dev i).own = (dev i).context
  presented : ∀ n ci, (dev i).context.find? n = some ci →
    ∃ e ∈ (dev ((dev i).src n)).iface n, e.ci = ci ∧
      (dev i).context.findTable? n = formerTable ci e.table ∧
      ∀ d ∈ e.reads, ((dev i).context.find? d).isSome = true ∧
        (dev i).key d = (dev ((dev i).src n)).key d
  projs : ∀ n ci, (dev i).context.find? n = some ci → EntryProjs (dev i).context n ci
  blocks : ∀ n ci, (dev i).context.find? n = some ci → BlockIn (dev i).context n ci
  tables_mem : ∀ t ∈ (dev i).context.tables, (dev i).context.findTable? t.structName = some t
  key_context : ∀ n, ((dev i).context.find? n).isSome = true →
    (dev i).key n = (dev ((dev i).src n)).key n
  key_own : ∀ n ci, (dev i).own.find? n = some ci → (dev i).context.find? n = none →
    (dev i).key n = (dev i).ownKey i n ci

end ConLeche.Modular
