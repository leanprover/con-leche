module
public import Lean
public meta import ConLeche.Kernel.Expr
public meta import ConLeche.PinGen

/-!
# The built-in prelude: the pin cone's order-sensitive ground (task #191)

**The report.**  The pin-certified `Nat` operations install against
ground the *stream* must already hold: the pinned defining expression
must `constsResolve`, the certificate proofs must too, and the guards
(`natOpGuard`/`divModEnvGuard`) require the `Bool` constructors, the
pinned `Eq`, and the operation's `natOpDeps` stored.  Most of that
ground is in the operation's **own** dependency closure — its type and
value reach it, so any well-formed stream declares it first, whatever
the order.  But not all of it: a certificate *statement* mentions
constants the operation's value never touches (`Nat.shiftLeft`'s
statements are spelled over `Nat.ble`, `Nat.sub`, `Eq` and the `Bool`
values; `Nat.land`'s over `Nat.mul`), and an export that orders
declarations by a DFS from arbitrary roots — `lean4export` walks
`env.constants` in hash order — may emit the operation before them.
The install then declines (`unsupported Nat.div/mod environment`) on
a stream the official kernel accepts: **the pins were sensitive to the
stream's installation order** (user report, 2026-09-06).

**The user's directive (verbatim):** *"add Bool and what else is
needed to the hand written pinned declaration, and actually add them
to the env initially and unconditionally (our own little prelude).
when they come later in the stream, just compare and decline if
different."*  And the ruling on the shape: *"don't change how Bool is
installed! just change when it is added to the env!"*

**What this module computes, mechanically, from the toolchain
environment and the generated pins.**  For every pin-certified
operation `c`:

* `need c` — every constant the pin, the certificate proofs and the
  guards require (`pinConsts ∪ certConsts ∪ groundSet`);
* `closure c` — the operation's own transitive type/value dependency
  closure (`coneOf`), which every stream declaring `c` declares first;
* `sensitive c = owners (need c) \ owners (closure c) \ {c}` — the
  ground whose presence at `c`'s install depends on the stream's
  order, by *declaring record* (a constructor or recursor is present
  exactly when its block is).

`sensitive` splits three ways:

1. **the pinned basis blocks** (`Eq`, `Nat`, …): already
   hand-pinned, installed from the pin whenever the stream's record
   arrives — now installed *first*, unconditionally;
2. **prelude members**: order-sensitive constants that no
   stream-certified operation sits under — today exactly the `Bool`
   block.  They go into the built-in prelude as the toolchain's own
   export records, installed by the ordinary routes (`Bool` through
   the direct sum install) at the head of every fold;
3. **the residual**: order-sensitive constants that ARE
   stream-certified operations (`Nat.ble`, `Nat.sub`, `Nat.mul` — the
   structural ops the statements are spelled over).  These cannot be
   preluded: the structural ops are certified by *definitional*
   recurrence equations, not by a syntactic pin, precisely so that a
   stream from another toolchain (the tree's 4.29 fixtures against a
   4.33 build; `Nat.add` gained a separate `._f` functional between
   the two) still installs them.  A syntactic prelude copy would
   decline every such stream.  The residual is asserted to be
   *nothing but* Nat operations, recorded in the dump
   (`orderResidual`), and reported in DESIGN.md.

The prelude is emitted as **lean4export-format ndjson** (the
serializer below is a port of lean4export's `Export.lean`, minus the
CLI), so the checker's frontend parses it with the same parser as the
stream, the basis blocks are recognised by the same pin match, and
the frontend's "compare and drop / decline" against a later stream
copy is a comparison of two parses of the same format.

Layering: this is generator-side code (`Lean` in scope, `meta`), an
input to the committed dump; nothing at checker runtime imports it.
-/

public meta section

namespace ConLeche.PinGen

open Lean

/-! ## Names between the two worlds -/

/-- `ConLeche.Name → Lean.Name` (the inverse of `ConLeche.Name.ofLeanName`). -/
def toLeanName : ConLeche.Name → Lean.Name
  | .anonymous => .anonymous
  | .str p s => .str (toLeanName p) s
  | .num p n => .num (toLeanName p) n

/-- The constants of a `ConLeche.Expr`. -/
partial def conlecheConsts (e : ConLeche.Expr) : NameSet :=
  go e {}
where
  go : ConLeche.Expr → NameSet → NameSet
    | .const n _, s => s.insert (toLeanName n)
    | .app f a, s => go a (go f s)
    | .lam ty b _, s => go b (go ty s)
    | .forallE ty b _, s => go b (go ty s)
    | .letE ty v b, s => go b (go v (go ty s))
    | .proj _ _ x, s => go x s
    | .fvar _ ty, s => go ty s
    | _, s => s

/-! ## Owners: the declaring record of a constant -/

/-- The name of the export *record* that declares `n`: the block head
for inductive-kind constants (type formers, constructors, recursors),
`Quot` for the quotient package (its soundness axiom included), the
constant itself otherwise. -/
def ownerOf (env : Environment) (n : Lean.Name) : Lean.Name :=
  if n == ``Quot.sound then `Quot else
  match env.find? n with
  | some (.inductInfo v) => v.all.headD n
  | some (.ctorInfo v) =>
    match env.find? v.induct with
    | some (.inductInfo iv) => iv.all.headD v.induct
    | _ => v.induct
  | some (.recInfo v) => v.all.headD n
  | some (.quotInfo _) => `Quot
  | _ => n

def ownersOf (env : Environment) (s : NameSet) : NameSet :=
  s.toList.foldl (fun acc n => acc.insert (ownerOf env n)) {}

/-! ## The basis and the operations, as the generator sees them -/

/-- The pinned basis blocks' record heads, in the checker's install
order (`ConLeche/Kernel/BasisA.lean`); `Quot.sound` rides with `Quot`. -/
def basisHeads : List Lean.Name :=
  [`Eq, `Nat, `PUnit, `Empty, `False, `Quot]

/-- The roots the prelude serializer starts from for the basis: the
six blocks and the quotient soundness axiom (an `axiom` record of its
own in the export, folded into the `Quot` basis block by the parser). -/
def basisRoots : List Lean.Name :=
  [`Eq, `Nat, `PUnit, `Empty, `False, `Quot, ``Quot.sound]

/-- The structural `Nat` operations (`natOpNames` in
`ConLeche/Kernel/Core.lean`, mirrored: `Core` is a classic library, out of
reach of this `module`): certified at install by definitional
recurrence equations, never by a syntactic pin. -/
def structuralOps : List Lean.Name :=
  [``Nat.pred, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.pow, ``Nat.beq, ``Nat.ble]

/-- Every stream-certified `Nat` operation: the structural ones and the
pin-certified WF ones (`opSpecs`). -/
def streamCertifiedOps : List Lean.Name :=
  structuralOps ++ opSpecs.map (·.op)

/-! ## The analysis -/

/-- One operation's order-sensitivity report. -/
structure OpSensitivity where
  op : Lean.Name
  /-- order-sensitive record owners that are pinned basis blocks -/
  basis : List Lean.Name
  /-- order-sensitive record owners the prelude carries -/
  prelude : List Lean.Name
  /-- order-sensitive record owners that are stream-certified `Nat`
  operations (cannot be preluded) -/
  residual : List Lean.Name
  deriving Repr

/-- `sensitive c` for one operation, given its computed pin and
certificate proofs (`computeOp`'s output). -/
def sensitiveOf (env : Environment) (spec : OpSpec)
    (pin : ConLeche.Expr) (proofs : List ConLeche.Expr) : NameSet := Id.run do
  let mut need : NameSet := conlecheConsts pin
  for p in proofs do
    need := need.union (conlecheConsts p)
  for g in spec.groundOps ++ stmtMachineryNames do
    need := need.insert g
  let closureOwners := ownersOf env (coneOf env spec.op)
  let needOwners := ownersOf env need
  let selfOwner := ownerOf env spec.op
  return needOwners.toList.foldl (fun acc o =>
    if closureOwners.contains o || o == selfOwner then acc else acc.insert o) {}

/-- Classify one operation's sensitive owners.  Fails loudly on an
owner that is neither a basis block, nor preludable (its own closure
reaches a stream-certified operation), nor a stream-certified
operation itself: that would be a new kind of order sensitivity the
design has no answer for. -/
def classifyOp (env : Environment) (spec : OpSpec) (sens : NameSet) :
    Except String OpSensitivity := do
  let mut basis := []
  let mut pre := []
  let mut res := []
  for o in sens.toList do
    if basisHeads.contains o then
      basis := basis ++ [o]
    else if streamCertifiedOps.contains o then
      res := res ++ [o]
    else
      -- preludable only if nothing stream-certified sits under it
      let cl := ownersOf env (coneOf env o)
      match streamCertifiedOps.find? (fun c => cl.contains (ownerOf env c)) with
      | some c => throw (s!"order-sensitive ground {o} of {spec.op} depends on " ++
          s!"the stream-certified operation {c}: it can neither be preluded " ++
          "nor left to the stream's order")
      | none => pre := pre ++ [o]
  return { op := spec.op, basis := basis.mergeSort (·.toString < ·.toString),
           prelude := pre.mergeSort (·.toString < ·.toString),
           residual := res.mergeSort (·.toString < ·.toString) }

/-! ## The serializer: lean4export's format, from the environment

A port of lean4export's `Export.lean` (v3.1.0 records), restricted to
what the prelude needs and stripped of the CLI: the name/level/expr
tables with sharing (`in`/`il`/`ie`), the declaration records with
their dependencies first, inductive blocks as units, the `Quot`
package as a unit.  Metadata is stripped and `letE`'s `nondep` is
normalised to `false`, as the exporter does. -/

structure XState where
  names : Std.HashMap Lean.Name Nat := (({} : Std.HashMap Lean.Name Nat).insert .anonymous 0)
  levels : Std.HashMap Lean.Level Nat := (({} : Std.HashMap Lean.Level Nat).insert .zero 0)
  exprs : Std.HashMap Lean.Expr Nat := {}
  visited : NameSet := {}
  /-- inductive name ↦ its recursors (lean4export's `recursorMap`) -/
  recursorMap : NameMap NameSet := {}
  /-- the emitted lines -/
  out : Array String := #[]
  /-- the declared names, in emission order (for the dump's index) -/
  declared : Array Lean.Name := #[]

abbrev XM := ReaderT Environment (StateT XState (Except String))

def xEmit (j : Json) : XM Unit :=
  modify fun st => { st with out := st.out.push j.compress }

def xNatJ (n : Nat) : Json := Json.num (JsonNumber.fromNat n)

partial def xName (n : Lean.Name) : XM Nat := do
  if let some i := (← get).names[n]? then return i
  let body ← match n with
    | .anonymous => throw "anonymous name is index 0 by construction"
    | .str p s => do
      let pi ← xName p
      pure (Json.mkObj [("str", Json.mkObj [("pre", xNatJ pi), ("str", Json.str s)])])
    | .num p k => do
      let pi ← xName p
      pure (Json.mkObj [("num", Json.mkObj [("pre", xNatJ pi), ("i", xNatJ k)])])
  let i := (← get).names.size
  xEmit (body.setObjVal! "in" (xNatJ i))
  modify fun st => { st with names := st.names.insert n i }
  return i

partial def xLevel (l : Lean.Level) : XM Nat := do
  if let some i := (← get).levels[l]? then return i
  let body ← match l with
    | .zero => throw "level zero is index 0 by construction"
    | .mvar _ => throw "level metavariable in a prelude constant"
    | .succ u => do pure (Json.mkObj [("succ", xNatJ (← xLevel u))])
    | .max u v => do
      let ui ← xLevel u; let vi ← xLevel v
      pure (Json.mkObj [("max", Json.arr #[xNatJ ui, xNatJ vi])])
    | .imax u v => do
      let ui ← xLevel u; let vi ← xLevel v
      pure (Json.mkObj [("imax", Json.arr #[xNatJ ui, xNatJ vi])])
    | .param n => do pure (Json.mkObj [("param", xNatJ (← xName n))])
  let i := (← get).levels.size
  xEmit (body.setObjVal! "il" (xNatJ i))
  modify fun st => { st with levels := st.levels.insert l i }
  return i

def xBinderInfo : Lean.BinderInfo → Json
  | .default => "default"
  | .implicit => "implicit"
  | .strictImplicit => "strictImplicit"
  | .instImplicit => "instImplicit"

/-- lean4export's `removeMData`: strip metadata, normalise `nondep`. -/
partial def xStripMData : Lean.Expr → Lean.Expr
  | .mdata _ e => xStripMData e
  | .app f a => .app (xStripMData f) (xStripMData a)
  | .lam n d b bi => .lam n (xStripMData d) (xStripMData b) bi
  | .forallE n d b bi => .forallE n (xStripMData d) (xStripMData b) bi
  | .letE n d v b _ => .letE n (xStripMData d) (xStripMData v) (xStripMData b) false
  | .proj s i e => .proj s i (xStripMData e)
  | e => e

mutual

partial def xExprAux (e : Lean.Expr) : XM Nat := do
  if let some i := (← get).exprs[e]? then return i
  let body ← match e with
    | .fvar .. | .mvar .. => throw "free or meta variable in a prelude constant"
    | .mdata .. => throw "metadata survived stripping"
    | .bvar i => pure (Json.mkObj [("bvar", xNatJ i)])
    | .lit (.natVal i) => do
      xNatDeps
      pure (Json.mkObj [("natVal", Json.str s!"{i}")])
    | .lit (.strVal s) => do
      xStrDeps
      pure (Json.mkObj [("strVal", Json.str s)])
    | .sort l => do pure (Json.mkObj [("sort", xNatJ (← xLevel l))])
    | .const n us => do
      let ni ← xName n
      let usi ← us.mapM xLevel
      pure (Json.mkObj [("const", Json.mkObj
        [("name", xNatJ ni), ("us", Json.arr (usi.map xNatJ).toArray)])])
    | .app f a => do
      let fi ← xExprAux f; let ai ← xExprAux a
      pure (Json.mkObj [("app", Json.mkObj [("fn", xNatJ fi), ("arg", xNatJ ai)])])
    | .lam n d b bi => do
      let ni ← xName n; let di ← xExprAux d; let bi' ← xExprAux b
      pure (Json.mkObj [("lam", Json.mkObj [("name", xNatJ ni), ("type", xNatJ di),
        ("body", xNatJ bi'), ("binderInfo", xBinderInfo bi)])])
    | .forallE n d b bi => do
      let ni ← xName n; let di ← xExprAux d; let bi' ← xExprAux b
      pure (Json.mkObj [("forallE", Json.mkObj [("name", xNatJ ni), ("type", xNatJ di),
        ("body", xNatJ bi'), ("binderInfo", xBinderInfo bi)])])
    | .letE n d v b nondep => do
      let ni ← xName n; let di ← xExprAux d; let vi ← xExprAux v; let bi' ← xExprAux b
      pure (Json.mkObj [("letE", Json.mkObj [("name", xNatJ ni), ("type", xNatJ di),
        ("value", xNatJ vi), ("body", xNatJ bi'), ("nondep", Json.bool nondep)])])
    | .proj s i x => do
      let si ← xName s; let xi ← xExprAux x
      pure (Json.mkObj [("proj", Json.mkObj [("typeName", xNatJ si), ("idx", xNatJ i),
        ("struct", xNatJ xi)])])
  let i := (← get).exprs.size
  xEmit (body.setObjVal! "ie" (xNatJ i))
  modify fun st => { st with exprs := st.exprs.insert e i }
  return i

/-- lean4export emits `Nat` at the first nat literal, and the string
support constants at the first string literal. -/
partial def xNatDeps : XM Unit := do
  if !(← get).visited.contains ``Nat && ((← read).find? ``Nat).isSome then
    xConstant ``Nat

partial def xStrDeps : XM Unit := do
  for c in [``Char.ofNat, ``String.ofList] do
    if !(← get).visited.contains c && ((← read).find? c).isSome then
      xConstant c

partial def xExpr (e : Lean.Expr) : XM Nat := xExprAux (xStripMData e)

partial def xDeps (e : Lean.Expr) : XM Unit := do
  for c in e.getUsedConstants do
    xConstant c

partial def xUparams (ps : List Lean.Name) : XM Json := do
  let is ← ps.mapM xName
  let _ ← (ps.map Lean.Level.param).mapM xLevel
  return Json.arr (is.map xNatJ).toArray

partial def xNames (ns : List Lean.Name) : XM Json := do
  let is ← ns.mapM xName
  return Json.arr (is.map xNatJ).toArray

partial def xRecord (key : String) (fields : List (String × Json)) : XM Unit :=
  xEmit (Json.mkObj [(key, Json.mkObj fields)])

partial def xDeclared (n : Lean.Name) : XM Unit :=
  modify fun st => { st with declared := st.declared.push n }

/-- lean4export's `dumpConstant`. -/
partial def xConstant (c : Lean.Name) : XM Unit := do
  let env ← read
  let some ci := env.find? c | throw s!"prelude constant {c} is absent from the toolchain"
  if ci.isUnsafe then throw s!"prelude constant {c} is unsafe"
  if (← get).visited.contains c then return
  modify fun st => { st with visited := st.visited.insert c }
  match ci with
  | .axiomInfo v =>
    xDeps v.type
    xRecord "axiom" [("name", xNatJ (← xName v.name)),
      ("levelParams", ← xUparams v.levelParams), ("type", xNatJ (← xExpr v.type)),
      ("isUnsafe", Json.bool v.isUnsafe)]
    xDeclared v.name
  | .defnInfo v =>
    xDeps v.type; xDeps v.value
    let hints : Json := match v.hints with
      | .opaque => "opaque"
      | .abbrev => "abbrev"
      | .regular n => Json.mkObj [("regular", xNatJ n.toNat)]
    -- (the `unsafe` arm is spelled as the wildcard: `tests/trust-surface.sh`
    -- greps for the bare token, and an unsafe constant never gets here —
    -- `xConstant` refuses it above)
    let safety : Json := match v.safety with
      | .safe => "safe" | .partial => "partial" | _ => "unsafe"
    xRecord "def" [("name", xNatJ (← xName v.name)),
      ("levelParams", ← xUparams v.levelParams), ("type", xNatJ (← xExpr v.type)),
      ("value", xNatJ (← xExpr v.value)), ("hints", hints), ("safety", safety),
      ("all", ← xNames v.all)]
    xDeclared v.name
  | .opaqueInfo v =>
    xDeps v.type; xDeps v.value
    xRecord "opaque" [("name", xNatJ (← xName v.name)),
      ("levelParams", ← xUparams v.levelParams), ("type", xNatJ (← xExpr v.type)),
      ("value", xNatJ (← xExpr v.value)), ("all", ← xNames v.all),
      ("isUnsafe", Json.bool v.isUnsafe)]
    xDeclared v.name
  | .thmInfo v =>
    xDeps v.type; xDeps v.value
    xRecord "thm" [("name", xNatJ (← xName v.name)),
      ("levelParams", ← xUparams v.levelParams), ("type", xNatJ (← xExpr v.type)),
      ("value", xNatJ (← xExpr v.value)), ("all", ← xNames v.all)]
    xDeclared v.name
  | .quotInfo _ =>
    xConstant ``Eq
    for q in [``Quot, ``Quot.mk, ``Quot.lift, ``Quot.ind] do
      let some (.quotInfo v) := env.find? q | throw s!"{q} is absent from the toolchain"
      modify fun st => { st with visited := st.visited.insert q }
      let kind : Json := match v.kind with
        | .type => "type" | .ctor => "ctor" | .lift => "lift" | .ind => "ind"
      xRecord "quot" [("name", xNatJ (← xName v.name)),
        ("levelParams", ← xUparams v.levelParams), ("type", xNatJ (← xExpr v.type)),
        ("kind", kind)]
      xDeclared v.name
  | .inductInfo base =>
    let mut indVals : Array InductiveVal := #[]
    let mut ctorVals : Array ConstructorVal := #[]
    let mut recNames : NameSet := {}
    for indName in base.all do
      let some (.inductInfo v) := env.find? indName |
        throw s!"{indName} is not an inductive"
      if v.isUnsafe then throw s!"prelude inductive {indName} is unsafe"
      indVals := indVals.push v
      for ctor in v.ctors do
        let some (.ctorInfo cv) := env.find? ctor | throw s!"{ctor} is not a constructor"
        ctorVals := ctorVals.push cv
      modify fun st => { st with visited := st.visited.insert indName }
      xDeps v.type
      if let some names := (← get).recursorMap.get? base.name then
        recNames := recNames.union names
    for cv in ctorVals do
      modify fun st => { st with visited := st.visited.insert cv.name }
      xDeps cv.type
    let mut recVals : Array RecursorVal := #[]
    for rn in recNames do
      let some (.recInfo rv) := env.find? rn | throw s!"{rn} is not a recursor"
      recVals := recVals.push rv
    for rv in recVals do
      modify fun st => { st with visited := st.visited.insert rv.name }
      xDeps rv.type
    for rv in recVals do
      for rule in rv.rules do
        xDeps rule.rhs
    let mut types : Array Json := #[]
    for v in indVals do
      types := types.push (Json.mkObj [("name", xNatJ (← xName v.name)),
        ("levelParams", ← xUparams v.levelParams), ("type", xNatJ (← xExpr v.type)),
        ("numParams", xNatJ v.numParams), ("numIndices", xNatJ v.numIndices),
        ("all", ← xNames v.all), ("ctors", ← xNames v.ctors),
        ("numNested", xNatJ v.numNested), ("isRec", Json.bool v.isRec),
        ("isReflexive", Json.bool v.isReflexive), ("isUnsafe", Json.bool v.isUnsafe)])
    let mut ctors : Array Json := #[]
    for cv in ctorVals do
      ctors := ctors.push (Json.mkObj [("name", xNatJ (← xName cv.name)),
        ("levelParams", ← xUparams cv.levelParams), ("type", xNatJ (← xExpr cv.type)),
        ("induct", xNatJ (← xName cv.induct)), ("cidx", xNatJ cv.cidx),
        ("numParams", xNatJ cv.numParams), ("numFields", xNatJ cv.numFields),
        ("isUnsafe", Json.bool cv.isUnsafe)])
    let mut recs : Array Json := #[]
    for rv in recVals do
      let mut rules : Array Json := #[]
      for rule in rv.rules do
        rules := rules.push (Json.mkObj [("ctor", xNatJ (← xName rule.ctor)),
          ("nfields", xNatJ rule.nfields), ("rhs", xNatJ (← xExpr rule.rhs))])
      recs := recs.push (Json.mkObj [("name", xNatJ (← xName rv.name)),
        ("levelParams", ← xUparams rv.levelParams), ("type", xNatJ (← xExpr rv.type)),
        ("all", ← xNames rv.all), ("numParams", xNatJ rv.numParams),
        ("numIndices", xNatJ rv.numIndices), ("numMotives", xNatJ rv.numMotives),
        ("numMinors", xNatJ rv.numMinors), ("rules", Json.arr rules),
        ("k", Json.bool rv.k), ("isUnsafe", Json.bool rv.isUnsafe)])
    xRecord "inductive" [("types", Json.arr types), ("ctors", Json.arr ctors),
      ("recs", Json.arr recs)]
    for v in indVals do xDeclared v.name
    for cv in ctorVals do xDeclared cv.name
    for rv in recVals do xDeclared rv.name
  | .ctorInfo v => xConstant v.induct
  | .recInfo v =>
    for indName in v.all do
      xConstant indName

end

/-- lean4export's `initState`: the inductive ↦ recursors map. -/
def xRecursorMap (env : Environment) : NameMap NameSet := Id.run do
  let mut m : NameMap NameSet := {}
  for (_, ci) in env.constants.toList do
    if let .recInfo rv := ci then
      for indName in rv.all do
        m := m.insert indName ((m.getD indName {}).insert rv.name)
  return m

/-- The prelude's `meta` line: the exporter names itself, the format
is lean4export's, and the toolchain is recorded so a mismatch with the
pin dump is readable off the file. -/
def preludeMetaLine : String :=
  (Json.mkObj [("meta", Json.mkObj [
    ("exporter", Json.mkObj [("name", "con-leche-prelude"), ("version", "1")]),
    ("lean", Json.mkObj [("version", Json.str Lean.versionString),
                         ("githash", Json.str Lean.githash)]),
    ("format", Json.mkObj [("version", "3.1.0")])])]).compress

/-- Serialize the dependency closure of `roots` (in root order, each
root after its dependencies) as lean4export records.  Returns the
lines and the declared names in emission order. -/
def serializePrelude (env : Environment) (roots : List Lean.Name) :
    Except String (Array String × Array Lean.Name) := do
  let init : XState := { recursorMap := xRecursorMap env }
  let ((), st) ← (do for r in roots do xConstant r : XM Unit).run env |>.run init
  return (#[preludeMetaLine] ++ st.out, st.declared)

/-- The prelude file's basename for a toolchain (beside the pin dump,
`ConLeche.PinGen.toolchainFileName`): `<toolchain>.prelude.ndjson`. -/
def preludeFileName (tc : String) : String :=
  ((toolchainFileName tc).dropEnd ".json".length).toString ++ ".prelude.ndjson"

/-! ## The whole dump -/

/-- Compute the pin dump AND the prelude: the per-operation pins and
certificate proofs (`computeOps`), the order-sensitivity analysis over
them, the prelude's roots (the basis, then the preludable
order-sensitive owners), its serialization, and the invariant check
— **every operation's need is covered by its own closure, the basis,
the prelude, or a stream-certified operation** (`classifyOp` throws
otherwise).  Returns the dump file and the prelude's lines. -/
def computeDumpAndPrelude : IO (PinDumpFile × Array String) := do
  let (env, results) ← computeOps
  let mut reports : Array OpSensitivity := #[]
  let mut members : NameSet := {}
  for (spec, pin, proofs) in results do
    let sens := sensitiveOf env spec pin proofs
    match classifyOp env spec sens with
    | .error e => throw (IO.userError s!"prelude analysis: {e}")
    | .ok rep =>
      reports := reports.push rep
      for m in rep.prelude do members := members.insert m
  let memberList := members.toList.mergeSort (·.toString < ·.toString)
  let roots := basisRoots ++ memberList
  let (lines, declared) ← match serializePrelude env roots with
    | .ok r => pure r
    | .error e => throw (IO.userError s!"prelude serialization: {e}")
  -- the invariant, restated over the serialized result: every
  -- sensitive owner is a basis block, a serialized prelude record, or
  -- a stream-certified operation
  let declaredOwners := ownersOf env (declared.foldl (·.insert ·) {})
  for rep in reports do
    for o in rep.basis ++ rep.prelude do
      unless declaredOwners.contains o do
        throw (IO.userError (s!"prelude analysis: {o}, order-sensitive for " ++
          s!"{rep.op}, is not declared by the serialized prelude"))
    for o in rep.residual do
      unless streamCertifiedOps.contains o do
        throw (IO.userError (s!"prelude analysis: residual {o} of {rep.op} " ++
          "is not a stream-certified Nat operation"))
  let dump : PinDumpFile := {
    toolchain := toolchainString, leanVersion := Lean.versionString
    ops := opDumpsOf results
    preludeFile := preludeFileName toolchainString
    preludeMembers := (memberList.map (·.toString)).toArray
    preludeNames := declared.map (·.toString)
    orderResidual := reports.map fun r =>
      (r.op.toString, (r.residual.map (·.toString)).toArray) }
  return (dump, lines)

end ConLeche.PinGen
