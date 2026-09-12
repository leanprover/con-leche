module

public import ConLeche.Frontend.Export
public import ConLeche.Frontend.InModel
public import ConLeche.Cached.ExprNodes
/- The line reader the driver calls is the SPECIFICATION, `scanLineSpec`
(the naive recogniser); the compiler substitutes `scanLineFwd` on the
strength of `scanLineSpec_eq_scanLineFwd` (`@[csimp]`).  `Scan.Fast`
comes with it. -/
public import ConLeche.Frontend.Scan.Equiv

@[expose] public section

/-!
# Direct-to-`Expr` export parsing (task #171)

The user order: the cached pipeline parses the ndjson export
**directly into `Expr`** — no parse arena, no `ofStore` conversion,
no interned detour.  The export's `ie`-indices *are* the sharing: the
format already externalizes exactly the DAG structure the arena
reconstructs, so the parse keeps a stream-index-keyed table of
`Expr` values and a table hit is a shared node by reference.
Sharing is preserved structurally; the derived fields are computed
once per node by the smart constructors, which is also what makes
every parsed term well-formed **by construction** — the entry obligation
the capstone consumes (`ConLeche/Verify/Cached/ParseC.lean`), replacing
`OfStoreC`'s index-memo lemma.

**The stream is read as bytes** (task #256): the driver asks the
handle for 4 MiB at a time, carries the incomplete tail into the next
chunk, and hands every complete line to the byte recogniser of
`ConLeche/Frontend/Scan/Fast.lean`, which decodes it into a syntax
record (`LineRec`) still in stream indices.  `applyLine` below is the
semantic half: it resolves the indices against the tables, builds the
nodes through the smart constructors, and runs the projection rewrite
and the in-process modeller.  There is one grammar in the tree and no
`Lean.Json` on the checking path.

**THE DECODER EMITS THE FILE'S RECORDS AND NOTHING ELSE** (task
#293).  Every inductive block parses to an `indDecl` — `Nat` and `Eq`
like any other — and every `#QUOT` record to a `quotDecl` carrying the
constant the file declares at the kind it declares it at.  No basis
recognition, no reserved-name logic, no prelude, no dedupe and no
reordering happen here: the checker's own prelude is prepended, the
pinned shapes are recognised and the pinned `Nat` operations' ground is
hoisted by `preparePrelude` (`ConLeche/Frontend/Prepare.lean`), between
this parse and the fold, and every VERDICT — a basis redefinition, a
quotient mismatch, a stream copy of a prelude record that differs — is
the fold's.

**Two non-decoding steps are left here**, and both die with the
in-process modeller (task #279):

* **the projection-function rewrite (2026-09-06,
  `ConLeche/Frontend/ProjRec.lean`)**, the one surface rewrite this
  parse performs on a definition record: a projection function
`fun p⃗ self => .proj T i self` of a structure-like owner the direct
install does not serve is replaced, before it reaches the checker, by
the recursor application the module documents.  Two bookkeeping
tables feed it — the owners of every parsed inductive block
(`projOwners`) and the field sorts read off the `T._model.proj_i.iota`
artifacts the in-process modeller GENERATES (`projLevels`; task #219:
the generated records are the only source, and the scan runs on them
alone).  The `PUnit` block the constant motives need is the prelude's,
installed first in every fold, so the parse no longer tracks whether
the stream has declared one;
* **the in-process modeller** (task #200): a mutual or nested block's
  `_model` family is generated here and pushed ahead of the block.
-/

namespace ConLeche.Frontend

open ConLeche


/-! ## The direct parse state -/

/-- The direct parse state: stream-index-keyed tables of *values*
(names and levels as trees, expressions as `Expr` — a table hit is a
shared node by reference) and the parsed declarations as
`Declaration`. -/
structure StateD where
  names : IdTable Name := IdTable.singleton .anonymous
  levels : IdTable Level := IdTable.singleton .zero
  exprs : IdTable Expr := {}
  decls : Array Declaration := #[]
  /-- structure-like owners the projection rewrite serves, by type
  name (`ConLeche/Frontend/ProjRec.lean`) -/
  projOwners : Std.HashMap Name ProjRecOwner := {}
  /-- field sorts, by artifact iota name `T._model.proj_i.iota` (the
  in-process modeller's own, and only those; task #219) -/
  projLevels : Std.HashMap Name Level := {}
  /-- projection functions rewritten so far (names, for the driver's
  trace) -/
  projRewrites : Array Name := #[]
  /-- the declared types of every declaration pushed so far, by name:
  the in-process modeller's sort inferer reads them (task #200) -/
  constTypes : Std.HashMap Name (List Name × Expr) := {}
  /-- the definitional heights of the definitions pushed so far (the
  hints of the generated definitions are computed from them, task #200) -/
  heights : Std.HashMap Name Nat := {}
  /-- in-process modelling of mutual/nested blocks is on (task #200;
  `CON_LECHE_INMODEL=0` turns it off) -/
  inModel : Bool := true
  /-- the blocks modelled in-process, in stream order (for the
  receipt on stderr) -/
  inModelled : Array Name := #[]
  /-- how many records the in-process modeller GENERATED and pushed
  (task #219): they are declarations of the fold like any other, but
  they are not records of the FILE, so the driver's headline count
  subtracts them and `scripts/stream-census.py` predicts the verdict
  off the file again -/
  genRecords : Nat := 0
  /-- each generated record's leading name ↦ the block it models (task
  #219): the driver names the block when a generated record is the one
  that fails, so a failure the file cannot be indexed for is still
  attributable -/
  genOwner : Std.HashMap Name Name := {}
  /-- for the debug dump (`CON_LECHE_INMODEL_DUMP`): per modelled block, its
  ordinal among the stream's `inductive` records and the generated
  records -/
  inModelGen : Array (Nat × Array Declaration) := #[]
  /-- the number of `inductive` records seen so far -/
  indCount : Nat := 0
  /-- the parsed inductive blocks, by member type name (the in-process
  modeller's nested rung reads a container's shape off it) -/
  indBlocks : Std.HashMap Name InModel.BlockRec := {}
  /-- CENSUS mode (`CON_LECHE_INMODEL_CENSUS=1`): a generator decline is
  recorded and the block pushed bare instead of declining the parse, so
  one parse lists every block's outcome (the driver then stops before
  the fold) -/
  inModelCensus : Bool := false
  /-- the census's declines: block name and reason -/
  inModelDeclined : Array (Name × String) := #[]
/-- Record a pushed declaration's constants in the declaration table
(`constTypes`, `heights`; task #200). -/
def noteDecl (st : StateD) (d : Declaration) : StateD :=
  let cvs : List (Name × List Name × Expr × Option Nat) := match d with
    | .axiomDecl cv => [(cv.name, cv.levelParams, cv.type, none)]
    | .defnDecl cv _ h => [(cv.name, cv.levelParams, cv.type, some (InModel.hintHeight h))]
    | .thmDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
    | .opaqueDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
    | .basisDecl k => k.decls.map fun ci =>
      (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
    | .quotDecl _ cv => [(cv.name, cv.levelParams, cv.type, none)]
    | .indDecl block _ => block.map fun ci =>
      (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
  let ct := st.constTypes
  let hs := st.heights
  let st := { st with constTypes := {}, heights := {} }
  let (ct, hs) := cvs.foldl (fun (ct, hs) (n, lps, ty, h) =>
    (ct.insert n (lps, ty), match h with | some h => hs.insert n h | none => hs)) (ct, hs)
  { st with constTypes := ct, heights := hs }

/-- **One parsed record, appended** (task #293): the decoder keeps the
file's records in the file's order.  What used to sit here was the
prelude dedupe — a basis block the prelude held dropped by kind, a
record under a prelude name dropped when identical and DECLINING the
stream when different — and it is `preparePrelude`'s and the fold's
now (`ConLeche/Frontend/Prepare.lean`). -/
def pushDecl (st : StateD) (d : Declaration) : StateD :=
  noteDecl { st with decls := st.decls.push d } d

def StateD.name (st : StateD) (i : Nat) : M Name :=
  match st.names.get? i with
  | some n => pure n
  | none => throw s!"undefined name index {i}"

def StateD.level (st : StateD) (i : Nat) : M Level :=
  match st.levels.get? i with
  | some l => pure l
  | none => throw s!"undefined level index {i}"

def StateD.expr (st : StateD) (i : Nat) : M Expr :=
  match st.exprs.get? i with
  | some e => pure e
  | none => throw s!"undefined expr index {i}"

/-- Declaration-level expression lookup: the table read.

The frontend tree-size budget that used to sit here was **retired at
task #215**: every consumer it bounded is now either name-selected (the
basis-pin match) or a memoized DAG walk (`Expr.renameConsts`,
`Expr.instantiate1`; `@[csimp]` in `ConLeche/Kernel/ExprOps.lean`), and
the adversarial DAG-tower fixtures in `tests/e2e` are the standing
gate in its place — a limit told a user "no", a fixture tells *us*
which walker regressed. -/
def getDeclD (st : StateD) (i : Nat) : M Expr :=
  st.expr i

/-- The `pw` datum over the direct name table. -/
def parsePwD (st : StateD) : PwRec → M PropWhen
  | .never => pure .never
  | .ifAllZero ns => do pure (.ifAllZero (← ns.mapM st.name))

/-! ## The rebinding test (task #290)

Every table entry is bound once: a line that binds an index a
previous line already bound is a parse error.  Before this the tables
let a later line overwrite an entry all the same (the entries are
resolved eagerly, so nothing already built could change).  What the
rule buys is the one property a theorem about the FILE needs of the
tables: the entry a line bound is the entry every later line reads,
whatever else the file holds
(`ConLeche/Verify/Frontend/ApplyLine.lean`). -/

/-- The rebinding error, named once. -/
def reboundError (what : String) (i : Nat) : String :=
  s!"{what} index {i} is already bound"

/-- The three tests, on a BORROWED state.  Written as separate
functions rather than inline so that the state is not deconstructed
before the test: an owned `st.exprs.bound i` at the top of a `do`
block made the compiler project and `inc` every field of the state
first (the reset/reuse pass moved the deconstruction ahead of the
test), which was a 17 % instruction increase on the parse phase;
against a borrowed parameter the state stays whole until the update
that consumes it, exactly as before. -/
@[noinline] def StateD.freshName (st : @& StateD) (i : Nat) : M Unit :=
  if st.names.bound i then throw (reboundError "name" i) else pure ()
@[noinline] def StateD.freshLevel (st : @& StateD) (i : Nat) : M Unit :=
  if st.levels.bound i then throw (reboundError "level" i) else pure ()
@[noinline] def StateD.freshExpr (st : @& StateD) (i : Nat) : M Unit :=
  if st.exprs.bound i then throw (reboundError "expression" i) else pure ()

/-! ## Table entries -/

/-- A name-table entry: the name value is built directly. -/
def parseNameEntryD (st : StateD) (i : Nat) : NameRec → M StateD
  | .str pre s => do
    let p ← st.name pre
    st.freshName i
    pure { st with names := st.names.insert i (Name.str p s) }
  | .num pre n => do
    let p ← st.name pre
    st.freshName i
    pure { st with names := st.names.insert i (Name.num p n) }

/-- A level-table entry. -/
def parseLevelEntryD (st : StateD) (i : Nat) (r : LevelRec) : M StateD := do
  st.freshLevel i
  let l ← match r with
    | .succ u => do pure (Level.succ (← st.level u))
    | .max a b => do pure (Level.max (← st.level a) (← st.level b))
    | .imax a b => do pure (Level.imax (← st.level a) (← st.level b))
    | .param n => do pure (Level.param (← st.name n))
  pure { st with levels := st.levels.insert i l }

/-- An expression-table entry: build the `Expr` node from the
children's table values (the derived fields are the compiler's, task
#172 B3a).

Binder names are display data the official kernel's equality and hash
ignore; ours are `.anonymous` on every parsed binder (task #203,
beside the `.default` annotation of task #142), so `==` is
α-equivalence downstream.  The `name` field is still required to be
present and well-formed (the recogniser reads it), it is just not
resolved. -/
def parseExprEntryD (st : StateD) (i : Nat) (r : ExprRec) : M StateD := do
  st.freshExpr i
  let e ← match r with
    | .bvar k => pure (Expr.mkBvar k)
    | .sort u => do pure (Expr.mkSort (← st.level u))
    | .const n us => do
      let nm ← st.name n
      let ls ← us.mapM st.level
      pure (Expr.mkConst nm ls)
    | .app f a => do pure (Expr.mkApp (← st.expr f) (← st.expr a))
    | .lam ty bd pw => do
      pure (Expr.mkLam (← st.expr ty) (← st.expr bd) ⟨← parsePwD st pw⟩)
    | .forallE ty bd pw => do
      pure (Expr.mkForallE (← st.expr ty) (← st.expr bd) ⟨← parsePwD st pw⟩)
    | .letE ty vl bd => do
      pure (Expr.mkLetE (← st.expr ty) (← st.expr vl) (← st.expr bd))
    | .proj tn ix s => do
      pure (Expr.mkProj (← st.name tn) ix (← st.expr s))
    | .natVal n => pure (Expr.mkLit (.natVal n))
    | .strVal s => pure (Expr.mkLit (.strVal s))
  pure { st with exprs := st.exprs.insert i e }

/-! ## Declaration records -/

/-- A declaration's common data; the type stays `Expr`. -/
def parseCVD (st : StateD) (cv : CVRec) : M ConstantVal := do
  let name ← st.name cv.name
  let ty ← getDeclD st cv.type
  pure { name := name
         levelParams := ← cv.levelParams.mapM st.name
         type := ty }

/-- The projection-function rewrite at a definition record
(`ConLeche/Frontend/ProjRec.lean`): the value is `fun p⃗ self => .proj T i
self` for a recorded owner `T`, the field's sort is on record from the
artifact, `PUnit` is available, and the definition's level parameters
are the block's.  `none` = leave the record as parsed. -/
def projRewriteD (st : StateD) (cv : ConstantVal) (vl : Expr) :
    Option Expr := do
  let .proj T i (.bvar 0) := lamBody vl | none
  let o ← st.projOwners[T]?
  guard (cv.levelParams == o.lps)
  let l ← st.projLevels[projIotaName T i]?
  projRecValue o l cv.type vl i

/-- An artifact `T._model.proj_i.iota` names the field's sort in its
`Eq` level: recorded for the projection rewrite.  Run on the records
the in-process modeller GENERATES and on those alone (task #219): a
stream record is an ordinary declaration whatever it is called, and
the rewrite's field sorts come from the modeller's own family. -/
def noteProjIota (st : StateD) (cvp : ConstantVal) : StateD :=
  if isProjIotaName cvp.name then
    match projIotaLevel cvp.type with
    | some l =>
      let m := st.projLevels
      let st := { st with projLevels := {} }
      { st with projLevels := m.insert cvp.name l }
    | none => st
  else st

/-- Push one record the in-process modeller generated (task #200):
`pushDecl`, plus the projection-iota registration (the ONLY place it
runs since task #219 — a stream record is an ordinary declaration
whatever it is called). -/
def pushGenD (st : StateD) (d : Declaration) : StateD :=
  match d with
  | .thmDecl cv _ => pushDecl (noteProjIota st cv) d
  | _ => pushDecl st d

/-- Book a record the in-process modeller generated for block `T0`
(task #219): a declaration of the FOLD, never a record of the file, so
the driver's headline count subtracts it and a failure at it is
reported with the block it models. -/
def noteGen (st : StateD) (d : Declaration) (T0 : Name) : StateD :=
  let m := st.genOwner
  let st := { st with genOwner := {} }
  { st with genRecords := st.genRecords + 1,
            genOwner := d.names.foldl (fun m n => m.insert n T0) m }

/-- **The syntactic Π-telescope length of a declared type** (task
#271): official counts a constructor's binders by walking `is_pi`
without reducing (`check_constructors`), and the count past the
parameters is the `numFields` of the constructor it generates. -/
def indPiTeleLen : Expr → Nat
  | .forallE _ b _ => indPiTeleLen b + 1
  | _ => 0

/-- One recursor rule of an inductive record, resolved. -/
def parseRuleD (st : StateD) (ru : RuleRec) : M RecRule := do
  pure (RecRule.mk (← st.name ru.ctor) ru.nfields 0 .inert
    (← getDeclD st ru.rhs) false false false)

/-- The export's shape data of an inductive record, for the in-process
modeller (task #200). -/
def blockRecOf (st : StateD) (types : List IndTypeRec) (ctors : List IndCtorRec)
    (recs : List IndRecRec) : M InModel.BlockRec := do
  let types ← types.mapM fun t => do
    pure { cv := ← parseCVD st t.cv
           nP := t.numParams
           nIdx := t.numIndices
           ctors := ← t.ctors.mapM st.name
           isRec := t.isRec
           isReflexive := t.isReflexive
           numNested := t.numNested : InModel.IndTypeRec }
  let ctors ← ctors.mapM fun c => do
    pure { cv := ← parseCVD st c.cv
           nP := c.numParams
           nF := c.numFields : InModel.IndCtorRec }
  let recs ← recs.mapM fun r => do
    let rules ← r.rules.mapM (parseRuleD st)
    pure { cv := ← parseCVD st r.cv
           nP := r.numParams
           nM := r.numMotives
           nm := r.numMinors
           nI := r.numIndices
           rules := rules : InModel.IndRecRec }
  pure ⟨types, ctors, recs⟩

/-- Record the structure-like owners of a parsed block that the
projection rewrite serves (`projRecOwners`). -/
def registerProjOwners (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (block : List ConstantInfo) : M StateD := do
  let types ← tys.mapM fun t => do
    let cv ← parseCVD st t.cv
    pure (cv.name, cv.levelParams, cv.type, t.numParams, t.numIndices,
      ← t.ctors.mapM st.name, t.isRec)
  let ctors ← cts.mapM fun c => do
    let cv ← parseCVD st c.cv
    pure (cv.name, c.numFields, cv.type)
  let recs ← rcs.mapM fun r => do
    let cv ← parseCVD st r.cv
    pure (cv.name, cv.levelParams, cv.type, r.numMotives, r.numMinors)
  match projRecOwners block types ctors recs with
  | [] => pure st
  | owners =>
    let m := st.projOwners
    let st := { st with projOwners := {} }
    pure { st with projOwners := owners.foldl (fun m o => m.insert o.T o) m }

/-- Push the records the in-process modeller generated (task #200),
each booked as a declaration of the fold and not a record of the file
(task #219).  (The loop of the install half, as a function: the file
theorem's frame lemma is an induction on it, task #290.) -/
def pushGenList (st : StateD) : List Declaration → Name → StateD
  | [], _ => st
  | d :: ds, T0 => pushGenList (noteGen (pushGenD st d) d T0) ds T0

/-- **An inductive record, validated** (tasks #217, #228, #271): the
half of the record's processing that reads the state and changes
nothing — the verdict, or the block's constructors in the block's own
order with the declared parameter count.  Split from `installIndD`
below at task #290 so that a proof about what the parse does to its
state need not look here at all. -/
def validateIndD (st : @& StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) : M (RecordVerdict ⊕ (List IndCtorRec × Nat)) := do
  -- TASK #217 (audit follow-up 6): an `unsafe inductive` is DECLINED,
  -- not an error.  The official kernel admits unsafe blocks (it skips
  -- positivity for them); we support no unsafe declaration at all, and
  -- unsafe axioms/opaques/definitions already decline positively.
  if tys.any (·.isUnsafe) then
    return .inl (.declined "unsafe inductive declaration")
  -- TASK #228 — THE DECLARED PARAMETER COUNT.  Official's replay
  -- hands `add_inductive` the `numParams` of ONE inductive record of
  -- the block (`Declaration.inductDecl lparams nparams types`,
  -- `Lean4Checker/Replay.lean`) and checks every former and every
  -- constructor against it; which record that is, is the name order
  -- of the replay's walk.  So the count is well defined for the
  -- block exactly when its type records AGREE on it — as every
  -- record a real export writes does, `add_inductive` storing one
  -- `m_nparams` in every member's `InductiveVal`.  A block whose
  -- records disagree has no declared count this checker could hold
  -- official to, and is positively declined here rather than checked
  -- against a count official might not have chosen.
  let nPs := tys.map (·.numParams)
  let nPd := nPs.head?.getD 0
  unless nPs.all (· == nPd) do
    return .inl (.declined "inductive block whose type records disagree on numParams")
  -- TASK #271 (issues #5 and #7) — THE BLOCK'S REDUNDANT FIELDS.
  -- Official's replay hands `add_inductive` the type formers, the
  -- constructors and the parameter count; the kernel then GENERATES
  -- the constructors and the recursors, and the replay compares each
  -- exported CONSTRUCTOR and RECURSOR record with the generated one
  -- structurally (`checkPostponedConstructors`,
  -- `checkPostponedRecursors`, `Lean4Checker/Replay.lean`) — a
  -- mismatch is "Invalid constructor" / "Invalid recursor", a
  -- REJECT.  An exported INDUCTIVE record is never compared with the
  -- generated `InductiveVal`, so its `numIndices`, `numNested`,
  -- `isRec`, `isReflexive` and `all` are not input official reads and
  -- are not checked here either (the `numParams` half official DOES
  -- read is task #228's, just above).  What is read of a type record
  -- is its `ctors` list: it groups the constructor records into the
  -- block, and it IS the block's constructor order (issue #5 — the
  -- `cidx` field is the redundant copy, not the other way round).
  -- These are consistency checks between the stream's own fields, so
  -- they live here, in the parse, and their verdict is `.invalid`:
  -- the fold never sees such a block.
  let tyNames ← tys.mapM fun t => st.name t.cv.name
  let tyTypes ← tys.mapM fun t => getDeclD st t.cv.type
  let listed ← tys.mapM fun t => t.ctors.mapM st.name
  let ctorNames ← cts.mapM fun c => st.name c.cv.name
  let flat := listed.flatten
  unless flat.Nodup do
    return .inl (.invalid "duplicate constructor name in an inductive type's ctors")
  unless flat.length == cts.length do
    return .inl (.invalid s!"the inductive block lists {flat.length} constructors \
      and carries {cts.length} constructor records")
  let ctorIx : Std.HashMap Name Nat :=
    (ctorNames.foldl (fun (mi : Std.HashMap Name Nat × Nat) n =>
      (mi.1.insert n mi.2, mi.2 + 1)) ({}, 0)).1
  let ctsA := cts.toArray
  -- the constructors IN THE BLOCK'S OWN ORDER, `types[].ctors` in
  -- type order (issue #5): a record array in another order is the
  -- same block, and the recursor generated from it is the same one
  let mut ordered : Array IndCtorRec := #[]
  for tn in tyNames.zip listed do
    let (T, ns) := tn
    let mut j := 0
    for n in ns do
      let some k := ctorIx[n]? | return .inl (.invalid s!"No such constructor {n}")
      let some c := ctsA[k]? | return .inl (.invalid s!"No such constructor {n}")
      if let some ci := c.cidx then
        unless ci == j do
          return .inl (.invalid s!"constructor {n} declares cidx {ci}; it is \
            constructor {j} of {T}")
      if let some iw := c.induct then
        let iwn ← st.name iw
        unless iwn == T do
          return .inl (.invalid s!"constructor {n} declares induct {iwn}; it is \
            a constructor of {T}")
      -- `numFields`: official counts the constructor's own Π binders
      -- without reducing (`check_constructors` walks `is_pi`) and
      -- stores the count past the parameters, so a record that
      -- declares another number is not the generated constructor.
      -- Before this, a count too LARGE declined at the field
      -- telescope (arena `ctor-num-fields`) and a count too small was
      -- caught later, by the constructor's result type, if at all.
      let cty ← getDeclD st c.cv.type
      unless nPd + c.numFields == indPiTeleLen cty do
        return .inl (.invalid s!"constructor {n} declares {c.numFields} fields at \
          {nPd} parameters; its type has {indPiTeleLen cty} binders")
      ordered := ordered.push c
      j := j + 1
  let cts := ordered.toList
  -- The recursor records: the counts and the K flag the GENERATED
  -- recursor carries.  `numParams + numMotives + numMinors` and the
  -- major-premise index are compared with the block at the install
  -- (`nativeRecPinOk`), which leaves a compensating pair of lies
  -- open; the individual counts are here.
  --
  -- NOT at a NESTED block.  The kernel specialises a nested block
  -- into a mutual one with a mimic type per nested occurrence, and
  -- the recursors it generates — `T.rec`, `T.rec_1`, … — are the
  -- SPECIALISED block's: their motives and minor premises count the
  -- mimics too, so the declared block's own type and constructor
  -- counts are not what they carry (measured: `ind_nest_inf`'s
  -- `InfNest.rec` declares two motives at one declared type).
  -- `numNested` is a field of the type record, which official never
  -- compares; reading it here only ever WEAKENS these checks, never
  -- rejects on it.
  let nested := tys.any (·.numNested != 0)
  let nTypes := tys.length
  let nCtors := cts.length
  -- official's `is_K_target`: the block is a `Prop`, has ONE type
  -- with ONE constructor, and that constructor takes only the
  -- parameters.  At a former whose declared type is not a syntactic
  -- Π-telescope ending in a sort (task #195) the sort cannot be read
  -- here and the flag is left to the install.
  let kExpected? : Option Bool :=
    match tyTypes, listed, cts with
    | [ty], [[_]], [c] =>
      match ty.piResult with
      | .sort s => some (c.numFields == 0 && Level.isEquiv s .zero == some true)
      | _ => none
    | _, _, _ => some false
  for r in (if nested then [] else rcs) do
    let rn ← st.name r.cv.name
    unless r.numParams == nPd do
      return .inl (.invalid s!"recursor {rn} declares {r.numParams} parameters; \
        the block declares {nPd}")
    unless r.numMotives == nTypes do
      return .inl (.invalid s!"recursor {rn} declares {r.numMotives} motives; \
        the block has {nTypes} inductive types")
    unless r.numMinors == nCtors do
      return .inl (.invalid s!"recursor {rn} declares {r.numMinors} minor premises; \
        the block has {nCtors} constructors")
    if let some kE := kExpected? then
      unless r.k == kE do
        return .inl (.invalid s!"recursor {rn} declares k := {r.k}; the generated \
          recursor of this block is{if kE then "" else " not"} K-like")
    -- `numIndices` of `T.rec` is what is left of `T`'s own telescope
    -- once the parameters are peeled; unreadable at a former declared
    -- at a definition, and then not checked
    if let .str T "rec" := rn then
      for tt in tyNames.zip tyTypes do
        if tt.1 == T then
          if let some n := tt.2.piSortTeleLen? then
            unless nPd + r.numIndices == n do
              return .inl (.invalid s!"recursor {rn} declares {r.numIndices} indices; \
                {T} has {n - nPd} at {nPd} parameters")
  return .inr (cts, nPd)

/-- **An inductive record, installed**: the block's constants, the
projection-owner table, the basis-pin match, the in-process modeller,
the push.  Every change to the state a validated inductive record
makes is here. -/
def installIndD (st : StateD) (tys : List IndTypeRec) (cts : List IndCtorRec)
    (rcs : List IndRecRec) (nPd : Nat) : M (StateD ⊕ RecordVerdict) := do
  let types ← tys.mapM fun t => do
    pure (ConstantInfo.indInfo (← parseCVD st t.cv) {})
  let ctors ← cts.mapM fun c => do
    pure (ConstantInfo.ctorInfo (← parseCVD st c.cv) c.numParams c.numFields)
  let recs ← rcs.mapM fun r => do
    let rules ← r.rules.mapM (parseRuleD st)
    pure (ConstantInfo.recInfo (← parseCVD st r.cv)
      (r.numParams + r.numMotives + r.numMinors + r.numIndices)
      (r.numParams + r.numMotives + r.numMinors) rules)
  let block := types ++ ctors ++ recs
  -- the projection rewrite's owner table (the export's own shape
  -- data: index/constructor counts, recursion flag, motive/minor
  -- counts)
  let st ← registerProjOwners st tys cts rcs block
  -- **EVERY BLOCK IS AN `indDecl`** (task #293): the basis-pin match
  -- that used to stand here — a name pre-filter (task #215) and then
  -- `canonEqList` against the five pinned blocks — is
  -- `preparePrelude`'s (`ConLeche/Frontend/Prepare.lean`), which
  -- retags a matching block to its `basisDecl` kind before the fold
  -- sees it.  A block under a pinned name that does NOT match keeps
  -- its `indDecl` form and is rejected by the fold's reserved-name
  -- check, exactly as before.
  --
  -- THE IN-PROCESS MODELLER (task #200; the ONLY model source
  -- since task #207, and since task #219 the only one there IS —
  -- a stream `_model` record is an ordinary declaration and is
  -- never consulted): a mutual or nested block gets its `_model`
  -- family generated here and pushed ahead of it; the block then
  -- installs through the modeled route.  A generator decline is
  -- the run's decline, naming the class (the residual: infinitary
  -- nesting, a `Prop` block with a large eliminator).
  let T0 := (block.head?.map (·.name)).getD .anonymous
  let b ← blockRecOf st tys cts rcs
  let st :=
    let m := st.indBlocks
    let st := { st with indBlocks := {} }
    { st with indBlocks := b.types.foldl (fun m t => m.insert t.cv.name b) m }
  if st.inModel && InModel.wants b then
    let ctx : InModel.Ctx :=
      ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0, fun n => st.indBlocks[n]?⟩
    match InModel.generate ctx b with
    | .error why =>
      if st.inModelCensus then
        return .inl (pushDecl { st with inModelDeclined := st.inModelDeclined.push (T0, why) }
          (.indDecl block nPd))
      else
        return .inr (.declined s!"in-process model of {T0}: {why}")
    | .ok gen =>
      -- a generated record is a declaration of the FOLD and not
      -- a record of the file (task #219): booked here, so the
      -- verdict line reports the file's own count
      let st1 := pushGenList st gen T0
      let st1 := { st1 with
        inModelled := st1.inModelled.push T0,
        inModelGen := st1.inModelGen.push (st1.indCount - 1, gen.toArray) }
      return .inl (pushDecl st1 (.indDecl block nPd))
  else
    return .inl (pushDecl st (.indDecl block nPd))

/-- The record's own semantics: the declaration kinds, producing
`Declaration` records.  Every branch, guard and error string is the one the
`Lean.Json` reader this replaced had (task #256); only the reads
changed, from key lookups in a DOM to fields of a syntax record. -/
def processLineCoreD (st : StateD) (d : DeclRec) : M (StateD ⊕ RecordVerdict) := do
  match d with
  | .ax cvr isUnsafe =>
    let cvp ← parseCVD st cvr
    if isUnsafe then
      return .inr (.declined "unsafe axiom")
    -- **`Quot.sound` is the FOLD's** (task #293): the axiom record is
    -- forwarded like any other, and the fold compares it with the
    -- pinned soundness axiom (`checkDecl`'s `.axiomDecl` arm) — the
    -- decline on a mismatch was the parser's and is not any more.
    return .inl (pushDecl st (.axiomDecl cvp))
  | .defn cvr value hints safety =>
    let cvp ← parseCVD st cvr
    match safety with
    | "safe" =>
      let vl ← getDeclD st value
      let h : ReducibilityHint := match hints with
        | .«abbrev» => .«abbrev»
        | .«opaque» => .«opaque»
        | .regular n => .regular n
      -- the projection-function rewrite (2026-09-06): a non-direct
      -- structure-like's `fun p⃗ self => .proj T i self` becomes the
      -- recursor application, at the field sort the artifact names
      match projRewriteD st cvp vl with
      | some vl' =>
        let st := pushDecl st (.defnDecl cvp vl' h)
        return .inl { st with projRewrites := st.projRewrites.push cvp.name }
      | none =>
        return .inl (pushDecl st (.defnDecl cvp vl h))
    | s => return .inr (.declined s!"definition with safety '{s}'")
  | .thm cvr value =>
    let cvp ← parseCVD st cvr
    let vl ← getDeclD st value
    -- a proof field's projection function is exported as a theorem
    -- (the elaborator's choice for a `Prop`-valued field): the same
    -- rewrite applies (2026-09-06)
    match projRewriteD st cvp vl with
    | some vl' =>
      let st := pushDecl st (.thmDecl cvp vl')
      return .inl { st with projRewrites := st.projRewrites.push cvp.name }
    | none =>
      return .inl (pushDecl st (.thmDecl cvp vl))
  | .opaq cvr value isUnsafe =>
    let cvp ← parseCVD st cvr
    if isUnsafe then
      return .inr (.declined "unsafe opaque declaration")
    let vl ← getDeclD st value
    return .inl (pushDecl st (.opaqueDecl cvp vl))
  | .quot cvr kind =>
    -- **ONE RECORD PER `#QUOT` LINE** (task #293): the file declares
    -- the quotient package as four records, and the decoder emits four
    -- — the constant as the file declares it, at the kind the file
    -- declares it at.  The comparison with the pinned block
    -- (`preparePrelude`, which retags a matching record to
    -- `basisDecl .quotK`) and the decline on a mismatch (the fold's
    -- `.quotDecl` arm) are not the parser's any more.
    let cv ← parseCVD st cvr
    let qk ← match kind with
      | "type" => pure QuotKind.type
      | "ctor" => pure QuotKind.ctor
      | "lift" => pure QuotKind.lift
      | "ind" => pure QuotKind.ind
      | k => throw s!"unknown quotient kind '{k}'"
    return .inl (pushDecl st (.quotDecl qk cv))
  | .ind tys cts rcs =>
    let st := { st with indCount := st.indCount + 1 }
    match ← validateIndD st tys cts rcs with
    | .inl v => pure (.inr v)
    | .inr (cts, nPd) => installIndD st tys cts rcs nPd

/-- A declaration record.  **`sorryAx` is the FOLD's** (user ruling):
the parse forwards every declaration record, the `sorryAx` axiom record
included — the fold checks its type, installs nothing for it, and
declines at the first record that USES the name
(`ConLeche/Kernel/Checker.lean`'s `.axiomDecl` arm, `unknownConstError`
and `unresolvedConstsError`).  What used to stand here was a read-only
taint pre-scan (`declRecordScanD`) that dropped the axiom record
without even parsing its type and skipped every declaration reaching
it, transitively, with the driver turning a non-empty skip list into a
decline at the END of the run.  The verdict was the same; the position
was not, and the parser owned a semantic decision. -/
def applyDeclD (st : StateD) (d : DeclRec) : M (StateD ⊕ RecordVerdict) :=
  processLineCoreD st d

/-- **The semantic layer**: one scanned line applied to the parse
state.  This is what the `Lean.Json`-based `processLineD` was, with
the DOM key lookups replaced by the fields of the syntax record the
byte recogniser produced (`ConLeche/Frontend/Scan/Fast.lean`, task
#256); the index resolution, the smart constructors, the projection
rewrite and the in-process modeller are unchanged. -/
def applyLine (st : StateD) (r : LineRec) : M (StateD ⊕ RecordVerdict) :=
  match r with
  | .expr i e => do pure (.inl (← parseExprEntryD st i e))
  | .name i n => do pure (.inl (← parseNameEntryD st i n))
  | .level i l => do pure (.inl (← parseLevelEntryD st i l))
  | .decl d => applyDeclD st d
  | .header => pure (.inl st)
  | .blank => pure (.inl st)

/-! ## The line feed and the drivers -/

/-- The direct parse result: the declarations over `Expr`, and the
parse's receipts.  No arena. -/
structure ParseResultD where
  /-- the FILE's declaration records, in the file's order, plus the
  records the in-process modeller generated (task #293: the prelude,
  the dedupe and the ground hoist are `preparePrelude`'s) -/
  decls : Array Declaration
  /-- projection functions rewritten to recursor form (2026-09-06) -/
  projRewrites : Array Name := #[]
  /-- the blocks modelled in-process (task #200), in stream order -/
  inModelled : Array Name := #[]
  /-- how many of `decls` the in-process modeller generated, and which
  block each of them models (task #219): the driver subtracts the count
  from its headline number — a generated record is a declaration of the
  fold, never a record of the file — and names the block when one of
  them is the record that fails -/
  genRecords : Nat := 0
  genOwner : Std.HashMap Name Name := {}
  /-- the in-process modeller's generated records per block, keyed by
  the block's ordinal among the stream's `inductive` records (for the
  debug dump only) -/
  inModelGen : Array (Nat × Array Declaration) := #[]
  /-- the census's declines (block, reason) -/
  inModelDeclined : Array (Name × String) := #[]

/-- The initial parse state (task #293: there is no prelude here any
more — the parse starts from the file's first record). -/
def StateD.init (inModel : Bool) (census : Bool := false) : StateD :=
  { inModel, inModelCensus := census }

/-- The result: the file's records, in the file's order. -/
def ParseResultD.ofState (st : StateD) : ParseResultD :=
  ⟨st.decls, st.projRewrites, st.inModelled,
   st.genRecords, st.genOwner, st.inModelGen, st.inModelDeclined⟩

/-- Scan and apply the LAST line of a stream — the one no newline
ends.  A syntactic failure is reported at its offset in the line. -/
def applyFinalLine (st : StateD) (b : @& ByteArray) (i : USize)
    (lineNo : Nat) : Except (CheckError × Nat) StateD :=
  match scanLineSpec b i with
  | .err e => .error (.internal (ScanErr.render ⟨e.offset - i.toNat, e.what⟩), lineNo)
  | .ok r _ =>
    match applyLine st r with
    | .error msg => .error (.internal msg, lineNo)
    | .ok (.inr v) => .error (v.toError, lineNo)
    | .ok (.inl st) => .ok st

/-- Every COMPLETE line of the chunk from `i`, applied in order: the
state, the line count, and where the incomplete tail begins (the
caller carries it into the next chunk).  A line the chunk cut in half
is told from a malformed one by whether the rest of the chunk holds a
newline at all — which is why a scan failure is not immediately an
error.  The loop's advance is the line, and the line reader never
returns a position at or before its own start, so the remaining byte
count is the termination measure.  The reader is `scanLineSpec`, the
naive reference; what runs is `scanLineFwd`, by the kernel-checked
equality the compiler substitutes (`ConLeche/Frontend/Scan/Equiv.lean`). -/
def feedChunk (st : StateD) (b : @& ByteArray) (i : USize) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × Nat × USize) :=
  if _h : i < b.usize then
    match scanLineSpec b i with
    | .err e =>
      if newlineFrom b i then
        .error (.internal (ScanErr.render ⟨e.offset - i.toNat, e.what⟩), lineNo + 1)
      else .ok (st, lineNo, i)
    | .ok r j =>
      -- `0` is the recogniser's "the buffer ended before a newline
      -- did": these bytes are an incomplete tail, not a line.  (A
      -- `USize` numeral must be COMPARED, not matched: a literal
      -- pattern of a machine-word type does not fire.)
      if j == 0 then .ok (st, lineNo, i)
      else
        match applyLine st r with
        | .error msg => .error (.internal msg, lineNo + 1)
        | .ok (.inr v) => .error (v.toError, lineNo + 1)
        | .ok (.inl st) =>
          if _hj : i < j then feedChunk st b j (lineNo + 1)
          else .error (.internal "the line scanner made no progress", lineNo + 1)
  else .ok (st, lineNo, i)
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i _h) (USize.lt_iff_toNat_lt.mp _hj)

/-- How many bytes the streaming driver asks for at a time. -/
def chunkSize : USize := 4 * 1024 * 1024

/-- **The size guard** (task #290).  The byte reader addresses its
buffer by machine word, so an input of `USize.size` bytes or more is
refused before any of it is read — the wholesale parse at its length,
the streaming parse when the bytes read so far would reach it.  No
real input comes near, and the guard is what lets the file theorem
(`ConLeche/Verify/Frontend/Lines.lean`, `parseExportD_eq_parseLines`)
stand without a size hypothesis: an accepted parse is a parse of a
buffer the word addresses. -/
def sizeError : CheckError × Nat :=
  (.notImplemented s!"an input of {USize.size} bytes or more", 0)

/-- **Wholesale direct parse of a byte buffer**: the whole input fed
at once, then the last line.  The specification the streaming parse is
proved equal to (`parseChunks_ok_parseBytes`,
`ConLeche/Verify/Frontend/Chunks.lean`). -/
def parseBytes (b : ByteArray) (inModel : Bool := true) (census : Bool := false) :
    Except (CheckError × Nat) ParseResultD := do
  if b.size ≥ USize.size then throw sizeError
  let (st, lineNo, tail) ← feedChunk (.init inModel census) b 0 0
  if tail < b.usize then
    let st ← applyFinalLine st b tail (lineNo + 1)
    return .ofState st
  else
    return .ofState st

/-- Wholesale direct parse of a string (the built-in prelude, tests
and small inputs): `parseBytes` of its UTF-8. -/
def parseExportD (contents : String)
    (inModel : Bool := true) (census : Bool := false) :
    Except (CheckError × Nat) ParseResultD :=
  parseBytes contents.toUTF8 inModel census

/-- **One chunk of the stream, applied** (task #290): the carried
incomplete tail is put in front of the new bytes, every complete line
of the buffer is fed, and the new incomplete tail is cut off for the
next chunk; `total` counts the bytes read before this chunk, for the
size guard.  This is the step the streaming reader takes
(`parseExportHandleD`), pure, so that `parseChunks` below — the same
step folded over a list of chunks — is exactly what the binary
computes and can be compared with the wholesale parse
(`parseChunks_eq_parseExportD`, `ConLeche/Verify/Frontend/Chunks.lean`). -/
def chunkStep (st : StateD) (carry : ByteArray) (lineNo total : Nat) (buf0 : ByteArray) :
    Except (CheckError × Nat) (StateD × ByteArray × Nat × Nat) :=
  if total + buf0.size ≥ USize.size then .error sizeError
  else
    let buf := if carry.isEmpty then buf0 else carry ++ buf0
    match feedChunk st buf 0 lineNo with
    | .error e => .error e
    | .ok (st, lineNo, tail) =>
      .ok (st, buf.extract tail.toNat buf.size, lineNo, total + buf0.size)

/-- The end of the stream: the carried tail, if any, is its last line. -/
def chunkFinish (st : StateD) (carry : ByteArray) (lineNo : Nat) :
    Except (CheckError × Nat) ParseResultD :=
  if carry.isEmpty then .ok (.ofState st)
  else
    match applyFinalLine st carry 0 (lineNo + 1) with
    | .error e => .error e
    | .ok st => .ok (.ofState st)

/-- The bytes of a list of chunks, in order: what the chunks a handle
hands out add up to (task #290). -/
def concatBytes : List ByteArray → ByteArray
  | [] => .empty
  | c :: cs => c ++ concatBytes cs

/-- **The streaming parse, purely** (task #290): `chunkStep` folded
over a list of chunks, `chunkFinish` at its end — what
`parseExportHandleD` does with the chunks its handle hands out, minus
the reads.  The list is folded whole (task #294): an empty chunk
contributes nothing and the fold goes on, so the parse of a list of
chunks is the parse of their concatenation, however it was cut
(`parseChunks_ok_parseBytes`, `ConLeche/Verify/Frontend/Chunks.lean`).
The loop's end-of-input decision — an empty READ is the end of the
file — is the loop's own, not the step's. -/
def parseChunks (chunks : List ByteArray) (inModel : Bool := true) (census : Bool := false) :
    Except (CheckError × Nat) ParseResultD :=
  go (.init inModel census) .empty 0 0 chunks
where
  go (st : StateD) (carry : ByteArray) (lineNo total : Nat) :
      List ByteArray → Except (CheckError × Nat) ParseResultD
    | [] => chunkFinish st carry lineNo
    | c :: cs =>
      match chunkStep st carry lineNo total c with
      | .error e => .error e
      | .ok (st, carry, lineNo, total) => go st carry lineNo total cs

/-- Streaming direct parse off an open handle.

The handle is read strictly forward, 4 MiB at a time, and is never
seeked, re-opened or asked for its size — so the source may be a
*pipe* just as well as a file (task #180: no scratch file at all,
anywhere; `Main.lean`).  It is a property to preserve: a seek or a
re-open here would silently re-introduce a temp file.

The unconsumed tail of a chunk — at most one incomplete line — is
carried into the next one, and `st` is threaded as a plain argument so
that the parse tables stay uniquely referenced across steps (task #78:
a handler that closes over the state holds it at RC 2 and every insert
inside copies it).  Each step is `chunkStep`, the end `chunkFinish`:
the loop is `parseChunks.go` with the reads interleaved (task #290),
stopping at the first empty read — the handle's end of file. -/
partial def parseExportHandleD (h : IO.FS.Handle)
    (inModel : Bool := true)
    (census : Bool := false) (chunk : USize := chunkSize) :
    IO (Except (CheckError × Nat) ParseResultD) := do
  let rec loop (st : StateD) (carry : ByteArray) (lineNo total : Nat) :
      IO (Except (CheckError × Nat) ParseResultD) := do
    let buf0 ← h.read chunk
    if buf0.isEmpty then
      return chunkFinish st carry lineNo
    else
      match chunkStep st carry lineNo total buf0 with
      | .error e => return .error e
      | .ok (st, carry, lineNo, total) => loop st carry lineNo total
  loop (.init inModel census) ByteArray.empty 0 0

/-- Streaming direct parse of a file. -/
def parseExportStreamD (path : System.FilePath)
    (inModel : Bool := true)
    (census : Bool := false) (chunk : USize := chunkSize) :
    IO (Except (CheckError × Nat) ParseResultD) := do
  parseExportHandleD (← IO.FS.Handle.mk path .read) inModel census chunk

end ConLeche.Frontend
