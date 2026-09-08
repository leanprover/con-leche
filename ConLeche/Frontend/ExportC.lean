module

public import ConLeche.Frontend.Export
public import ConLeche.Frontend.ProjRec
public import ConLeche.Frontend.InModel
public import ConLeche.Frontend.NatOpGround
public import ConLeche.Cached.ParsedC

@[expose] public section

/-!
# Direct-to-`ExprC` export parsing (task #171)

The user order: the cached pipeline parses the ndjson export
**directly into `ExprC`** — no parse arena, no `ofStore` conversion,
no interned detour.  The export's `ie`-indices *are* the sharing: the
format already externalizes exactly the DAG structure the arena
reconstructs, so the parse keeps a stream-index-keyed table of
`ExprC` values and a table hit is a shared node by reference.
Sharing is preserved structurally; the derived fields are computed
once per node by the smart constructors, which is also what makes
every parsed term well-formed **by construction** — the entry obligation
the capstone consumes (`ConLeche/Verify/Cached/ParseC.lean`), replacing
`OfStoreC`'s index-memo lemma.

Every record kind, the taint policy, the sentinels
and the error strings mirror `ConLeche/Frontend/Export.lean` clause by
clause — verdict identity with the arena path is the contract.  The
byte-level fast path (`fastParse`, shared with the arena parser — it
produces stream indices, not representations) plugs in through
direct-construction apply functions.

The pin-matching consumers (basis and quotient blocks) read the parsed
slot itself; the tree-size budget that used to bound them was retired
at task #215 (`ConLeche/Frontend/Export.lean`).

**Three pure transformations of the parsed list happen here, below
the verified fold** — the fold sees their result as an ordinary list
of records, and the main theorem quantifies over that list:

* **the built-in prelude (task #191, `ConLeche/Frontend/Prelude.lean`)**:
  every parse is handed the checker's own prelude (the six pinned
  basis blocks and `Bool`), prepends its records, and drops a later
  stream copy of one of them when it is the same declaration
  (declining the run when it differs) — `pushDecl` below;
* **the ground hoist (task #191, `ConLeche/Frontend/NatOpGround.lean`)**:
  a pinned `Nat` operation's stream-certified structural ground is
  moved ahead of it when the stream declares it later;
* **the projection-function rewrite (2026-09-06,
  `ConLeche/Frontend/ProjRec.lean`)**, the one surface rewrite this
  parse performs on a definition record: a projection function
`fun p⃗ self => .proj T i self` of a structure-like owner the direct
install does not serve is replaced, before it reaches the checker, by
the recursor application the module documents.  Three bookkeeping
tables feed it — the owners of every parsed inductive block
(`projOwners`), the field sorts read off the `T._model.proj_i.iota`
artifacts the in-process modeller GENERATES (`projLevels`; task #219:
the generated records are the only source, and the scan runs on them
alone), and whether the `PUnit` basis block has been seen (the
constant motives need it).
-/

namespace ConLeche.Frontend

open Lean (Json)
open ConLeche
open ConLeche.Cached (ExprC DeclC)


/-! ## The built-in prelude (task #191)

The checker's own little prelude — the pinned basis blocks and the
`Bool` block, the order-sensitive ground of the pin-certified `Nat`
operations (`ConLeche/PinGen/Prelude.lean`) — is a parsed stream of its
own (`ConLeche/Frontend/Prelude.lean`) that every parse PREPENDS to its
result, so the fold installs it first, unconditionally.  A later
stream record under a prelude name is compared with the prelude's
copy up to the basis-matching canonical form (`ConstantInfo.canon`:
binder names, binder infos and level-parameter names erased): the
same declaration is DROPPED (it is already installed), a different
one DECLINES the stream (exit 2, naming the declaration — the user's
word; note the contrast with the pinned basis blocks, whose
mismatching redefinitions keep REJECTING through the reserved-name
check, as before).  Basis blocks are matched by kind: the stream's
`Nat` record parses to `basisDecl .natK` exactly as before and is
dropped as the prelude's duplicate. -/

/-- The constant a definition-like record would store, for the canon
comparison (`opaqueDecl` is told apart from `defnDecl` by `sameCanon`'s
constructor test, not here). -/
def _root_.ConLeche.Cached.DeclC.asInfo? : DeclC → Option ConstantInfo
  | .axiomDecl cv => some (.axiomInfo ⟨cv.name, cv.levelParams, cv.type⟩)
  | .defnDecl cv v h => some (.defnInfo ⟨cv.name, cv.levelParams, cv.type⟩ v h)
  | .thmDecl cv v => some (.thmInfo ⟨cv.name, cv.levelParams, cv.type⟩ v)
  | .opaqueDecl cv v => some (.defnInfo ⟨cv.name, cv.levelParams, cv.type⟩ v .opaque)
  | _ => none

/-- Two parsed records are the same declaration: same kind, and equal
up to the basis-matching canonical form (`ConstantInfo.canon`). -/
def _root_.ConLeche.Cached.DeclC.sameCanon : DeclC → DeclC → Bool
  | .basisDecl k, .basisDecl k' => k == k'
  | .indDecl b nP, .indDecl b' nP' => nP == nP' && canonEqList b b'
  | .opaqueDecl .., .defnDecl .. => false
  | .defnDecl .., .opaqueDecl .. => false
  | a, b =>
    match a.asInfo?, b.asInfo? with
    | some x, some y => ConstantInfo.canonEq x y
    | _, _ => false

/-- The built-in prelude, indexed: its records in order, the
definition-like and inductive records by every name they declare, and
the basis blocks by kind. -/
structure PreludeIx where
  decls : Array DeclC := #[]
  byName : Std.HashMap Name DeclC := {}
  basis : List BasisKind := []

def PreludeIx.ofDecls (ds : Array DeclC) : PreludeIx :=
  ds.foldl (init := {}) fun ix d =>
    match d with
    | .basisDecl k => { ix with decls := ix.decls.push d, basis := k :: ix.basis }
    | _ => { ix with decls := ix.decls.push d,
                     byName := d.names.foldl (fun m n => m.insert n d) ix.byName }

/-! ## The direct parse state -/

/-- The direct parse state: stream-index-keyed tables of *values*
(names and levels as trees, expressions as `ExprC` — a table hit is a
shared node by reference), the parsed declarations as `DeclC`, and
the taint/size bookkeeping of the arena parser, unchanged (both are
keyed by stream indices, so they are representation-independent). -/
structure StateD where
  names : Std.HashMap Nat Name := .ofList [(0, .anonymous)]
  levels : Std.HashMap Nat Level := .ofList [(0, .zero)]
  exprs : Std.HashMap Nat ExprC := {}
  decls : Array DeclC := #[]
  tainted : Std.HashMap Nat Name := {}
  taintedNames : Std.HashMap Name Name := {}
  taintSkipped : Array (Name × Name) := #[]
  /-- structure-like owners the projection rewrite serves, by type
  name (`ConLeche/Frontend/ProjRec.lean`) -/
  projOwners : Std.HashMap Name ProjRecOwner := {}
  /-- field sorts, by artifact iota name `T._model.proj_i.iota` (the
  in-process modeller's own, and only those; task #219) -/
  projLevels : Std.HashMap Name Level := {}
  /-- the `PUnit` basis block has been parsed -/
  punitSeen : Bool := false
  /-- projection functions rewritten so far (names, for the driver's
  trace) -/
  projRewrites : Array Name := #[]
  /-- the built-in prelude this parse dedupes against (task #191) -/
  prelude : PreludeIx := {}
  /-- the declared types of every declaration pushed so far (the
  prelude's included), by name: the in-process modeller's sort inferer
  reads them (task #200) -/
  constTypes : Std.HashMap Name (List Name × ExprC) := {}
  /-- the definitional heights of the definitions pushed so far (the
  hints of the generated definitions are computed from them, task #200) -/
  heights : Std.HashMap Name Nat := {}
  /-- in-process modelling of mutual/nested blocks is on (task #200;
  `CON_LECHE_INMODEL=0` turns it off) -/
  inModel : Bool := true
  /-- the blocks modelled in-process, in stream order (for the receipt
  and the route trace) -/
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
  inModelGen : Array (Nat × Array DeclC) := #[]
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
  /-- stream records dropped as identical copies of prelude records:
  they count as accepted stream declarations (they ARE installed, from
  the prelude), so the driver's record count adds them back -/
  preludeDropped : Nat := 0
/-- Record a pushed declaration's constants in the declaration table
(`constTypes`, `heights`; task #200). -/
def noteDecl (st : StateD) (d : DeclC) : StateD :=
  let cvs : List (Name × List Name × ExprC × Option Nat) := match d with
    | .axiomDecl cv => [(cv.name, cv.levelParams, cv.type, none)]
    | .defnDecl cv _ h => [(cv.name, cv.levelParams, cv.type, some (InModel.hintHeight h))]
    | .thmDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
    | .opaqueDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
    | .basisDecl k => k.decls.map fun ci =>
      (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
    | .indDecl block _ => block.map fun ci =>
      (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
  let ct := st.constTypes
  let hs := st.heights
  let st := { st with constTypes := {}, heights := {} }
  let (ct, hs) := cvs.foldl (fun (ct, hs) (n, lps, ty, h) =>
    (ct.insert n (lps, ty), match h with | some h => hs.insert n h | none => hs)) (ct, hs)
  { st with constTypes := ct, heights := hs }

/-- **The prelude dedupe** (task #191), at every declaration push: a
basis block the prelude holds is dropped by kind; a record under a
prelude name is dropped when it is the same declaration
(`DeclC.sameCanon`) and declines the stream when it differs. -/
def pushDecl (st : StateD) (d : DeclC) : StateD ⊕ String :=
  match d with
  | .basisDecl k =>
    if st.prelude.basis.contains k then
      .inl { st with preludeDropped := st.preludeDropped + 1 }
    else .inl (noteDecl { st with decls := st.decls.push d } d)
  | _ =>
    match d.names.findSome? (fun n => (st.prelude.byName[n]?).map (n, ·)) with
    | none => .inl (noteDecl { st with decls := st.decls.push d } d)
    | some (n, p) =>
      if d.sameCanon p then
        .inl { st with preludeDropped := st.preludeDropped + 1 }
      else .inr (s!"declaration {n} differs from the checker's built-in " ++
        s!"prelude (the toolchain's own {n}, installed first)")

def StateD.name (st : StateD) (i : Nat) : M Name :=
  match st.names[i]? with
  | some n => pure n
  | none => throw s!"undefined name index {i}"

def StateD.level (st : StateD) (i : Nat) : M Level :=
  match st.levels[i]? with
  | some l => pure l
  | none => throw s!"undefined level index {i}"

def StateD.expr (st : StateD) (i : Nat) : M ExprC :=
  match st.exprs[i]? with
  | some e => pure e
  | none => throw s!"undefined expr index {i}"

def getNameD (st : StateD) (j : Json) (key : String) : M Name := do
  st.name (← getIdx j key)

def getExprD (st : StateD) (j : Json) (key : String) : M ExprC := do
  st.expr (← getIdx j key)

/-- Declaration-level expression lookup (twin of `getDeclEIdx'`): the
taint sentinel, then the table read.

The frontend tree-size budget that used to sit here was **retired at
task #215**: every consumer it bounded is now either name-selected (the
basis-pin match) or a memoized DAG walk (`Expr.renameConsts`,
`Expr.instantiate1`; `@[csimp]` in `ConLeche/Kernel/ExprOps.lean`), and
the adversarial DAG-tower fixtures in `tests/e2e` are the standing
gate in its place — a limit told a user "no", a fixture tells *us*
which walker regressed. -/
def getDeclD (st : StateD) (j : Json) (key : String) : M ExprC := do
  let i ← getIdx j key
  if st.tainted[i]?.isSome then
    throw taintSentinel
  st.expr i

/-- Declaration-level lookup for the inductive-block and quotient
readers (twin of `getDeclExpr'`); since task #172 B3a there is one
type, so the "tree" is the parsed node itself. -/
def getDeclExprD (st : StateD) (j : Json) (key : String) : M Expr := do
  getDeclD st j key

/-- Twin of `parsePw` over the direct name table. -/
def parsePwD (st : StateD) (j : Json) : M PropWhen := do
  match j.getObjVal? "pw" with
  | .error _ => pure .never
  | .ok v =>
    if let .ok s := v.getStr? then
      match s with
      | "never" => pure .never
      | _ => throw s!"unknown pw {s}"
    else if let .ok a := v.getArr? then
      pure (.ifAllZero (← a.toList.mapM (fun i => do st.name (← i.getNat?))))
    else
      throw "malformed pw field"

/-! ## Table entries -/

/-- Twin of `parseNameEntry`: the name value is built directly. -/
def parseNameEntryD (st : StateD) (j : Json) (i : Nat) : M StateD := do
  let n ← if let .ok v := j.getObjVal? "str" then do
      let p ← st.name (← getIdx v "pre")
      pure (Name.str p (← (← v.getObjVal? "str").getStr?))
    else if let .ok v := j.getObjVal? "num" then do
      let p ← st.name (← getIdx v "pre")
      pure (Name.num p (← (← v.getObjVal? "i").getNat?))
    else
      throw "malformed name entry"
  pure { st with names := st.names.insert i n }

/-- Twin of `parseLevelEntry`. -/
def parseLevelEntryD (st : StateD) (j : Json) (i : Nat) : M StateD := do
  let l ←
    if let .ok v := j.getObjVal? "succ" then
      pure (Level.succ (← st.level (← v.getNat?)))
    else if let .ok v := j.getObjVal? "max" then
      match ← (← v.getArr?).mapM (·.getNat?) with
      | #[a, b] => pure (Level.max (← st.level a) (← st.level b))
      | _ => throw "malformed max level"
    else if let .ok v := j.getObjVal? "imax" then
      match ← (← v.getArr?).mapM (·.getNat?) with
      | #[a, b] => pure (Level.imax (← st.level a) (← st.level b))
      | _ => throw "malformed imax level"
    else if let .ok v := j.getObjVal? "param" then
      pure (Level.param (← st.name (← v.getNat?)))
    else
      throw "malformed level entry"
  pure { st with levels := st.levels.insert i l }

/-- Twin of `parseExprEntry`: build the `ExprC` node from the
children's table values (the derived fields are the compiler's, task
#172 B3a), with the taint/size bookkeeping unchanged. -/
def parseExprEntryD (st : StateD) (j : Json) (i : Nat)
    : M StateD := do
  let (e, taintConst) ←
    if let .ok v := j.getObjVal? "bvar" then do
      pure (ExprC.mkBVar (← v.getNat?), none)
    else if let .ok v := j.getObjVal? "sort" then do
      pure (ExprC.mkSort (← st.level (← v.getNat?)), none)
    else if let .ok v := j.getObjVal? "const" then do
      let n ← getNameD st v "name"
      let us ← (← (← v.getObjVal? "us").getArr?).mapM
        (fun u => do st.level (← u.getNat?))
      let taintC : Option Name ←
        if st.taintedNames.isEmpty then pure none
        else do pure st.taintedNames[n]?
      pure (ExprC.mkConst n us.toList, taintC)
    else if let .ok v := j.getObjVal? "app" then do
      pure (ExprC.mkApp (← getExprD st v "fn") (← getExprD st v "arg"), none)
    -- Binder names are display data the official kernel's equality
    -- and hash ignore; ours are `.anonymous` on every parsed binder
    -- (task #203, beside the `.default` annotation of task #142), so
    -- `==` is α-equivalence downstream.  The `name` field is still
    -- required to be present and well-formed (`getIdx`), it is just
    -- not resolved.
    else if let .ok v := j.getObjVal? "lam" then do
      parseBinderInfo v
      let _ ← getIdx v "name"
      pure (ExprC.mkLam
        (← getExprD st v "type") (← getExprD st v "body")
        ⟨← parsePwD st v⟩, none)
    else if let .ok v := j.getObjVal? "forallE" then do
      parseBinderInfo v
      let _ ← getIdx v "name"
      pure (ExprC.mkForallE
        (← getExprD st v "type") (← getExprD st v "body")
        ⟨← parsePwD st v⟩, none)
    else if let .ok v := j.getObjVal? "letE" then do
      let _ ← getIdx v "name"
      pure (ExprC.mkLetE
        (← getExprD st v "type") (← getExprD st v "value")
        (← getExprD st v "body"), none)
    else if let .ok v := j.getObjVal? "proj" then do
      pure (ExprC.mkProj (← getNameD st v "typeName")
        (← (← v.getObjVal? "idx").getNat?) (← getExprD st v "struct"), none)
    else if let .ok v := j.getObjVal? "natVal" then
      match (← v.getStr?).toNat? with
      | some n => pure (ExprC.mkLit (.natVal n), none)
      | none => throw "malformed natVal literal"
    else if let .ok v := j.getObjVal? "strVal" then do
      pure (ExprC.mkLit (.strVal (← v.getStr?)), none)
    else
      throw "malformed or unsupported expr entry"
  let cs ← exprEntryChildren j
  let taint : Option Name :=
    taintConst <|> cs.findSome? (fun c => st.tainted[c]?)
  let st := { st with exprs := st.exprs.insert i e }
  if let some root := taint then
    let t := st.tainted
    let st := { st with tainted := {} }
    pure { st with tainted := t.insert i root }
  else
    pure st

/-! ## Declaration records -/

/-- Twin of `parseConstantValP`: the type stays `ExprC`. -/
def parseConstantValD (st : StateD) (v : Json) : M ConstantVal := do
  let name ← getNameD st v "name"
  let ty ← getDeclD st v "type"
  pure { name := name
         levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
         type := ty }

/-- Twin of `parseConstantVal` (tree form, the bounded consumers). -/
def parseConstantValTD (st : StateD) (v : Json) : M ConstantVal := do
  pure {
    name := ← getNameD st v "name"
    levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
    type := ← getDeclExprD st v "type"
  }

/-- The projection-function rewrite at a definition record
(`ConLeche/Frontend/ProjRec.lean`): the value is `fun p⃗ self => .proj T i
self` for a recorded owner `T`, the field's sort is on record from the
artifact, `PUnit` is available, and the definition's level parameters
are the block's.  `none` = leave the record as parsed. -/
def projRewriteD (st : StateD) (cv : ConstantVal) (vl : ExprC) :
    Option ExprC := do
  let .proj T i (.bvar 0) := lamBody vl | none
  let o ← st.projOwners[T]?
  guard st.punitSeen
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
def pushGenD (st : StateD) (d : DeclC) : StateD ⊕ String :=
  match d with
  | .thmDecl cv _ => pushDecl (noteProjIota st cv) d
  | _ => pushDecl st d

/-- Book a record the in-process modeller generated for block `T0`
(task #219): a declaration of the FOLD, never a record of the file, so
the driver's headline count subtracts it and a failure at it is
reported with the block it models. -/
def noteGen (st : StateD) (d : DeclC) (T0 : Name) : StateD :=
  let m := st.genOwner
  let st := { st with genOwner := {} }
  { st with genRecords := st.genRecords + 1,
            genOwner := d.names.foldl (fun m n => m.insert n T0) m }

/-- The export's shape data of an inductive record, for the in-process
modeller (task #200). -/
def blockRecOf (st : StateD) (v : Json) : M InModel.BlockRec := do
  let types ← (← (← v.getObjVal? "types").getArr?).toList.mapM fun t => do
    pure { cv := ← parseConstantValTD st t
           nP := ← (← t.getObjVal? "numParams").getNat?
           nIdx := ← (← t.getObjVal? "numIndices").getNat?
           ctors := (← (← getIdxs t "ctors").mapM st.name).toList
           isRec := ← (← t.getObjVal? "isRec").getBool?
           isReflexive := ← (← t.getObjVal? "isReflexive").getBool?
           numNested := ← (← t.getObjVal? "numNested").getNat? : InModel.IndTypeRec }
  let ctors ← (← (← v.getObjVal? "ctors").getArr?).toList.mapM fun c => do
    pure { cv := ← parseConstantValTD st c
           nP := ← (← c.getObjVal? "numParams").getNat?
           nF := ← (← c.getObjVal? "numFields").getNat? : InModel.IndCtorRec }
  let recs ← (← (← v.getObjVal? "recs").getArr?).toList.mapM fun r => do
    let rules ← (← (← r.getObjVal? "rules").getArr?).toList.mapM fun ru => do
      pure (RecRule.mk (← getNameD st ru "ctor")
        (← (← ru.getObjVal? "nfields").getNat?) 0 .inert
        (← getDeclExprD st ru "rhs"))
    pure { cv := ← parseConstantValTD st r
           nP := ← (← r.getObjVal? "numParams").getNat?
           nM := ← (← r.getObjVal? "numMotives").getNat?
           nm := ← (← r.getObjVal? "numMinors").getNat?
           nI := ← (← r.getObjVal? "numIndices").getNat?
           rules := rules : InModel.IndRecRec }
  pure ⟨types, ctors, recs⟩

/-- Twin of `processLineCore` over the direct state, producing `DeclC`
records.  Every branch, guard and error string mirrors the arena
parser's. -/
def processLineCoreD (st : StateD) (j : Json) :
    M (StateD ⊕ String) := do
  if let .ok v := j.getObjVal? "in" then
    return .inl (← parseNameEntryD st j (← v.getNat?))
  else if let .ok v := j.getObjVal? "il" then
    return .inl (← parseLevelEntryD st j (← v.getNat?))
  else if let .ok v := j.getObjVal? "ie" then
    return .inl (← parseExprEntryD st j (← v.getNat?))
  else if (j.getObjVal? "meta").isOk then
    return .inl st
  else if let .ok v := j.getObjVal? "axiom" then
    let cvp ← parseConstantValD st v
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe axiom"
    if cvp.name = quotSoundName then
      let cv ← parseConstantValTD st v
      if ConstantInfo.canonEq (.axiomInfo cv)
          (quotBasis.getD 4 (.axiomInfo default)) then
        return .inl st
      else
        return .inr "quotient soundness axiom mismatch"
    return pushDecl st (.axiomDecl cvp)
  else if let .ok v := j.getObjVal? "def" then
    let cvp ← parseConstantValD st v
    match (← (← v.getObjVal? "safety").getStr?) with
    | "safe" =>
      let vl ← getDeclD st v "value"
      let h ← parseHints v
      -- the projection-function rewrite (2026-09-06): a non-direct
      -- structure-like's `fun p⃗ self => .proj T i self` becomes the
      -- recursor application, at the field sort the artifact names
      match projRewriteD st cvp vl with
      | some vl' =>
        return (pushDecl st (.defnDecl cvp vl' h)).map
          (fun st => { st with projRewrites := st.projRewrites.push cvp.name }) id
      | none =>
        return pushDecl st (.defnDecl cvp vl h)
    | s => return .inr s!"definition with safety '{s}'"
  else if let .ok v := j.getObjVal? "thm" then
    let cvp ← parseConstantValD st v
    let vl ← getDeclD st v "value"
    -- a proof field's projection function is exported as a theorem
    -- (the elaborator's choice for a `Prop`-valued field): the same
    -- rewrite applies (2026-09-06)
    match projRewriteD st cvp vl with
    | some vl' =>
      return (pushDecl st (.thmDecl cvp vl')).map
        (fun st => { st with projRewrites := st.projRewrites.push cvp.name }) id
    | none =>
      return pushDecl st (.thmDecl cvp vl)
  else if let .ok v := j.getObjVal? "opaque" then
    let cvp ← parseConstantValD st v
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe opaque declaration"
    let vl ← getDeclD st v "value"
    return pushDecl st (.opaqueDecl cvp vl)
  else if let .ok v := j.getObjVal? "quot" then
    let cv ← parseConstantValTD st v
    let slot ← match (← (← v.getObjVal? "kind").getStr?) with
      | "type" => pure 0
      | "ctor" => pure 1
      | "lift" => pure 2
      | "ind" => pure 3
      | k => throw s!"unknown quotient kind '{k}'"
    let pin := (BasisKind.quotK.decls.getD slot (.axiomInfo default))
    -- the two records are compared at `toConstantVal`, which
    -- `ConstantInfo.canon_toConstantVal` identifies with
    -- `ConstantVal.canon` of each side
    if ConstantVal.canonEq cv pin.toConstantVal then
      if slot = 0 then
        return pushDecl st (.basisDecl .quotK)
      else
        return .inl st
    else
      return .inr "quotient declaration mismatch"
  else if let .ok v := j.getObjVal? "inductive" then
    let st := { st with indCount := st.indCount + 1 }
    let tys ← (← v.getObjVal? "types").getArr?
    -- TASK #217 (audit follow-up 6): an `unsafe inductive` is DECLINED,
    -- not an error.  The official kernel admits unsafe blocks (it skips
    -- positivity for them); we support no unsafe declaration at all, and
    -- unsafe axioms/opaques/definitions already decline positively
    -- (`:475`, `:518`, the `def` arm's safety branch).  The inductive
    -- path used to `throw`, which the driver reports as exit 3.
    if ← tys.anyM fun t => do (← t.getObjVal? "isUnsafe").getBool? then
      return .inr "unsafe inductive declaration"
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
    let nPs ← tys.mapM fun t => do (← t.getObjVal? "numParams").getNat?
    let nPd := nPs[0]?.getD 0
    unless nPs.all (· == nPd) do
      return .inr "inductive block whose type records disagree on numParams"
    let types ← tys.mapM fun t => do
      pure (ConstantInfo.indInfo (← parseConstantValTD st t) {})
    let ctors ← (← (← v.getObjVal? "ctors").getArr?).mapM fun c => do
      pure (ConstantInfo.ctorInfo (← parseConstantValTD st c)
        (← (← c.getObjVal? "numParams").getNat?)
        (← (← c.getObjVal? "numFields").getNat?))
    let recs ← (← (← v.getObjVal? "recs").getArr?).mapM fun r => do
      let rules ← (← (← r.getObjVal? "rules").getArr?).mapM fun ru => do
        pure (RecRule.mk (← getNameD st ru "ctor")
          (← (← ru.getObjVal? "nfields").getNat?) 0 .inert
          (← getDeclExprD st ru "rhs"))
      let nP ← (← r.getObjVal? "numParams").getNat?
      let nM ← (← r.getObjVal? "numMotives").getNat?
      let nm ← (← r.getObjVal? "numMinors").getNat?
      let ni ← (← r.getObjVal? "numIndices").getNat?
      pure (ConstantInfo.recInfo (← parseConstantValTD st r)
        (nP + nM + nm + ni) (nP + nM + nm) rules.toList)
    let block := types.toList ++ ctors.toList ++ recs.toList
    -- the projection rewrite's owner table (the export's own shape
    -- data: index/constructor counts, recursion flag, motive/minor
    -- counts)
    let st ← registerProjOwners st v block
    -- TASK #215 — the basis-pin NAME pre-filter.
    -- `ConstantInfo.canon` rebuilds the WHOLE block as an unshared tree
    -- (`Frontend.canonExpr`, unmemoized) just to compare it against five
    -- pins: on a heavily DAG-shared block that was the frontend's single
    -- largest cost, and the first row of task #213's retired budget audit
    -- (`ModularCurve.JZeroGoodReductionSpecialization_alt` is a
    -- 5 038-entry DAG that rebuilds as 78 394 796 nodes).
    -- `canon` renames only *level parameters* — it leaves every constant
    -- name alone — so a block can match a pin only when its members'
    -- names are the pin's, member for member.  Selecting the candidate
    -- by name first is a handful of `Name` comparisons, and no canonical
    -- form is built at all for any block that is not one of the five.
    -- Same verdict on every input; only the work changes.
    let blockNames := block.map (·.name)
    let pinHit : Option BasisKind :=
      ([BasisKind.eqK, .natK, .punitK, .emptyK, .falseK].find? fun k =>
          k.decls.map (·.name) == blockNames).filter fun k =>
        canonEqList block k.decls
    if let some k := pinHit then
      if k == BasisKind.punitK then
        return pushDecl { st with punitSeen := true } (.basisDecl k)
      else
        return pushDecl st (.basisDecl k)
    else
      -- THE IN-PROCESS MODELLER (task #200; the ONLY model source
      -- since task #207, and since task #219 the only one there IS —
      -- a stream `_model` record is an ordinary declaration and is
      -- never consulted): a mutual or nested block gets its `_model`
      -- family generated here and pushed ahead of it; the block then
      -- installs through the modeled route.  A generator decline is
      -- the run's decline, naming the class (the residual: infinitary
      -- nesting, a `Prop` block with a large eliminator).
      let T0 := (block.head?.map (·.name)).getD .anonymous
      let b ← blockRecOf st v
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
            return pushDecl { st with inModelDeclined := st.inModelDeclined.push (T0, why) }
              (.indDecl block nPd)
          else
            return .inr s!"in-process model of {T0}: {why}"
        | .ok gen =>
          let mut st1 := st
          for d in gen do
            let before := st1.decls.size
            match pushGenD st1 d with
            | .inl st' =>
              -- a generated record is a declaration of the FOLD and not
              -- a record of the file (task #219): booked here, so the
              -- verdict line reports the file's own count
              st1 := if st'.decls.size > before then noteGen st' d T0 else st'
            | r => return r
          st1 := { st1 with
            inModelled := st1.inModelled.push T0,
            inModelGen := st1.inModelGen.push (st1.indCount - 1, gen.toArray) }
          return pushDecl st1 (.indDecl block nPd)
      else
        return pushDecl st (.indDecl block nPd)
  else
    throw "unrecognized line"
where
  /-- Record the structure-like owners of a parsed block that the
  projection rewrite serves (`projRecOwners`). -/
  registerProjOwners (st : StateD) (v : Json) (block : List ConstantInfo) :
      M StateD := do
    let types ← (← (← v.getObjVal? "types").getArr?).toList.mapM fun t => do
      let cv ← parseConstantValTD st t
      pure (cv.name, cv.levelParams, cv.type,
        ← (← t.getObjVal? "numParams").getNat?,
        ← (← t.getObjVal? "numIndices").getNat?,
        (← (← getIdxs t "ctors").mapM st.name).toList,
        ← (← t.getObjVal? "isRec").getBool?)
    let ctors ← (← (← v.getObjVal? "ctors").getArr?).toList.mapM fun c => do
      let cv ← parseConstantValTD st c
      pure (cv.name, ← (← c.getObjVal? "numFields").getNat?, cv.type)
    let recs ← (← (← v.getObjVal? "recs").getArr?).toList.mapM fun r => do
      let cv ← parseConstantValTD st r
      pure (cv.name, cv.levelParams, cv.type,
        ← (← r.getObjVal? "numMotives").getNat?,
        ← (← r.getObjVal? "numMinors").getNat?)
    match projRecOwners block types ctors recs with
    | [] => pure st
    | owners =>
      let m := st.projOwners
      let st := { st with projOwners := {} }
      pure { st with projOwners := owners.foldl (fun m o => m.insert o.T o) m }

/-- Twin of `declRecordScan` (read-only pre-scan for the taint
policy). -/
def declRecordScanD (st : StateD) (j : Json) :
    M (Option (List Name × List Nat)) := do
  for k in ["axiom", "quot"] do
    if let .ok v := j.getObjVal? k then
      return some ([← getNameD st v "name"], [← getIdx v "type"])
  for k in ["def", "thm", "opaque"] do
    if let .ok v := j.getObjVal? k then
      return some ([← getNameD st v "name"],
        [← getIdx v "type", ← getIdx v "value"])
  if let .ok v := j.getObjVal? "inductive" then
    let mut names := []
    let mut idxs := []
    for key in ["types", "ctors", "recs"] do
      for t in (← (← v.getObjVal? key).getArr?) do
        names := (← getNameD st t "name") :: names
        idxs := (← getIdx t "type") :: idxs
    for r in (← (← v.getObjVal? "recs").getArr?) do
      for ru in (← (← r.getObjVal? "rules").getArr?) do
        idxs := (← getIdx ru "rhs") :: idxs
    return some (names.reverse, idxs)
  return none

/-- Twin of `processLine` (the taint policy). -/
def processLineD (st : StateD) (j : Json) :
    M (StateD ⊕ String) := do
  if let .ok v := j.getObjVal? "axiom" then
    let name ← getNameD st v "name"
    if toleratedAxiomNames.contains name then
      let m := st.taintedNames
      let st := { st with taintedNames := {} }
      return .inl { st with taintedNames := m.insert name name }
  let scan ← declRecordScanD st j
  if let some (names, idxs) := scan then
    if let some root := idxs.findSome? (fun i => st.tainted[i]?) then
      let m := st.taintedNames
      let sk := st.taintSkipped
      let st := { st with taintedNames := {}, taintSkipped := #[] }
      let m := names.foldl (fun m n => m.insert n root) m
      return .inl { st with
        taintedNames := m,
        taintSkipped := sk.push (names.headD .anonymous, root) }
  -- a `match`, not `tryCatch`: a capturing closure would be allocated
  -- on EVERY line rather than shared as a constant.  (A handler that
  -- mentions `st` also holds the parse tables at RC 2 across
  -- `processLineCoreD`, so every insert inside copies them — the
  -- task-#78 copy-on-write pathology, measured at +48 % on
  -- `init-core` when the retired size-decline message took the state.)
  match processLineCoreD st j with
  | .ok r => pure r
  | .error e =>
    if e = taintSentinel then
      pure (.inr "declaration uses a skipped (non-pinned) axiom")
    else throw e

/-! ## The byte fast path's direct apply functions -/

/-- Fast-path outcome over the direct state (see `FastRes`). -/
inductive FastResD where
  | handled (r : Except String StateD)
  | fallback (st : StateD)

/-- Semantic phase for a hot `{"ie":…}` line, direct construction. -/
def fastApplyIED (st : StateD) (i : Nat) (fn : FastNode)
    : FastResD :=
  let mk : Option (ExprC × List Nat) :=
    match fn with
    | .app f a => do
      let fe ← st.exprs[f]?
      let ae ← st.exprs[a]?
      pure (ExprC.mkApp fe ae, [f, a])
    -- binder names: `.anonymous`, as on the generic path (task #203);
    -- the name index is parsed, not resolved
    | .binder isAll _nm ty bd => do
      let tI ← st.exprs[ty]?
      let bI ← st.exprs[bd]?
      pure (if isAll then (ExprC.mkForallE tI bI ⟨.never⟩, [ty, bd])
            else (ExprC.mkLam tI bI ⟨.never⟩, [ty, bd]))
    | .letE _nm ty vl bd => do
      let tI ← st.exprs[ty]?
      let vI ← st.exprs[vl]?
      let bI ← st.exprs[bd]?
      pure (ExprC.mkLetE tI vI bI, [ty, vl, bd])
    | .const nm us => do
      let nI ← st.names[nm]?
      let usI ← us.mapM (st.levels[·]?)
      pure (ExprC.mkConst nI usI, [])
    | .bvar k => pure (ExprC.mkBVar k, [])
    | .sort l => do
      let lI ← st.levels[l]?
      pure (ExprC.mkSort lI, [])
  match mk with
  | none => .fallback st
  | some (node, cs) =>
    if (match fn with | .const .. => true | _ => false)
        && !st.taintedNames.isEmpty then .fallback st
    else
      let taint : Option Name := cs.findSome? (fun c => st.tainted[c]?)
      let st := { st with exprs := st.exprs.insert i node }
      if let some root := taint then
        let t := st.tainted
        let st := { st with tainted := {} }
        .handled (.ok { st with tainted := t.insert i root })
      else
        .handled (.ok st)

/-- Semantic phase for a hot `{"in":…,"str":…}` line. -/
def fastApplyIND (st : StateD) (i pre : Nat) (s : String) : FastResD :=
  match st.names[pre]? with
  | none => .fallback st
  | some p =>
    .handled (.ok { st with names := st.names.insert i (Name.str p s) })

/-- The fast path over the direct state (shares `fastParse` with the
arena parser — the byte layer produces stream indices). -/
def fastEntryD (st : StateD) (line : String) : FastResD :=
  match fastParse line.toUTF8 with
  | some (.ie i n) => fastApplyIED st i n
  | some (.inStr i pre s) => fastApplyIND st i pre s
  | none => .fallback st

/-! ## The line feed and the drivers -/

/-- The direct parse result: declarations over `ExprC` and the taint
skips.  No arena. -/
structure ParseResultD where
  /-- the built-in prelude's records first, then the stream's (task #191) -/
  decls : Array DeclC
  taintSkipped : Array (Name × Name)
  /-- projection functions rewritten to recursor form (2026-09-06) -/
  projRewrites : Array Name := #[]
  /-- how many of `decls` are the prelude's, and how many stream
  records were dropped as identical copies of prelude records: the
  stream's accepted-record count is
  `decls.size - preludeCount + preludeDropped` (task #191) -/
  preludeCount : Nat := 0
  preludeDropped : Nat := 0
  /-- the records moved ahead of a pinned `Nat` operation they ground
  (`ConLeche/Frontend/NatOpGround.lean`, task #191; names, for the
  driver's receipt) -/
  hoisted : Array Name := #[]
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
  inModelGen : Array (Nat × Array DeclC) := #[]
  /-- the census's declines (block, reason) -/
  inModelDeclined : Array (Name × String) := #[]

/-- The initial parse state over a prelude: `PUnit` counts as seen for
the projection rewrite when the prelude installs it; the prelude's
constants seed the declaration table (task #200). -/
def StateD.init (prelude : PreludeIx) (inModel : Bool)
    (census : Bool := false) : StateD :=
  prelude.decls.foldl noteDecl
    { prelude, punitSeen := prelude.basis.contains .punitK, inModel,
      inModelCensus := census }

/-- The result: the prelude's records, then the stream's with every
pinned operation's stream-certified ground hoisted ahead of it
(`hoistNatOpGround`). -/
def ParseResultD.ofState (st : StateD) : ParseResultD :=
  let (decls, hoisted) := hoistNatOpGround st.decls
  ⟨st.prelude.decls ++ decls, st.taintSkipped, st.projRewrites,
   st.prelude.decls.size, st.preludeDropped, hoisted, st.inModelled,
   st.genRecords, st.genOwner, st.inModelGen, st.inModelDeclined⟩

/-- Twin of `feedLine`. -/
def feedLineD (st : StateD) (line : String) (lineNo : Nat) :
    Except FrontendError StateD :=
  if line.trimAscii.isEmpty then .ok st
  else
    match fastEntryD st line with
    | .handled (.ok st) => .ok st
    | .handled (.error msg) => .error (.parseError lineNo msg)
    | .fallback st =>
      match Json.parse line >>= (fun j => processLineD st j) with
      | .error msg => .error (.parseError lineNo msg)
      | .ok (.inr what) => .error (.unsupported what)
      | .ok (.inl st) => .ok st

/-- Wholesale direct parse (tests and small inputs).  `prelude` is the
built-in prelude the result is prepended with and deduped against
(task #191; empty for the prelude's own parse). -/
def parseExportD (contents : String)
    (prelude : PreludeIx := {}) (inModel : Bool := true)
    (census : Bool := false) :
    Except FrontendError ParseResultD := do
  let mut st : StateD := .init prelude inModel census
  let mut lineNo := 0
  for line in contents.splitToList (· == '\n') do
    lineNo := lineNo + 1
    st ← feedLineD st line lineNo
  return .ofState st

/-- Streaming direct parse off an open handle (twin of
`parseExportStream`; explicit recursion so the tables stay uniquely
referenced across steps).

The handle is read strictly forward, one `getLine` at a time, and is
never seeked, re-opened or asked for its size — so the source may be a
*pipe* just as well as a file (task #180: no scratch file at all,
anywhere; `Main.lean`).  It is a property to preserve: a seek or a
re-open here would silently re-introduce a temp file. -/
partial def parseExportHandleD (h : IO.FS.Handle)
    (prelude : PreludeIx := {}) (inModel : Bool := true)
    (census : Bool := false) :
    IO (Except FrontendError ParseResultD) := do
  let rec loop (lineNo : Nat) (st : StateD) :
      IO (Except FrontendError ParseResultD) := do
    let raw ← h.getLine
    if raw.isEmpty then
      return .ok (.ofState st)
    let line := if raw.back == '\n' then (raw.dropEnd 1).copy else raw
    match feedLineD st line (lineNo + 1) with
    | .error e => return .error e
    | .ok st => loop (lineNo + 1) st
  loop 0 (.init prelude inModel census)

/-- Streaming direct parse of a file. -/
def parseExportStreamD (path : System.FilePath)
    (prelude : PreludeIx := {}) (inModel : Bool := true)
    (census : Bool := false) :
    IO (Except FrontendError ParseResultD) := do
  parseExportHandleD (← IO.FS.Handle.mk path .read) prelude inModel census

end ConLeche.Frontend
