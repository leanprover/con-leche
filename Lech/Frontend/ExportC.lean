import Lech.Frontend.Export
import Lech.Frontend.ProjRec
import Lech.Frontend.InModel
import Lech.Frontend.NatOpGround
import Lech.Cached.ParsedC

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
the capstone consumes (`Lech/Verify/Cached/ParseC.lean`), replacing
`OfStoreC`'s index-memo lemma.

Every record kind, the taint policy, the size budget, the sentinels
and the error strings mirror `Lech/Frontend/Export.lean` clause by
clause — verdict identity with the arena path is the contract.  The
byte-level fast path (`fastParse`, shared with the arena parser — it
produces stream indices, not representations) plugs in through
direct-construction apply functions.

The frontend-budgeted tree consumers (basis/quotient pin matching,
inductive blocks) read their `Expr` trees through the memoized
the parsed slot itself — the same bounded-tree contract as
the arena's budgeted readback, without the arena.

**Three pure transformations of the parsed list happen here, below
the verified fold** — the fold sees their result as an ordinary list
of records, and the main theorem quantifies over that list:

* **the built-in prelude (task #191, `Lech/Frontend/Prelude.lean`)**:
  every parse is handed the checker's own prelude (the six pinned
  basis blocks and `Bool`), prepends its records, and drops a later
  stream copy of one of them when it is the same declaration
  (declining the run when it differs) — `pushDecl` below;
* **the ground hoist (task #191, `Lech/Frontend/NatOpGround.lean`)**:
  a pinned `Nat` operation's stream-certified structural ground is
  moved ahead of it when the stream declares it later;
* **the projection-function rewrite (2026-09-06,
  `Lech/Frontend/ProjRec.lean`)**, the one surface rewrite this
  parse performs on a definition record: a projection function
`fun p⃗ self => .proj T i self` of a structure-like owner the direct
install does not serve is replaced, before it reaches the checker, by
the recursor application the module documents.  Three bookkeeping
tables feed it — the owners of every parsed inductive block
(`projOwners`), the field sorts read off the preprocessor's
`T._model.proj_i.iota` artifacts (`projLevels`), and whether the
`PUnit` basis block has been seen (the constant motives need it).
-/

namespace Lech.Frontend

open Lean (Json)
open Lech
open Lech.Cached (ExprC ConstantValC DeclC)

private abbrev M := Except String

/-! ## The built-in prelude (task #191)

The checker's own little prelude — the pinned basis blocks and the
`Bool` block, the order-sensitive ground of the pin-certified `Nat`
operations (`Lech/PinGen/Prelude.lean`) — is a parsed stream of its
own (`Lech/Frontend/Prelude.lean`) that every parse PREPENDS to its
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
private def _root_.Lech.Cached.DeclC.asInfo? : DeclC → Option ConstantInfo
  | .axiomDecl cv => some (.axiomInfo ⟨cv.name, cv.levelParams, cv.type⟩)
  | .defnDecl cv v h => some (.defnInfo ⟨cv.name, cv.levelParams, cv.type⟩ v h)
  | .thmDecl cv v => some (.thmInfo ⟨cv.name, cv.levelParams, cv.type⟩ v)
  | .opaqueDecl cv v => some (.defnInfo ⟨cv.name, cv.levelParams, cv.type⟩ v .opaque)
  | _ => none

/-- Two parsed records are the same declaration: same kind, and equal
up to the basis-matching canonical form (`ConstantInfo.canon`). -/
def _root_.Lech.Cached.DeclC.sameCanon : DeclC → DeclC → Bool
  | .basisDecl k, .basisDecl k' => k == k'
  | .indDecl b, .indDecl b' =>
    b.map ConstantInfo.canon == b'.map ConstantInfo.canon
  | .opaqueDecl .., .defnDecl .. => false
  | .defnDecl .., .opaqueDecl .. => false
  | a, b =>
    match a.asInfo?, b.asInfo? with
    | some x, some y => ConstantInfo.canon x == ConstantInfo.canon y
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
  sizes : Std.HashMap Nat Nat := {}
  /-- structure-like owners the projection rewrite serves, by type
  name (`Lech/Frontend/ProjRec.lean`) -/
  projOwners : Std.HashMap Name ProjRecOwner := {}
  /-- field sorts, by artifact iota name `T._model.proj_i.iota` -/
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
  reads them, and its "does the stream carry a model for this block"
  test looks up `T._model` here (task #200) -/
  constTypes : Std.HashMap Name (List Name × ExprC) := {}
  /-- the definitional heights of the definitions pushed so far (the
  hints of the generated definitions are computed from them, task #200) -/
  heights : Std.HashMap Name Nat := {}
  /-- in-process modelling of mutual/nested blocks is on (task #200;
  `LECH_INMODEL=0` turns it off) -/
  inModel : Bool := true
  /-- the blocks modelled in-process, in stream order (for the receipt
  and the route trace) -/
  inModelled : Array Name := #[]
  /-- for the debug dump (`LECH_INMODEL_DUMP`): per modelled block, its
  ordinal among the stream's `inductive` records and the generated
  records -/
  inModelGen : Array (Nat × Array DeclC) := #[]
  /-- the number of `inductive` records seen so far -/
  indCount : Nat := 0
  /-- the parsed inductive blocks, by member type name (the in-process
  modeller's nested rung reads a container's shape off it) -/
  indBlocks : Std.HashMap Name InModel.BlockRec := {}
  /-- CENSUS mode (`LECH_INMODEL_CENSUS=1`): a generator decline is
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

/-- Is the record budgeted for the tree consumers?  The prelude
comparison walks the parsed tree (`ConstantInfo.canon`), so a record
under a prelude name is budgeted like a basis block. -/
private def StateD.budgetedD (st : StateD) (n : Name) : Bool :=
  budgetedName n || st.prelude.byName.contains n

/-- Record a pushed declaration's constants in the declaration table
(`constTypes`, `heights`; task #200). -/
private def noteDecl (st : StateD) (d : DeclC) : StateD :=
  let cvs : List (Name × List Name × ExprC × Option Nat) := match d with
    | .axiomDecl cv => [(cv.name, cv.levelParams, cv.type, none)]
    | .defnDecl cv _ h => [(cv.name, cv.levelParams, cv.type, some (InModel.hintHeight h))]
    | .thmDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
    | .opaqueDecl cv _ => [(cv.name, cv.levelParams, cv.type, none)]
    | .basisDecl k => k.decls.map fun ci =>
      (ci.toConstantVal.name, ci.toConstantVal.levelParams, ci.toConstantVal.type, none)
    | .indDecl block => block.map fun ci =>
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
private def pushDecl (st : StateD) (d : DeclC) : StateD ⊕ String :=
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

private def StateD.name (st : StateD) (i : Nat) : M Name :=
  match st.names[i]? with
  | some n => pure n
  | none => throw s!"undefined name index {i}"

private def StateD.level (st : StateD) (i : Nat) : M Level :=
  match st.levels[i]? with
  | some l => pure l
  | none => throw s!"undefined level index {i}"

private def StateD.expr (st : StateD) (i : Nat) : M ExprC :=
  match st.exprs[i]? with
  | some e => pure e
  | none => throw s!"undefined expr index {i}"

private def getNameD (st : StateD) (j : Json) (key : String) : M Name := do
  st.name (← getIdx j key)

private def getExprD (st : StateD) (j : Json) (key : String) : M ExprC := do
  st.expr (← getIdx j key)

/-- Declaration-level expression lookup (twin of `getDeclEIdx'`):
taint sentinel, then the tree-size budget when `budgeted`, then the
table read. -/
private def getDeclD (st : StateD) (j : Json) (key : String)
    (budgeted : Bool) : M ExprC := do
  let i ← getIdx j key
  if st.tainted[i]?.isSome then
    throw taintSentinel
  if budgeted ∧ (st.sizes[i]?.getD 1) ≥ declTreeSizeBudget then
    throw sizeSentinel
  st.expr i

/-- Declaration-level *tree* lookup for the bounded consumers (twin of
`getDeclExpr'`): budgeted; since task #172 B3a there is one type, so
the "tree" is the parsed node itself. -/
private def getDeclExprD (st : StateD) (j : Json) (key : String) : M Expr := do
  getDeclD st j key (budgeted := true)

/-- Twin of `parsePw` over the direct name table. -/
private def parsePwD (st : StateD) (j : Json) : M PropWhen := do
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
private def parseNameEntryD (st : StateD) (j : Json) (i : Nat) : M StateD := do
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
private def parseLevelEntryD (st : StateD) (j : Json) (i : Nat) : M StateD := do
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
private def parseExprEntryD (st : StateD) (j : Json) (i : Nat) : M StateD := do
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
    else if let .ok v := j.getObjVal? "lam" then do
      parseBinderInfo v
      pure (ExprC.mkLam (← getNameD st v "name")
        (← getExprD st v "type") (← getExprD st v "body")
        ⟨.default, ← parsePwD st v⟩, none)
    else if let .ok v := j.getObjVal? "forallE" then do
      parseBinderInfo v
      pure (ExprC.mkForallE (← getNameD st v "name")
        (← getExprD st v "type") (← getExprD st v "body")
        ⟨.default, ← parsePwD st v⟩, none)
    else if let .ok v := j.getObjVal? "letE" then do
      pure (ExprC.mkLetE (← getNameD st v "name")
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
  let size : Nat := min declTreeSizeBudget
    (cs.foldl (fun acc c => acc + (st.sizes[c]?.getD 1)) 1)
  let st := { st with exprs := st.exprs.insert i e }
  let st := if size > 1 then
    let m := st.sizes
    let st := { st with sizes := {} }
    { st with sizes := m.insert i size }
  else st
  if let some root := taint then
    let t := st.tainted
    let st := { st with tainted := {} }
    pure { st with tainted := t.insert i root }
  else
    pure st

/-! ## Declaration records -/

/-- Twin of `parseConstantValP`: the type stays `ExprC`. -/
private def parseConstantValD (st : StateD) (v : Json) (budgeted : Bool) :
    M ConstantValC := do
  let name ← getNameD st v "name"
  let ty ← getDeclD st v "type" (budgeted || st.budgetedD name)
  pure { name := name
         levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
         type := ty }

/-- Twin of `parseConstantVal` (tree form, the bounded consumers). -/
private def parseConstantValTD (st : StateD) (v : Json) : M ConstantVal := do
  pure {
    name := ← getNameD st v "name"
    levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
    type := ← getDeclExprD st v "type"
  }

/-- The projection-function rewrite at a definition record
(`Lech/Frontend/ProjRec.lean`): the value is `fun p⃗ self => .proj T i
self` for a recorded owner `T`, the field's sort is on record from the
artifact, `PUnit` is available, and the definition's level parameters
are the block's.  `none` = leave the record as parsed. -/
private def projRewriteD (st : StateD) (cv : ConstantValC) (vl : ExprC) :
    Option ExprC := do
  let .proj T i (.bvar 0) := lamBody vl | none
  let o ← st.projOwners[T]?
  guard st.punitSeen
  guard (cv.levelParams == o.lps)
  let l ← st.projLevels[projIotaName T i]?
  projRecValue o l cv.type vl i

/-- An artifact `T._model.proj_i.iota` names the field's sort in its
`Eq` level: recorded for the projection rewrite (stream theorems and
the in-process modeller's alike). -/
private def noteProjIota (st : StateD) (cvp : ConstantValC) : StateD :=
  if isProjIotaName cvp.name then
    match projIotaLevel cvp.type with
    | some l =>
      let m := st.projLevels
      let st := { st with projLevels := {} }
      { st with projLevels := m.insert cvp.name l }
    | none => st
  else st

/-- Push one record the in-process modeller generated (task #200):
`pushDecl`, plus the projection-iota registration a stream theorem
gets. -/
private def pushGenD (st : StateD) (d : DeclC) : StateD ⊕ String :=
  match d with
  | .thmDecl cv _ => pushDecl (noteProjIota st cv) d
  | _ => pushDecl st d

/-- The export's shape data of an inductive record, for the in-process
modeller (task #200). -/
private def blockRecOf (st : StateD) (v : Json) : M InModel.BlockRec := do
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
private def processLineCoreD (st : StateD) (j : Json)
    (modeled : Bool := false) : M (StateD ⊕ String) := do
  if let .ok v := j.getObjVal? "in" then
    return .inl (← parseNameEntryD st j (← v.getNat?))
  else if let .ok v := j.getObjVal? "il" then
    return .inl (← parseLevelEntryD st j (← v.getNat?))
  else if let .ok v := j.getObjVal? "ie" then
    return .inl (← parseExprEntryD st j (← v.getNat?))
  else if (j.getObjVal? "meta").isOk then
    return .inl st
  else if let .ok v := j.getObjVal? "axiom" then
    let cvp ← parseConstantValD st v (budgeted := true)
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe axiom"
    if cvp.name = quotSoundName then
      let cv ← parseConstantValTD st v
      if ConstantInfo.canon (.axiomInfo cv) =
          ConstantInfo.canon (quotBasis.getD 4 (.axiomInfo default)) then
        return .inl st
      else
        return .inr "quotient soundness axiom mismatch"
    return pushDecl st (.axiomDecl cvp)
  else if let .ok v := j.getObjVal? "def" then
    let cvp ← parseConstantValD st v (budgeted := false)
    match (← (← v.getObjVal? "safety").getStr?) with
    | "safe" =>
      let vl ← getDeclD st v "value" (st.budgetedD cvp.name)
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
    let cvp ← parseConstantValD st v (budgeted := false)
    let vl ← getDeclD st v "value" (st.budgetedD cvp.name)
    -- an artifact `T._model.proj_i.iota` names the field's sort in its
    -- `Eq` level: recorded for the projection rewrite
    let st := noteProjIota st cvp
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
    let cvp ← parseConstantValD st v (budgeted := false)
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe opaque declaration"
    let vl ← getDeclD st v "value" (st.budgetedD cvp.name)
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
    if (ConstantInfo.canon (.axiomInfo cv)).toConstantVal =
        (ConstantInfo.canon pin).toConstantVal then
      if slot = 0 then
        return pushDecl st (.basisDecl .quotK)
      else
        return .inl st
    else
      return .inr "quotient declaration mismatch"
  else if let .ok v := j.getObjVal? "inductive" then
    let st := { st with indCount := st.indCount + 1 }
    let types ← (← (← v.getObjVal? "types").getArr?).mapM fun t => do
      if (← (← t.getObjVal? "isUnsafe").getBool?) then throw "unsafe inductive"
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
    let blockC := block.map ConstantInfo.canon
    if blockC = BasisKind.eqK.decls.map ConstantInfo.canon then
      return pushDecl st (.basisDecl .eqK)
    else if blockC = BasisKind.natK.decls.map ConstantInfo.canon then
      return pushDecl st (.basisDecl .natK)
    else if blockC = BasisKind.punitK.decls.map ConstantInfo.canon then
      return pushDecl { st with punitSeen := true } (.basisDecl .punitK)
    else if blockC = BasisKind.emptyK.decls.map ConstantInfo.canon then
      return pushDecl st (.basisDecl .emptyK)
    else if blockC = BasisKind.falseK.decls.map ConstantInfo.canon then
      return pushDecl st (.basisDecl .falseK)
    else
      if modeled then
        -- THE IN-PROCESS MODELLER (task #200): a mutual or nested block
        -- the stream carries no model for gets its `_model` family
        -- generated here and pushed ahead of it; the block then
        -- installs through the modeled route as a preprocessed one
        -- does.  A generator decline is the run's decline, naming the
        -- reason (the residual that still needs `lech-preprocess`).
        let T0 := (block.head?.map (·.name)).getD .anonymous
        let b ← blockRecOf st v
        let st :=
          let m := st.indBlocks
          let st := { st with indBlocks := {} }
          { st with indBlocks := b.types.foldl (fun m t => m.insert t.cv.name b) m }
        if st.inModel && InModel.wants b &&
            !st.constTypes.contains (T0.str "_model") then
          let ctx : InModel.Ctx :=
            ⟨fun n => st.constTypes[n]?, fun n => st.heights.getD n 0, fun n => st.indBlocks[n]?⟩
          match InModel.generate ctx b with
          | .error why =>
            if st.inModelCensus then
              return pushDecl { st with inModelDeclined := st.inModelDeclined.push (T0, why) }
                (.indDecl block)
            else
              return .inr s!"in-process model of {T0}: {why}"
          | .ok gen =>
            let mut st1 := st
            for d in gen do
              match pushGenD st1 d with
              | .inl st' => st1 := st'
              | r => return r
            st1 := { st1 with
              inModelled := st1.inModelled.push T0,
              inModelGen := st1.inModelGen.push (st1.indCount - 1, gen.toArray) }
            return pushDecl st1 (.indDecl block)
        else
          return pushDecl st (.indDecl block)
      else
        -- alias every member to its `_model` counterpart; the member
        -- type is the parsed `ExprC` slot itself (no re-interning, no
        -- conversion), the alias head is a fresh `const` node
        let mut st := st
        for t in (← (← v.getObjVal? "types").getArr?) do
          match ← aliasMember st t with
          | .inl st' => st := st'
          | r => return r
        for c in (← (← v.getObjVal? "ctors").getArr?) do
          match ← aliasMember st c with
          | .inl st' => st := st'
          | r => return r
        for r in (← (← v.getObjVal? "recs").getArr?) do
          match ← aliasMember st r with
          | .inl st' => st := st'
          | r => return r
        return .inl st
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
  /-- One `T := T._model` alias definition from a block-member record:
  the type is the parsed slot (already `ExprC`), the value a fresh
  `const` at the member's own level parameters. -/
  aliasMember (st : StateD) (t : Json) : M (StateD ⊕ String) := do
    let name ← getNameD st t "name"
    let lps := (← (← getIdxs t "levelParams").mapM st.name).toList
    let ty ← getDeclD st t "type" (budgeted := true)
    let v := ExprC.mkConst (Name.str name "_model") (lps.map .param)
    let d : DeclC := .defnDecl ⟨name, lps, ty⟩ v .abbrev
    pure (pushDecl st d)

/-- Twin of `declRecordScan` (read-only pre-scan for the taint
policy). -/
private def declRecordScanD (st : StateD) (j : Json) :
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
private def processLineD (st : StateD) (j : Json)
    (modeled : Bool := false) : M (StateD ⊕ String) := do
  if let .ok v := j.getObjVal? "axiom" then
    let name ← getNameD st v "name"
    if toleratedAxiomNames.contains name then
      let m := st.taintedNames
      let st := { st with taintedNames := {} }
      return .inl { st with taintedNames := m.insert name name }
  if let some (names, idxs) ← declRecordScanD st j then
    if let some root := idxs.findSome? (fun i => st.tainted[i]?) then
      let m := st.taintedNames
      let sk := st.taintSkipped
      let st := { st with taintedNames := {}, taintSkipped := #[] }
      let m := names.foldl (fun m n => m.insert n root) m
      return .inl { st with
        taintedNames := m,
        taintSkipped := sk.push (names.headD .anonymous, root) }
  tryCatch (processLineCoreD st j modeled) fun e =>
    if e = taintSentinel then
      pure (.inr "declaration uses a skipped (non-pinned) axiom")
    else if e = sizeSentinel then
      pure (.inr "declaration's unshared tree size exceeds the frontend budget (heavily DAG-shared input; this record kind still materializes trees)")
    else throw e

/-! ## The byte fast path's direct apply functions -/

/-- Fast-path outcome over the direct state (see `FastRes`). -/
private inductive FastResD where
  | handled (r : Except String StateD)
  | fallback (st : StateD)

/-- Semantic phase for a hot `{"ie":…}` line, direct construction. -/
private def fastApplyIED (st : StateD) (i : Nat) (fn : FastNode) : FastResD :=
  let mk : Option (ExprC × List Nat) :=
    match fn with
    | .app f a => do
      let fe ← st.exprs[f]?
      let ae ← st.exprs[a]?
      pure (ExprC.mkApp fe ae, [f, a])
    | .binder isAll nm ty bd => do
      let nI ← st.names[nm]?
      let tI ← st.exprs[ty]?
      let bI ← st.exprs[bd]?
      pure (if isAll then (ExprC.mkForallE nI tI bI ⟨.default, .never⟩, [ty, bd])
            else (ExprC.mkLam nI tI bI ⟨.default, .never⟩, [ty, bd]))
    | .letE nm ty vl bd => do
      let nI ← st.names[nm]?
      let tI ← st.exprs[ty]?
      let vI ← st.exprs[vl]?
      let bI ← st.exprs[bd]?
      pure (ExprC.mkLetE nI tI vI bI, [ty, vl, bd])
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
      let size : Nat := min declTreeSizeBudget
        (cs.foldl (fun acc c => acc + (st.sizes[c]?.getD 1)) 1)
      let st := { st with exprs := st.exprs.insert i node }
      let st := if size > 1 then
        let m := st.sizes
        let st := { st with sizes := {} }
        { st with sizes := m.insert i size }
      else st
      if let some root := taint then
        let t := st.tainted
        let st := { st with tainted := {} }
        .handled (.ok { st with tainted := t.insert i root })
      else
        .handled (.ok st)

/-- Semantic phase for a hot `{"in":…,"str":…}` line. -/
private def fastApplyIND (st : StateD) (i pre : Nat) (s : String) : FastResD :=
  match st.names[pre]? with
  | none => .fallback st
  | some p =>
    .handled (.ok { st with names := st.names.insert i (Name.str p s) })

/-- The fast path over the direct state (shares `fastParse` with the
arena parser — the byte layer produces stream indices). -/
private def fastEntryD (st : StateD) (line : String) : FastResD :=
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
  (`Lech/Frontend/NatOpGround.lean`, task #191; names, for the
  driver's receipt) -/
  hoisted : Array Name := #[]
  /-- the blocks modelled in-process (task #200), in stream order -/
  inModelled : Array Name := #[]
  /-- the in-process modeller's generated records per block, keyed by
  the block's ordinal among the stream's `inductive` records (for the
  debug dump only) -/
  inModelGen : Array (Nat × Array DeclC) := #[]
  /-- the census's declines (block, reason) -/
  inModelDeclined : Array (Name × String) := #[]

/-- The initial parse state over a prelude: `PUnit` counts as seen for
the projection rewrite when the prelude installs it; the prelude's
constants seed the declaration table (task #200). -/
private def StateD.init (prelude : PreludeIx) (inModel : Bool) (census : Bool := false) : StateD :=
  prelude.decls.foldl noteDecl
    { prelude, punitSeen := prelude.basis.contains .punitK, inModel, inModelCensus := census }

/-- The result: the prelude's records, then the stream's with every
pinned operation's stream-certified ground hoisted ahead of it
(`hoistNatOpGround`). -/
private def ParseResultD.ofState (st : StateD) : ParseResultD :=
  let (decls, hoisted) := hoistNatOpGround st.decls
  ⟨st.prelude.decls ++ decls, st.taintSkipped, st.projRewrites,
   st.prelude.decls.size, st.preludeDropped, hoisted, st.inModelled, st.inModelGen,
   st.inModelDeclined⟩

/-- Twin of `feedLine`. -/
private def feedLineD (st : StateD) (line : String) (lineNo : Nat)
    (modeled : Bool) : Except FrontendError StateD :=
  if line.trimAscii.isEmpty then .ok st
  else
    match fastEntryD st line with
    | .handled (.ok st) => .ok st
    | .handled (.error msg) => .error (.parseError lineNo msg)
    | .fallback st =>
      match Json.parse line >>= (fun j => processLineD st j modeled) with
      | .error msg => .error (.parseError lineNo msg)
      | .ok (.inr what) => .error (.unsupported what)
      | .ok (.inl st) => .ok st

/-- Wholesale direct parse (tests and small inputs).  `prelude` is the
built-in prelude the result is prepended with and deduped against
(task #191; empty for the prelude's own parse). -/
def parseExportD (contents : String) (modeled : Bool := false)
    (prelude : PreludeIx := {}) (inModel : Bool := true) (census : Bool := false) :
    Except FrontendError ParseResultD := do
  let mut st : StateD := .init prelude inModel census
  let mut lineNo := 0
  for line in contents.splitToList (· == '\n') do
    lineNo := lineNo + 1
    st ← feedLineD st line lineNo modeled
  return .ofState st

/-- Streaming direct parse off an open handle (twin of
`parseExportStream`; explicit recursion so the tables stay uniquely
referenced across steps).

The handle is read strictly forward, one `getLine` at a time, and is
never seeked, re-opened or asked for its size — so the source may be a
*pipe* just as well as a file.  That is what lets the checker read the
preprocessor's stdout directly (task #180: no scratch file at all;
`Main.lean`), and it is a property to preserve: a seek or a re-open
here would silently re-introduce the temp file. -/
partial def parseExportHandleD (h : IO.FS.Handle)
    (modeled : Bool := false) (prelude : PreludeIx := {}) (inModel : Bool := true)
    (census : Bool := false) :
    IO (Except FrontendError ParseResultD) := do
  let rec loop (lineNo : Nat) (st : StateD) :
      IO (Except FrontendError ParseResultD) := do
    let raw ← h.getLine
    if raw.isEmpty then
      return .ok (.ofState st)
    let line := if raw.back == '\n' then (raw.dropEnd 1).copy else raw
    match feedLineD st line (lineNo + 1) modeled with
    | .error e => return .error e
    | .ok st => loop (lineNo + 1) st
  loop 0 (.init prelude inModel census)

/-- Streaming direct parse of a file. -/
def parseExportStreamD (path : System.FilePath)
    (modeled : Bool := false) (prelude : PreludeIx := {}) (inModel : Bool := true)
    (census : Bool := false) :
    IO (Except FrontendError ParseResultD) := do
  parseExportHandleD (← IO.FS.Handle.mk path .read) modeled prelude inModel census

end Lech.Frontend
