import Setlec.Frontend.Export
import Setlec.Cached.ParsedC

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
every parsed term `WFc` **by construction** — the entry obligation
the capstone consumes (`Setlec/Verify/Cached/ParseC.lean`), replacing
`OfStoreC`'s index-memo lemma.

Every record kind, the taint policy, the size budget, the sentinels
and the error strings mirror `Setlec/Frontend/Export.lean` clause by
clause — verdict identity with the arena path is the contract.  The
byte-level fast path (`fastParse`, shared with the arena parser — it
produces stream indices, not representations) plugs in through
direct-construction apply functions.

The frontend-budgeted tree consumers (basis/quotient pin matching,
inductive blocks) read their `Expr` trees through the memoized
the parsed slot itself — the same bounded-tree contract as
the arena's budgeted readback, without the arena.
-/

namespace Setlec.Frontend

open Lean (Json)
open Setlec
open Setlec.Cached (ExprC ConstantValC DeclC WDeclC DeclCWFc)
open Setlec.Cached.ExprC (WExprC)

private abbrev M := Except String

/-! ## The direct parse state -/

/-- The direct parse state: stream-index-keyed tables of *values*
(names and levels as trees, expressions as `ExprC` — a table hit is a
shared node by reference), the parsed declarations as `DeclC`, and
the taint/size bookkeeping of the arena parser, unchanged (both are
keyed by stream indices, so they are representation-independent). -/
structure StateD where
  names : Std.HashMap Nat Name := .ofList [(0, .anonymous)]
  levels : Std.HashMap Nat Level := .ofList [(0, .zero)]
  exprs : Std.HashMap Nat WExprC := {}
  decls : Array WDeclC := #[]
  tainted : Std.HashMap Nat Name := {}
  taintedNames : Std.HashMap Name Name := {}
  taintSkipped : Array (Name × Name) := #[]
  sizes : Std.HashMap Nat Nat := {}

private def StateD.name (st : StateD) (i : Nat) : M Name :=
  match st.names[i]? with
  | some n => pure n
  | none => throw s!"undefined name index {i}"

private def StateD.level (st : StateD) (i : Nat) : M Level :=
  match st.levels[i]? with
  | some l => pure l
  | none => throw s!"undefined level index {i}"

private def StateD.expr (st : StateD) (i : Nat) : M WExprC :=
  match st.exprs[i]? with
  | some e => pure e
  | none => throw s!"undefined expr index {i}"

private def getNameD (st : StateD) (j : Json) (key : String) : M Name := do
  st.name (← getIdx j key)

private def getExprD (st : StateD) (j : Json) (key : String) : M WExprC := do
  st.expr (← getIdx j key)

/-- Declaration-level expression lookup (twin of `getDeclEIdx'`):
taint sentinel, then the tree-size budget when `budgeted`, then the
table read. -/
private def getDeclD (st : StateD) (j : Json) (key : String)
    (budgeted : Bool) : M WExprC := do
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
  let c ← getDeclD st j key (budgeted := true)
  pure c.1

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
children's table values through the smart constructors (derived
fields computed once; `WFc` by construction), with the taint/size
bookkeeping unchanged. -/
private def parseExprEntryD (st : StateD) (j : Json) (i : Nat) : M StateD := do
  let (e, taintConst) ←
    if let .ok v := j.getObjVal? "bvar" then do
      pure (ExprC.mkBVarW (← v.getNat?), none)
    else if let .ok v := j.getObjVal? "sort" then do
      pure (ExprC.mkSortW (← st.level (← v.getNat?)), none)
    else if let .ok v := j.getObjVal? "const" then do
      let n ← getNameD st v "name"
      let us ← (← (← v.getObjVal? "us").getArr?).mapM
        (fun u => do st.level (← u.getNat?))
      let taintC : Option Name ←
        if st.taintedNames.isEmpty then pure none
        else do pure st.taintedNames[n]?
      pure (ExprC.mkConstW n us.toList, taintC)
    else if let .ok v := j.getObjVal? "app" then do
      pure (ExprC.mkAppW (← getExprD st v "fn") (← getExprD st v "arg"), none)
    else if let .ok v := j.getObjVal? "lam" then do
      parseBinderInfo v
      pure (ExprC.mkLamW (← getNameD st v "name")
        (← getExprD st v "type") (← getExprD st v "body")
        ⟨.default, ← parsePwD st v⟩, none)
    else if let .ok v := j.getObjVal? "forallE" then do
      parseBinderInfo v
      pure (ExprC.mkForallEW (← getNameD st v "name")
        (← getExprD st v "type") (← getExprD st v "body")
        ⟨.default, ← parsePwD st v⟩, none)
    else if let .ok v := j.getObjVal? "letE" then do
      pure (ExprC.mkLetEW (← getNameD st v "name")
        (← getExprD st v "type") (← getExprD st v "value")
        (← getExprD st v "body"), none)
    else if let .ok v := j.getObjVal? "proj" then do
      pure (ExprC.mkProjW (← getNameD st v "typeName")
        (← (← v.getObjVal? "idx").getNat?) (← getExprD st v "struct"), none)
    else if let .ok v := j.getObjVal? "natVal" then
      match (← v.getStr?).toNat? with
      | some n => pure (ExprC.mkLitW (.natVal n), none)
      | none => throw "malformed natVal literal"
    else if let .ok v := j.getObjVal? "strVal" then do
      pure (ExprC.mkLitW (.strVal (← v.getStr?)), none)
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
    M ({ cv : ConstantValC // ExprC.WFc cv.type }) := do
  let name ← getNameD st v "name"
  let ty ← getDeclD st v "type" (budgeted || budgetedName name)
  pure ⟨{ name := name
          levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
          type := ty.1 }, ty.2⟩

/-- Twin of `parseConstantVal` (tree form, the bounded consumers). -/
private def parseConstantValTD (st : StateD) (v : Json) : M ConstantVal := do
  pure {
    name := ← getNameD st v "name"
    levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
    type := ← getDeclExprD st v "type"
  }

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
    if cvp.1.name = quotSoundName then
      let cv ← parseConstantValTD st v
      if ConstantInfo.canon (.axiomInfo cv) =
          ConstantInfo.canon (quotBasis.getD 4 (.axiomInfo default)) then
        return .inl st
      else
        return .inr "quotient soundness axiom mismatch"
    return .inl { st with decls := st.decls.push ⟨.axiomDecl cvp.1, cvp.2⟩ }
  else if let .ok v := j.getObjVal? "def" then
    let cvp ← parseConstantValD st v (budgeted := false)
    match (← (← v.getObjVal? "safety").getStr?) with
    | "safe" =>
      let vl ← getDeclD st v "value" (budgetedName cvp.1.name)
      let h ← parseHints v
      return .inl { st with
        decls := st.decls.push ⟨.defnDecl cvp.1 vl.1 h, cvp.2, vl.2⟩ }
    | s => return .inr s!"definition with safety '{s}'"
  else if let .ok v := j.getObjVal? "thm" then
    let cvp ← parseConstantValD st v (budgeted := false)
    let vl ← getDeclD st v "value" (budgetedName cvp.1.name)
    return .inl { st with
      decls := st.decls.push ⟨.thmDecl cvp.1 vl.1, cvp.2, vl.2⟩ }
  else if let .ok v := j.getObjVal? "opaque" then
    let cvp ← parseConstantValD st v (budgeted := false)
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe opaque declaration"
    let vl ← getDeclD st v "value" (budgetedName cvp.1.name)
    return .inl { st with
      decls := st.decls.push ⟨.opaqueDecl cvp.1 vl.1, cvp.2, vl.2⟩ }
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
        return .inl { st with decls := st.decls.push ⟨.basisDecl .quotK, trivial⟩ }
      else
        return .inl st
    else
      return .inr "quotient declaration mismatch"
  else if let .ok v := j.getObjVal? "inductive" then
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
    let blockC := block.map ConstantInfo.canon
    if blockC = BasisKind.eqK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push ⟨.basisDecl .eqK, trivial⟩ }
    else if blockC = BasisKind.natK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push ⟨.basisDecl .natK, trivial⟩ }
    else if blockC = BasisKind.psigmaK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push ⟨.basisDecl .psigmaK, trivial⟩ }
    else if blockC = BasisKind.punitK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push ⟨.basisDecl .punitK, trivial⟩ }
    else if blockC = BasisKind.emptyK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push ⟨.basisDecl .emptyK, trivial⟩ }
    else
      if modeled then
        return .inl { st with decls := st.decls.push ⟨.indDecl block, trivial⟩ }
      else
        -- alias every member to its `_model` counterpart; the member
        -- type is the parsed `ExprC` slot itself (no re-interning, no
        -- conversion), the alias head is a fresh `const` node
        let mut st := st
        for t in (← (← v.getObjVal? "types").getArr?) do
          st ← aliasMember st t
        for c in (← (← v.getObjVal? "ctors").getArr?) do
          st ← aliasMember st c
        for r in (← (← v.getObjVal? "recs").getArr?) do
          st ← aliasMember st r
        return .inl st
  else
    throw "unrecognized line"
where
  /-- One `T := T._model` alias definition from a block-member record:
  the type is the parsed slot (already `ExprC`), the value a fresh
  `const` at the member's own level parameters. -/
  aliasMember (st : StateD) (t : Json) : M StateD := do
    let name ← getNameD st t "name"
    let lps := (← (← getIdxs t "levelParams").mapM st.name).toList
    let ty ← getDeclD st t "type" (budgeted := true)
    let v := ExprC.mkConstW (Name.str name "_model") (lps.map .param)
    let d : WDeclC := ⟨.defnDecl ⟨name, lps, ty.1⟩ v.1 .abbrev, ty.2, v.2⟩
    pure { st with decls := st.decls.push d }

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
  let mk : Option (WExprC × List Nat) :=
    match fn with
    | .app f a => do
      let fe ← st.exprs[f]?
      let ae ← st.exprs[a]?
      pure (ExprC.mkAppW fe ae, [f, a])
    | .binder isAll nm ty bd => do
      let nI ← st.names[nm]?
      let tI ← st.exprs[ty]?
      let bI ← st.exprs[bd]?
      pure (if isAll then (ExprC.mkForallEW nI tI bI ⟨.default, .never⟩, [ty, bd])
            else (ExprC.mkLamW nI tI bI ⟨.default, .never⟩, [ty, bd]))
    | .letE nm ty vl bd => do
      let nI ← st.names[nm]?
      let tI ← st.exprs[ty]?
      let vI ← st.exprs[vl]?
      let bI ← st.exprs[bd]?
      pure (ExprC.mkLetEW nI tI vI bI, [ty, vl, bd])
    | .const nm us => do
      let nI ← st.names[nm]?
      let usI ← us.mapM (st.levels[·]?)
      pure (ExprC.mkConstW nI usI, [])
    | .bvar k => pure (ExprC.mkBVarW k, [])
    | .sort l => do
      let lI ← st.levels[l]?
      pure (ExprC.mkSortW lI, [])
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
  decls : Array WDeclC
  taintSkipped : Array (Name × Name)

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

/-- Wholesale direct parse (tests and small inputs). -/
def parseExportD (contents : String) (modeled : Bool := false) :
    Except FrontendError ParseResultD := do
  let mut st : StateD := {}
  let mut lineNo := 0
  for line in contents.splitToList (· == '\n') do
    lineNo := lineNo + 1
    st ← feedLineD st line lineNo modeled
  return ⟨st.decls, st.taintSkipped⟩

/-- Streaming direct parse (twin of `parseExportStream`; explicit
recursion so the tables stay uniquely referenced across steps). -/
partial def parseExportStreamD (path : System.FilePath)
    (modeled : Bool := false) :
    IO (Except FrontendError ParseResultD) := do
  let h ← IO.FS.Handle.mk path .read
  let rec loop (lineNo : Nat) (st : StateD) :
      IO (Except FrontendError ParseResultD) := do
    let raw ← h.getLine
    if raw.isEmpty then
      return .ok ⟨st.decls, st.taintSkipped⟩
    let line := if raw.back == '\n' then (raw.dropEnd 1).copy else raw
    match feedLineD st line (lineNo + 1) modeled with
    | .error e => return .error e
    | .ok st => loop (lineNo + 1) st
  loop 0 {}

end Setlec.Frontend
