import Lean.Data.Json
import Setlec.Kernel.Env
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Basis

/-!
# Reading lean4export ndjson files

Parses the lean4export NDJSON format (version 3.x, see `format_ndjson.md` in
the lean4export repository) into `Setlec.Declaration`s.

The file is a sequence of JSON objects: an initial `meta` object, then
name/level/expression table entries (keys `in`/`il`/`ie` give the table
index) interleaved with declarations.  Index 0 of the name table is
`Name.anonymous`, index 0 of the level table is `Level.zero`; both are
implicit.  Indices need not be dense or in order (hand-crafted arena tests
have gaps), so the tables are maps; entries are resolved eagerly when
inserted, so a later re-binding of an index cannot retroactively change
anything built earlier.

Declaration kinds the checker cannot represent yet map to
`FrontendError.unsupported`, which the driver turns into the arena's
"declined" exit code — as opposed to malformed input, which is a hard error.
-/

namespace Setlec.Frontend

open Lean (Json)

inductive FrontendError where
  | parseError (line : Nat) (msg : String)
  | unsupported (what : String)

structure State where
  names : Std.HashMap Nat Name := .ofList [(0, .anonymous)]
  levels : Std.HashMap Nat Level := .ofList [(0, .zero)]
  exprs : Std.HashMap Nat Expr := {}
  decls : Array Declaration := #[]

private abbrev M := Except String

private def State.name (st : State) (i : Nat) : M Name :=
  match st.names[i]? with
  | some n => pure n
  | none => throw s!"undefined name index {i}"

private def State.level (st : State) (i : Nat) : M Level :=
  match st.levels[i]? with
  | some l => pure l
  | none => throw s!"undefined level index {i}"

private def State.expr (st : State) (i : Nat) : M Expr :=
  match st.exprs[i]? with
  | some e => pure e
  | none => throw s!"undefined expr index {i}"

private def getIdx (j : Json) (key : String) : M Nat := do
  (← j.getObjVal? key).getNat?

private def getName' (st : State) (j : Json) (key : String) : M Name := do
  st.name (← getIdx j key)

private def getLevel' (st : State) (j : Json) (key : String) : M Level := do
  st.level (← getIdx j key)

private def getExpr' (st : State) (j : Json) (key : String) : M Expr := do
  st.expr (← getIdx j key)

private def getIdxs (j : Json) (key : String) : M (Array Nat) := do
  (← (← j.getObjVal? key).getArr?).mapM (·.getNat?)

private def parseBinderInfo (j : Json) : M BinderInfo := do
  match (← (← j.getObjVal? "binderInfo").getStr?) with
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | s => throw s!"unknown binderInfo {s}"

/-- Parse a name table entry `{"in": i, "str"|"num": {...}}`. -/
private def parseNameEntry (st : State) (j : Json) (i : Nat) : M State := do
  let n ← if let .ok v := j.getObjVal? "str" then
      pure <| Name.str (← getName' st v "pre") (← (← v.getObjVal? "str").getStr?)
    else if let .ok v := j.getObjVal? "num" then
      pure <| Name.num (← getName' st v "pre") (← (← v.getObjVal? "i").getNat?)
    else
      throw "malformed name entry"
  pure { st with names := st.names.insert i n }

/-- Parse a level table entry `{"il": i, ...}`. -/
private def parseLevelEntry (st : State) (j : Json) (i : Nat) : M State := do
  let l ← if let .ok v := j.getObjVal? "succ" then
      pure <| Level.succ (← st.level (← v.getNat?))
    else if let .ok v := j.getObjVal? "max" then
      match ← (← v.getArr?).mapM (·.getNat?) with
      | #[a, b] => pure <| Level.max (← st.level a) (← st.level b)
      | _ => throw "malformed max level"
    else if let .ok v := j.getObjVal? "imax" then
      match ← (← v.getArr?).mapM (·.getNat?) with
      | #[a, b] => pure <| Level.imax (← st.level a) (← st.level b)
      | _ => throw "malformed imax level"
    else if let .ok v := j.getObjVal? "param" then
      pure <| Level.param (← st.name (← v.getNat?))
    else
      throw "malformed level entry"
  pure { st with levels := st.levels.insert i l }

/-- Parse an expression table entry `{"ie": i, ...}`. -/
private def parseExprEntry (st : State) (j : Json) (i : Nat) : M State := do
  let e ← if let .ok v := j.getObjVal? "bvar" then
      pure <| Expr.bvar (← v.getNat?)
    else if let .ok v := j.getObjVal? "sort" then
      pure <| Expr.sort (← st.level (← v.getNat?))
    else if let .ok v := j.getObjVal? "const" then
      pure <| Expr.const (← getName' st v "name")
        (← (← (← v.getObjVal? "us").getArr?).mapM (fun u => do st.level (← u.getNat?))).toList
    else if let .ok v := j.getObjVal? "app" then
      pure <| Expr.app (← getExpr' st v "fn") (← getExpr' st v "arg")
    else if let .ok v := j.getObjVal? "lam" then
      pure <| Expr.lam (← getName' st v "name") (← getExpr' st v "type")
        (← getExpr' st v "body") ⟨← parseBinderInfo v, none⟩
    else if let .ok v := j.getObjVal? "forallE" then
      pure <| Expr.forallE (← getName' st v "name") (← getExpr' st v "type")
        (← getExpr' st v "body") ⟨← parseBinderInfo v, none⟩
    else if let .ok v := j.getObjVal? "letE" then
      pure <| Expr.letE (← getName' st v "name") (← getExpr' st v "type")
        (← getExpr' st v "value") (← getExpr' st v "body")
    else if let .ok v := j.getObjVal? "proj" then
      pure <| Expr.proj (← getName' st v "typeName") (← (← v.getObjVal? "idx").getNat?)
        (← getExpr' st v "struct")
    else if let .ok v := j.getObjVal? "natVal" then
      match (← v.getStr?).toNat? with
      | some n => pure <| Expr.lit (.natVal n)
      | none => throw "malformed natVal literal"
    else if let .ok v := j.getObjVal? "strVal" then
      pure <| Expr.lit (.strVal (← v.getStr?))
    else
      throw "malformed or unsupported expr entry"
  pure { st with exprs := st.exprs.insert i e }

private def parseConstantVal (st : State) (v : Json) : M ConstantVal := do
  pure {
    name := ← getName' st v "name"
    levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
    -- `let` is definitionally its expansion; the checker works let-free.
    type := (← getExpr' st v "type").zetaExpand
  }

/-- Process one line of the export file.  `Sum.inl`: fine (possibly updated
state); `Sum.inr`: unsupported declaration kind. -/
private def processLine (st : State) (j : Json) : M (State ⊕ String) := do
  if let .ok v := j.getObjVal? "in" then
    return .inl (← parseNameEntry st j (← v.getNat?))
  else if let .ok v := j.getObjVal? "il" then
    return .inl (← parseLevelEntry st j (← v.getNat?))
  else if let .ok v := j.getObjVal? "ie" then
    return .inl (← parseExprEntry st j (← v.getNat?))
  else if (j.getObjVal? "meta").isOk then
    return .inl st
  else if let .ok v := j.getObjVal? "axiom" then
    let cv ← parseConstantVal st v
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe axiom"
    return .inl { st with decls := st.decls.push (.axiomDecl cv) }
  else if let .ok v := j.getObjVal? "def" then
    let cv ← parseConstantVal st v
    match (← (← v.getObjVal? "safety").getStr?) with
    | "safe" => return .inl { st with
        decls := st.decls.push (.defnDecl cv (← getExpr' st v "value").zetaExpand) }
    | s => return .inr s!"definition with safety '{s}'"
  else if let .ok v := j.getObjVal? "thm" then
    let cv ← parseConstantVal st v
    return .inl { st with
      decls := st.decls.push (.thmDecl cv (← getExpr' st v "value").zetaExpand) }
  else if (j.getObjVal? "opaque").isOk then
    return .inr "opaque declaration"
  else if (j.getObjVal? "quot").isOk then
    return .inr "quotient declaration"
  else if let .ok v := j.getObjVal? "inductive" then
    -- Parse the block into stored-constant form; a pinned basis block
    -- becomes a `basisDecl`, anything else is converted into alias
    -- definitions `T := T._model` etc. (the lean-inductive-models
    -- preprocessor has emitted the `_model` family earlier in the
    -- stream; if it hasn't, the checker rejects the unresolved alias).
    let types ← (← (← v.getObjVal? "types").getArr?).mapM fun t => do
      if (← (← t.getObjVal? "isUnsafe").getBool?) then throw "unsafe inductive"
      pure (ConstantInfo.indInfo (← parseConstantVal st t))
    let ctors ← (← (← v.getObjVal? "ctors").getArr?).mapM fun c => do
      pure (ConstantInfo.ctorInfo (← parseConstantVal st c)
        (← (← c.getObjVal? "numParams").getNat?)
        (← (← c.getObjVal? "numFields").getNat?))
    let recs ← (← (← v.getObjVal? "recs").getArr?).mapM fun r => do
      let rules ← (← (← r.getObjVal? "rules").getArr?).mapM fun ru => do
        pure (RecRule.mk (← getName' st ru "ctor")
          (← (← ru.getObjVal? "nfields").getNat?)
          (← getExpr' st ru "rhs"))
      pure (ConstantInfo.recInfo (← parseConstantVal st r)
        (← (← r.getObjVal? "numParams").getNat?)
        (← (← r.getObjVal? "numMotives").getNat?)
        (← (← r.getObjVal? "numMinors").getNat?)
        (← (← r.getObjVal? "numIndices").getNat?) rules.toList)
    let block := types.toList ++ ctors.toList ++ recs.toList
    if block = BasisKind.eqK.decls then
      return .inl { st with decls := st.decls.push (.basisDecl .eqK) }
    else if block = BasisKind.natK.decls then
      return .inl { st with decls := st.decls.push (.basisDecl .natK) }
    else if block = BasisKind.psigmaK.decls then
      return .inl { st with decls := st.decls.push (.basisDecl .psigmaK) }
    else if block = BasisKind.punitK.decls then
      return .inl { st with decls := st.decls.push (.basisDecl .punitK) }
    else
      -- alias every member to its `_model` counterpart
      let mut ds := st.decls
      for ci in block do
        let cv := ci.toConstantVal
        ds := ds.push (.defnDecl cv
          (.const (cv.name.str "_model") (cv.levelParams.map .param)))
      return .inl { st with decls := ds }
  else
    throw "unrecognized line"

/-- Parse a whole export file into the declarations it contains, in order. -/
def parseExport (contents : String) : Except FrontendError (Array Declaration) := do
  let mut st : State := {}
  let mut lineNo := 0
  for line in contents.splitToList (· == '\n') do
    lineNo := lineNo + 1
    if line.trimAscii.isEmpty then
      continue
    match Json.parse line >>= processLine st with
    | .error msg => throw (.parseError lineNo msg)
    | .ok (.inr what) => throw (.unsupported what)
    | .ok (.inl st') => st := st'
  return st.decls

end Setlec.Frontend
