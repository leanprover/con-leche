import Lean.Data.Json
import Setlec.Kernel.Env
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Basis
import Setlec.Kernel.StdAxioms

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

/-- Rename level parameters (for basis-block matching up to
level-parameter names). -/
private def canonLevel (m : Name → Name) : Level → Level
  | .zero => .zero
  | .succ u => .succ (canonLevel m u)
  | .max u v => .max (canonLevel m u) (canonLevel m v)
  | .imax u v => .imax (canonLevel m u) (canonLevel m v)
  | .param n => .param (m n)

/-- Erase binder names and rename level parameters: the alpha/renaming
canonical form used to match a parsed inductive block against a pinned
basis block (Lean's exports use auto-bound universe names and hygienic
binder names, both semantically irrelevant). -/
private def canonExpr (m : Name → Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx _ ty => .fvar idx .anonymous (canonExpr m ty)
  | .sort u => .sort (canonLevel m u)
  | .const n us => .const n (us.map (canonLevel m))
  | .app f a => .app (canonExpr m f) (canonExpr m a)
  | .lam _ ty b bm => .lam .anonymous (canonExpr m ty) (canonExpr m b)
      ⟨bm.bi, bm.cod.map (canonLevel m)⟩
  | .forallE _ ty b bm => .forallE .anonymous (canonExpr m ty) (canonExpr m b)
      ⟨bm.bi, bm.cod.map (canonLevel m)⟩
  | .letE _ ty v b => .letE .anonymous (canonExpr m ty) (canonExpr m v)
      (canonExpr m b)
  | .lit l => .lit l
  | .proj s i e => .proj s i (canonExpr m e)

/-- Canonical form of a stored constant for basis matching. -/
private def ConstantInfo.canon (ci : ConstantInfo) : ConstantInfo :=
  let ps := ci.toConstantVal.levelParams
  let m : Name → Name := fun n =>
    match ps.findIdx? (fun p => p == n) with
    | some i => .num .anonymous i
    | none => n
  let cv : ConstantVal := { ci.toConstantVal with
    levelParams := (List.range ps.length).map (.num .anonymous ·),
    type := canonExpr m ci.toConstantVal.type }
  match ci with
  | .axiomInfo _ => .axiomInfo cv
  | .defnInfo _ v hint => .defnInfo cv (canonExpr m v) hint
  | .thmInfo _ v => .thmInfo cv (canonExpr m v)
  | .indInfo _ _ => .indInfo cv {}
  | .ctorInfo _ nP nF => .ctorInfo cv nP nF
  | .recInfo _ mI rP rules => .recInfo cv mI rP
      (rules.map fun r => { r with rhs := canonExpr m r.rhs })
  -- table entries never occur in parsed input; identity keeps the
  -- match total
  | .projInfo e => .projInfo e

inductive FrontendError where
  | parseError (line : Nat) (msg : String)
  | unsupported (what : String)

structure State where
  names : Std.HashMap Nat Name := .ofList [(0, .anonymous)]
  levels : Std.HashMap Nat Level := .ofList [(0, .zero)]
  exprs : Std.HashMap Nat Expr := {}
  decls : Array Declaration := #[]
  /-- Expression-table entries that (transitively) mention a skipped
  axiom, maintained as entries are parsed so the check is `O(1)` per
  entry even on heavily shared tables. -/
  tainted : Std.HashMap Nat Unit := {}
  /-- Names of skipped axiom records.  Non-pinned axioms are invisible
  (user ruling: only the pinned standard axioms are ever accepted, see
  DESIGN.md): the *declaration* is dropped without stopping the run —
  like `sorryAx`, which has no set model (`∀ α, Bool → α` is empty at
  `α := ∅`) — and any later *use* is positively declined. -/
  skippedAxioms : Std.HashMap Name Unit := {}

/-- Internal sentinel converted to a decline at the record level. -/
private def taintSentinel : String := "\x00uses-skipped-axiom"

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

/-- Declaration-level expression lookup: a reference to a skipped
(non-pinned) axiom is a positive decline (via `taintSentinel`). -/
private def getDeclExpr' (st : State) (j : Json) (key : String) : M Expr := do
  let i ← getIdx j key
  if st.tainted[i]?.isSome then
    throw taintSentinel
  st.expr i

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

/-- The child expression-table indices of an entry (for taint
propagation). -/
private def exprEntryChildren (j : Json) : M (List Nat) := do
  if let .ok v := j.getObjVal? "app" then
    pure [← getIdx v "fn", ← getIdx v "arg"]
  else if let .ok v := j.getObjVal? "lam" then
    pure [← getIdx v "type", ← getIdx v "body"]
  else if let .ok v := j.getObjVal? "forallE" then
    pure [← getIdx v "type", ← getIdx v "body"]
  else if let .ok v := j.getObjVal? "letE" then
    pure [← getIdx v "type", ← getIdx v "value", ← getIdx v "body"]
  else if let .ok v := j.getObjVal? "proj" then
    pure [← getIdx v "struct"]
  else
    pure []

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
  let taint : Bool ← do
    match e with
    | .const n _ => pure (st.skippedAxioms.contains n)
    | _ =>
      let cs ← exprEntryChildren j
      pure (cs.any (fun c => st.tainted[c]?.isSome))
  let st := { st with exprs := st.exprs.insert i e }
  if taint then
    let t := st.tainted
    let st := { st with tainted := {} }
    pure { st with tainted := t.insert i () }
  else
    pure st

/-- Parse a `def` record's `hints` field: `"abbrev"`, `"opaque"`, or
`{"regular": n}`.  A missing field defaults to `regular 0` — hints
steer only the unfolding order of lazy delta, so any default is
behaviorally safe. -/
private def parseHints (v : Json) : M ReducibilityHint := do
  match v.getObjVal? "hints" with
  | .error _ => pure (.regular 0)
  | .ok h =>
    if let .ok s := h.getStr? then
      match s with
      | "abbrev" => pure .abbrev
      | "opaque" => pure .opaque
      | s => throw s!"unknown reducibility hint '{s}'"
    else if let .ok n := h.getObjVal? "regular" then
      pure (.regular (← n.getNat?))
    else
      throw "malformed hints field"

private def parseConstantVal (st : State) (v : Json) : M ConstantVal := do
  pure {
    name := ← getName' st v "name"
    levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
    -- `let` is definitionally its expansion; the checker works let-free.
    type := (← getDeclExpr' st v "type").zetaExpand
  }

/-- Process one line of the export file.  `Sum.inl`: fine (possibly updated
state); `Sum.inr`: unsupported declaration kind. -/
private def processLineCore (st : State) (j : Json)
    (modeled : Bool := false) : M (State ⊕ String) := do
  if let .ok v := j.getObjVal? "in" then
    return .inl (← parseNameEntry st j (← v.getNat?))
  else if let .ok v := j.getObjVal? "il" then
    return .inl (← parseLevelEntry st j (← v.getNat?))
  else if let .ok v := j.getObjVal? "ie" then
    return .inl (← parseExprEntry st j (← v.getNat?))
  else if (j.getObjVal? "meta").isOk then
    return .inl st
  else if let .ok v := j.getObjVal? "axiom" then
    -- an axiom whose own type references a previously skipped axiom
    -- is itself a *use*: the sentinel in `parseConstantVal` declines
    let cv ← parseConstantVal st v
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe axiom"
    -- the pinned quotient soundness axiom is installed with the `Quot`
    -- basis block; skip its (matching) declaration record
    if cv.name = quotSoundName then
      if ConstantInfo.canon (.axiomInfo cv) =
          ConstantInfo.canon (quotBasis.getD 4 (.axiomInfo default)) then
        return .inl st
      else
        return .inr "quotient soundness axiom mismatch"
    -- every axiom record is forwarded (the checker well-formedness-
    -- checks it — a garbage record must keep rejecting), but only the
    -- pinned standard axioms are installed; every other axiom is
    -- invisible after its check (user ruling): the run continues, and
    -- any later declaration referencing the skipped axiom is
    -- positively declined (see `State.skippedAxioms`)
    if cv.name = propextName ∨ cv.name = choiceName then
      return .inl { st with decls := st.decls.push (.axiomDecl cv) }
    return .inl { st with
      decls := st.decls.push (.axiomDecl cv),
      skippedAxioms := st.skippedAxioms.insert cv.name () }
  else if let .ok v := j.getObjVal? "def" then
    -- Note: `_model` companions the preprocessor may emit for basis
    -- blocks (e.g. `Eq._model`) are *not* special-cased here: `_model`
    -- names are not reserved, so they flow through and are checked as
    -- ordinary definitions like any other input declaration (the
    -- pinned basis install never consults them — a basis inductive
    -- block matches the pinned declarations, not the modeled path).
    let cv ← parseConstantVal st v
    match (← (← v.getObjVal? "safety").getStr?) with
    | "safe" => return .inl { st with
        decls := st.decls.push (.defnDecl cv
          (← getDeclExpr' st v "value").zetaExpand (← parseHints v)) }
    | s => return .inr s!"definition with safety '{s}'"
  else if let .ok v := j.getObjVal? "thm" then
    let cv ← parseConstantVal st v
    return .inl { st with
      decls := st.decls.push (.thmDecl cv (← getDeclExpr' st v "value").zetaExpand) }
  else if let .ok v := j.getObjVal? "opaque" then
    let cv ← parseConstantVal st v
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe opaque declaration"
    return .inl { st with
      decls := st.decls.push
        (.opaqueDecl cv (← getDeclExpr' st v "value").zetaExpand) }
  else if let .ok v := j.getObjVal? "quot" then
    -- the kernel quotient bundle: each record must match its pinned
    -- basis member; the type former's record installs the whole block
    let cv ← parseConstantVal st v
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
        return .inl { st with decls := st.decls.push (.basisDecl .quotK) }
      else
        return .inl st
    else
      return .inr "quotient declaration mismatch"
  else if let .ok v := j.getObjVal? "inductive" then
    -- Parse the block into stored-constant form; a pinned basis block
    -- becomes a `basisDecl`, anything else is converted into alias
    -- definitions `T := T._model` etc. (the lean-inductive-models
    -- preprocessor has emitted the `_model` family earlier in the
    -- stream; if it hasn't, the checker rejects the unresolved alias).
    let types ← (← (← v.getObjVal? "types").getArr?).mapM fun t => do
      if (← (← t.getObjVal? "isUnsafe").getBool?) then throw "unsafe inductive"
      pure (ConstantInfo.indInfo (← parseConstantVal st t) {})
    let ctors ← (← (← v.getObjVal? "ctors").getArr?).mapM fun c => do
      pure (ConstantInfo.ctorInfo (← parseConstantVal st c)
        (← (← c.getObjVal? "numParams").getNat?)
        (← (← c.getObjVal? "numFields").getNat?))
    let recs ← (← (← v.getObjVal? "recs").getArr?).mapM fun r => do
      let rules ← (← (← r.getObjVal? "rules").getArr?).mapM fun ru => do
        -- `ctorParams`/`fire` are install-computed; parse placeholders.
        -- The rhs is zeta-expanded like every other parsed expression
        -- (the checker works let-free; install annotates the rhs and
        -- would otherwise decline on `letE`).
        pure (RecRule.mk (← getName' st ru "ctor")
          (← (← ru.getObjVal? "nfields").getNat?) 0 .inert
          (← getDeclExpr' st ru "rhs").zetaExpand)
      -- only the two sums the checker reads are kept: the major's
      -- position and the rule-application prefix
      let nP ← (← r.getObjVal? "numParams").getNat?
      let nM ← (← r.getObjVal? "numMotives").getNat?
      let nm ← (← r.getObjVal? "numMinors").getNat?
      let ni ← (← r.getObjVal? "numIndices").getNat?
      pure (ConstantInfo.recInfo (← parseConstantVal st r)
        (nP + nM + nm + ni) (nP + nM + nm) rules.toList)
    let block := types.toList ++ ctors.toList ++ recs.toList
    let blockC := block.map ConstantInfo.canon
    if blockC = BasisKind.eqK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push (.basisDecl .eqK) }
    else if blockC = BasisKind.natK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push (.basisDecl .natK) }
    else if blockC = BasisKind.psigmaK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push (.basisDecl .psigmaK) }
    else if blockC = BasisKind.punitK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push (.basisDecl .punitK) }
    else if blockC = BasisKind.emptyK.decls.map ConstantInfo.canon then
      return .inl { st with decls := st.decls.push (.basisDecl .emptyK) }
    else
      if modeled then
        -- store the block opaquely, checked against its `_model` family
        return .inl { st with decls := st.decls.push (.indDecl block) }
      else
        -- alias every member to its `_model` counterpart
        let mut ds := st.decls
        for ci in block do
          let cv := ci.toConstantVal
          ds := ds.push (.defnDecl cv
            (.const (cv.name.str "_model") (cv.levelParams.map .param))
            .abbrev)
        return .inl { st with decls := ds }
  else
    throw "unrecognized line"

/-- `processLineCore` plus the skipped-axiom-use sentinel translated
into a decline. -/
private def processLine (st : State) (j : Json)
    (modeled : Bool := false) : M (State ⊕ String) :=
  tryCatch (processLineCore st j modeled) fun e =>
    if e = taintSentinel then
      pure (.inr "declaration uses a skipped (non-pinned) axiom")
    else throw e

/-- Parse a whole export file into the declarations it contains, in order. -/
def parseExport (contents : String) (modeled : Bool := false) :
    Except FrontendError (Array Declaration) := do
  let mut st : State := {}
  let mut lineNo := 0
  for line in contents.splitToList (· == '\n') do
    lineNo := lineNo + 1
    if line.trimAscii.isEmpty then
      continue
    match Json.parse line >>= (fun j => processLine st j modeled) with
    | .error msg => throw (.parseError lineNo msg)
    | .ok (.inr what) => throw (.unsupported what)
    | .ok (.inl st') => st := st'
  return st.decls

end Setlec.Frontend
