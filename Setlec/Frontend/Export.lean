import Lean.Data.Json
import Setlec.Kernel.Env
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Basis
import Setlec.Kernel.StdAxioms
import Setlec.Kernel.DeclI
import Setlec.Kernel.Core
import Setlec.Kernel.WFStore

/-!
# Reading lean4export ndjson files

Parses the lean4export NDJSON format (version 3.x, see `format_ndjson.md` in
the lean4export repository) into `Setlec.DeclP`s over a parse arena.

The file is a sequence of JSON objects: an initial `meta` object, then
name/level/expression table entries (keys `in`/`il`/`ie` give the table
index) interleaved with declarations.  Index 0 of the name table is
`Name.anonymous`, index 0 of the level table is `Level.zero`; both are
implicit.  Indices need not be dense or in order (hand-crafted arena tests
have gaps), so the tables are maps; entries are resolved eagerly when
inserted, so a later re-binding of an index cannot retroactively change
anything built earlier.

**Parse-time interning (task #78).**  Expression- and level-table entries
are interned *directly into the arena* (a `WFStore`, well-formed by
construction since task #103) — one checked `intern?` per record,
children resolved to already-interned indices, `O(1)` per entry — so the
export format's structural sharing is preserved: a DAG-shaped table
(arena `good/perf/app-lam`: 24k entries, ~10^1160 unshared tree nodes)
parses in linear time and the checker's drivers consume the indices
without ever materializing a tree.  Declarations carry indices (`DeclP`);
`Expr` trees are read back only where a genuinely bounded consumer needs
them — basis/quotient pin matching and inductive blocks (whose install
pipeline compares member types against `_model` artifacts with tree
traversals) — all guarded by the unshared-tree-size budget.

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
  /-- The parse arena: every expression/level-table entry interned on
  arrival, well-formed *by construction* (`WFStore`, task #103 — the
  entry interns go through the checked `intern?` variants, so a record
  whose translated child indices were out of range is rejected on the
  spot).  Seeded with the implicit level-table index 0 (`zero`). -/
  store : WFStore := .empty
  /-- Stream name-table index → arena name index (task #88: name-table
  entries are interned directly; index 0 is the implicit
  `anonymous`, seeded by `initState`). -/
  names : Std.HashMap Nat NIdx := {}
  levels : Std.HashMap Nat LIdx := {}
  exprs : Std.HashMap Nat EIdx := {}
  decls : Array DeclP := #[]
  /-- Expression-table entries that (transitively) mention a tainted
  constant, mapped to the whitelisted axiom root the taint traces to;
  maintained as entries are parsed so the check is `O(1)` per entry
  even on heavily shared tables. -/
  tainted : Std.HashMap Nat Name := {}
  /-- Tainted constant names, mapped to the whitelisted axiom root:
  the tolerated axioms themselves (root = the axiom; the *declaration*
  record is dropped without stopping the run — user ruling: only the
  pinned standard axioms are ever accepted, see DESIGN.md — like
  `sorryAx`, which has no set model: `∀ α, Bool → α` is empty at
  `α := ∅`) plus every declaration skipped because it (transitively)
  *uses* one (skip-and-continue, user directive 2026-08-24). -/
  taintedNames : Std.HashMap Name Name := {}
  /-- Declarations skipped because they (transitively) use a tolerated
  axiom — (declaration name, whitelisted axiom root), in stream order.
  Tolerated axiom *records* themselves are not listed: dropping them is
  by design and alone never declines the stream.  Nonempty means the
  input as a whole is declined by the driver even when every remaining
  declaration checks (uses of tolerated axioms are never accepted). -/
  taintSkipped : Array (Name × Name) := #[]
  /-- Saturated *unshared tree size* per expression-table entry,
  maintained incrementally (`O(1)` per entry).  Since parse-time
  interning (task #78) the ordinary definition/theorem/opaque pipeline
  is DAG-preserving end to end and needs no budget; the budget guards
  exactly the remaining tree-materializing consumers (see
  `budgetExempt` below). -/
  sizes : Std.HashMap Nat Nat := {}

/-- Internal sentinel: a declaration-level expression lookup hit a
tainted entry.  Backstop only — `processLine`'s read-only pre-scan
(`declRecordScan`) skips tainted declarations before any parsing, so
this should be unreachable; if it fires anyway it is converted to a
decline at the record level (the pre-change behavior). -/
private def taintSentinel : String := "\x00uses-skipped-axiom"

/-- Internal sentinel converted to a decline at the record level. -/
private def sizeSentinel : String := "\x00tree-size-budget"

/-- Cap on a declaration's *unshared tree size* (nodes of the
expression tree with all sharing expanded).  `2^25`: at and beyond this
scale the remaining tree-materializing consumers could not represent
the declaration anyway; every stream the checker supports today is far
below it, while adversarial DAG towers are cleanly declined.  Since
parse-time interning (task #78) the budget no longer applies to
ordinary definition/theorem/opaque records (whose whole pipeline is
DAG-preserving; arena `good/perf/app-lam` accepts) — it guards exactly
the consumers that still materialize or walk trees:

* inductive and quotient blocks (read back for basis-pin matching, and
  the install pipeline compares member types/rule right-hand sides
  against `_model` artifacts with tree traversals),
* axiom records (standard-axiom pin matching walks the stored type),
* records whose name contains a `_model` component (their stored types
  are consumed by tree traversals at a later inductive install:
  iota/eta/unitlike statements, model types, projection models),
* the certified `Nat` operations (`natOpNames`/`natDivModNames`; the
  install-time certification substitutes the stored value into the
  recurrence equations and re-interns the result). -/
def declTreeSizeBudget : Nat := 33554432

/-- Any name component is `_model` (the preprocessor's model-family
shape: `T._model`, `T._model.iota_j`, `T._model.proj_i.iota`, …). -/
private def anyComponentModel : Name → Bool
  | .anonymous => false
  | .str p s => s == "_model" || anyComponentModel p
  | .num p _ => anyComponentModel p

/-- Does the budget apply to a definition/theorem/opaque record of
this name?  (Inductive, quotient and axiom records are always
budgeted.) -/
private def budgetedName (n : Name) : Bool :=
  anyComponentModel n || natOpNames.contains n || natDivModNames.contains n

private abbrev M := Except String

private def State.nameIdx (st : State) (i : Nat) : M NIdx :=
  match st.names[i]? with
  | some n => pure n
  | none => throw s!"undefined name index {i}"

/-- The name-table entry as a `Name` tree (readback from the arena;
declaration headers and level parameters). -/
private def State.name (st : State) (i : Nat) : M Name := do
  match st.store.readbackN (← st.nameIdx i) with
  | some n => pure n
  | none => throw "internal: parse-arena name readback failed"

private def State.level (st : State) (i : Nat) : M LIdx :=
  match st.levels[i]? with
  | some l => pure l
  | none => throw s!"undefined level index {i}"

private def State.expr (st : State) (i : Nat) : M EIdx :=
  match st.exprs[i]? with
  | some e => pure e
  | none => throw s!"undefined expr index {i}"

private def getIdx (j : Json) (key : String) : M Nat := do
  (← j.getObjVal? key).getNat?

private def getName' (st : State) (j : Json) (key : String) : M Name := do
  st.name (← getIdx j key)

private def getNameIdx' (st : State) (j : Json) (key : String) : M NIdx := do
  st.nameIdx (← getIdx j key)

private def getExprIdx' (st : State) (j : Json) (key : String) : M EIdx := do
  st.expr (← getIdx j key)

/-- Declaration-level expression lookup: a reference to a tainted
entry throws `taintSentinel` (backstop — the pre-scan in `processLine`
skips tainted declarations before parsing reaches here).  The
tree-size budget is applied only when `budgeted` (see
`declTreeSizeBudget`). -/
private def getDeclEIdx' (st : State) (j : Json) (key : String)
    (budgeted : Bool) : M EIdx := do
  let i ← getIdx j key
  if st.tainted[i]?.isSome then
    throw taintSentinel
  if budgeted ∧ (st.sizes[i]?.getD 1) ≥ declTreeSizeBudget then
    throw sizeSentinel
  st.expr i

/-- Declaration-level *tree* lookup for the bounded consumers
(basis/quotient pin matching, inductive blocks): taint check, budget
check, memoized readback (pointer-shared, `O(DAG)`). -/
private def getDeclExpr' (st : State) (j : Json) (key : String) : M Expr := do
  let i ← getDeclEIdx' st j key (budgeted := true)
  match st.store.readbackI i with
  | some e => pure e
  | none => throw "internal: parse-arena readback failed"

private def getIdxs (j : Json) (key : String) : M (Array Nat) := do
  (← (← j.getObjVal? key).getArr?).mapM (·.getNat?)

private def parseBinderInfo (j : Json) : M BinderInfo := do
  match (← (← j.getObjVal? "binderInfo").getStr?) with
  | "default" => pure .default
  | "implicit" => pure .implicit
  | "strictImplicit" => pure .strictImplicit
  | "instImplicit" => pure .instImplicit
  | s => throw s!"unknown binderInfo {s}"

/-- Intern one name node into the parse arena (linear threading, as
`internL'` below; the checked intern rejects out-of-range child
indices — a malformed export record). -/
private def State.internN' (st : State) (n : NNode) : M (NIdx × State) :=
  let store := st.store
  let st := { st with store := WFStore.empty }
  match store.internN? n with
  | some (u, store) => pure (u, { st with store := store })
  | none => throw "malformed name entry: node index out of range"

/-- Parse a name table entry `{"in": i, "str"|"num": {...}}`, interning
the node directly from the stream's prefix index (task #88). -/
private def parseNameEntry (st : State) (j : Json) (i : Nat) : M State := do
  let (ni, st) ← if let .ok v := j.getObjVal? "str" then do
      let p ← st.nameIdx (← getIdx v "pre")
      st.internN' (.str p (← (← v.getObjVal? "str").getStr?))
    else if let .ok v := j.getObjVal? "num" then do
      let p ← st.nameIdx (← getIdx v "pre")
      st.internN' (.num p (← (← v.getObjVal? "i").getNat?))
    else
      throw "malformed name entry"
  pure { st with names := st.names.insert i ni }

/-- Intern one level node into the parse arena (linear threading: the
store is detached from the state before the update). -/
private def State.internL' (st : State) (n : LNode) : M (LIdx × State) :=
  let store := st.store
  let st := { st with store := WFStore.empty }
  match store.internL? n with
  | some (u, store) => pure (u, { st with store := store })
  | none => throw "malformed level entry: node index out of range"

/-- Intern one expression node into the parse arena. -/
private def State.intern' (st : State) (n : ENode) : M (EIdx × State) :=
  let store := st.store
  let st := { st with store := WFStore.empty }
  match store.intern? n with
  | some (i, store) => pure (i, { st with store := store })
  | none => throw "malformed expr entry: node index out of range"

/-- Parse a level table entry `{"il": i, ...}`, interning the node. -/
private def parseLevelEntry (st : State) (j : Json) (i : Nat) : M State := do
  let (l, st) ←
    if let .ok v := j.getObjVal? "succ" then
      st.internL' (.succ (← st.level (← v.getNat?)))
    else if let .ok v := j.getObjVal? "max" then
      match ← (← v.getArr?).mapM (·.getNat?) with
      | #[a, b] => st.internL' (.max (← st.level a) (← st.level b))
      | _ => throw "malformed max level"
    else if let .ok v := j.getObjVal? "imax" then
      match ← (← v.getArr?).mapM (·.getNat?) with
      | #[a, b] => st.internL' (.imax (← st.level a) (← st.level b))
      | _ => throw "malformed imax level"
    else if let .ok v := j.getObjVal? "param" then
      st.internL' (.param (← st.name (← v.getNat?)))
    else
      throw "malformed level entry"
  pure { st with levels := st.levels.insert i l }

/-- The child expression-table indices of an entry (for taint and size
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

/-- Parse an expression table entry `{"ie": i, ...}`: build the node
over the children's arena indices and intern it — `O(1)` per entry,
sharing preserved. -/
private def parseExprEntry (st : State) (j : Json) (i : Nat) : M State := do
  let (e, taintConst, st) ←
    if let .ok v := j.getObjVal? "bvar" then
      let (e, st) ← st.intern' (.bvar (← v.getNat?))
      pure (e, none, st)
    else if let .ok v := j.getObjVal? "sort" then
      let (e, st) ← st.intern' (.sort (← st.level (← v.getNat?)))
      pure (e, none, st)
    else if let .ok v := j.getObjVal? "const" then
      let nI ← getNameIdx' st v "name"
      let us ← (← (← v.getObjVal? "us").getArr?).mapM
        (fun u => do st.level (← u.getNat?))
      let taintC : Option Name ←
        if st.taintedNames.isEmpty then pure none
        else do pure st.taintedNames[(← getName' st v "name")]?
      let (e, st) ← st.intern' (.const nI us.toList)
      pure (e, taintC, st)
    else if let .ok v := j.getObjVal? "app" then
      let (e, st) ← st.intern'
        (.app (← getExprIdx' st v "fn") (← getExprIdx' st v "arg"))
      pure (e, none, st)
    else if let .ok v := j.getObjVal? "lam" then
      let (e, st) ← st.intern' (.lam (← getNameIdx' st v "name")
        (← getExprIdx' st v "type") (← getExprIdx' st v "body")
        ⟨← parseBinderInfo v, none⟩)
      pure (e, none, st)
    else if let .ok v := j.getObjVal? "forallE" then
      let (e, st) ← st.intern' (.forallE (← getNameIdx' st v "name")
        (← getExprIdx' st v "type") (← getExprIdx' st v "body")
        ⟨← parseBinderInfo v, none⟩)
      pure (e, none, st)
    else if let .ok v := j.getObjVal? "letE" then
      let (e, st) ← st.intern' (.letE (← getNameIdx' st v "name")
        (← getExprIdx' st v "type") (← getExprIdx' st v "value")
        (← getExprIdx' st v "body"))
      pure (e, none, st)
    else if let .ok v := j.getObjVal? "proj" then
      let (e, st) ← st.intern' (.proj (← getNameIdx' st v "typeName")
        (← (← v.getObjVal? "idx").getNat?) (← getExprIdx' st v "struct"))
      pure (e, none, st)
    else if let .ok v := j.getObjVal? "natVal" then
      match (← v.getStr?).toNat? with
      | some n =>
        let (e, st) ← st.intern' (.lit (.natVal n))
        pure (e, none, st)
      | none => throw "malformed natVal literal"
    else if let .ok v := j.getObjVal? "strVal" then
      let (e, st) ← st.intern' (.lit (.strVal (← v.getStr?)))
      pure (e, none, st)
    else
      throw "malformed or unsupported expr entry"
  let cs ← exprEntryChildren j
  let taint : Option Name :=
    taintConst <|> cs.findSome? (fun c => st.tainted[c]?)
  -- saturated unshared tree size (children default to 1: leaf entries
  -- are never inserted into `sizes` below the cap check's default)
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

/-- Parse a record's constant-value header with the type as an arena
index (`letE` flows through unexpanded: the kernel zeta-reduces
lazily, task #79). -/
private def parseConstantValP (st : State) (v : Json) (budgeted : Bool) :
    M ConstantValP := do
  let name ← getName' st v "name"
  pure {
    name := name
    levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
    type := ← getDeclEIdx' st v "type" (budgeted || budgetedName name)
  }

/-- Parse a record's constant-value header as a tree (the bounded
consumers: basis/quotient matching, inductive blocks). -/
private def parseConstantVal (st : State) (v : Json) : M ConstantVal := do
  pure {
    name := ← getName' st v "name"
    levelParams := (← (← getIdxs v "levelParams").mapM st.name).toList
    type := ← getDeclExpr' st v "type"
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
    -- tolerated-whitelist axiom records never reach this branch
    -- (`processLine` drops them without parsing the type); an axiom
    -- whose own type references a tainted constant is itself a *use*
    -- and was skipped by the pre-scan.  Axiom records stay budgeted:
    -- standard-axiom pin matching walks the stored type as a tree.
    let cvp ← parseConstantValP st v (budgeted := true)
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe axiom"
    -- the pinned quotient soundness axiom is installed with the `Quot`
    -- basis block; skip its (matching) declaration record
    if cvp.name = quotSoundName then
      let cv ← parseConstantVal st v
      if ConstantInfo.canon (.axiomInfo cv) =
          ConstantInfo.canon (quotBasis.getD 4 (.axiomInfo default)) then
        return .inl st
      else
        return .inr "quotient soundness axiom mismatch"
    -- every remaining axiom record is forwarded (the checker
    -- well-formedness-checks it first — a garbage record must keep
    -- *rejecting* — then installs the pinned standard axioms and
    -- positively declines the rest at their own record).
    return .inl { st with decls := st.decls.push (.axiomDecl cvp) }
  else if let .ok v := j.getObjVal? "def" then
    -- Note: `_model` companions the preprocessor may emit for basis
    -- blocks (e.g. `Eq._model`) are *not* special-cased here: `_model`
    -- names are not reserved, so they flow through and are checked as
    -- ordinary definitions like any other input declaration (the
    -- pinned basis install never consults them — a basis inductive
    -- block matches the pinned declarations, not the modeled path).
    let cvp ← parseConstantValP st v (budgeted := false)
    match (← (← v.getObjVal? "safety").getStr?) with
    | "safe" => return .inl { st with
        decls := st.decls.push (.defnDecl cvp
          (← getDeclEIdx' st v "value" (budgetedName cvp.name))
          (← parseHints v)) }
    | s => return .inr s!"definition with safety '{s}'"
  else if let .ok v := j.getObjVal? "thm" then
    let cvp ← parseConstantValP st v (budgeted := false)
    return .inl { st with
      decls := st.decls.push (.thmDecl cvp
        (← getDeclEIdx' st v "value" (budgetedName cvp.name))) }
  else if let .ok v := j.getObjVal? "opaque" then
    let cvp ← parseConstantValP st v (budgeted := false)
    if (← (← v.getObjVal? "isUnsafe").getBool?) then
      return .inr "unsafe opaque declaration"
    return .inl { st with
      decls := st.decls.push
        (.opaqueDecl cvp (← getDeclEIdx' st v "value" (budgetedName cvp.name))) }
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
    -- Parse the block into stored-constant form (read back under the
    -- budget: the install pipeline compares member types against the
    -- `_model` family with tree traversals); a pinned basis block
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
        -- Like every other parsed expression, the rhs keeps its `letE`
        -- nodes; install annotates it through the kernel's letE rule.
        pure (RecRule.mk (← getName' st ru "ctor")
          (← (← ru.getObjVal? "nfields").getNat?) 0 .inert
          (← getDeclExpr' st ru "rhs"))
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
        -- alias every member to its `_model` counterpart (interning the
        -- small synthetic alias value and re-interning the member type
        -- gives the parsed-index record shape; the block was read back
        -- under the budget, so the tree walk is bounded)
        let mut st := st
        for ci in block do
          let cv := ci.toConstantVal
          let store := st.store
          st := { st with store := WFStore.empty }
          let (us, store) := store.internLevels (cv.levelParams.map .param)
          let (mI, store) := store.internName (cv.name.str "_model")
          -- the alias head's levels/name were interned just above, so
          -- the checked intern cannot fail; the guard keeps the arena
          -- well-formed by construction
          let some (vi, store) := store.intern? (.const mI us)
            | throw "internal: parse-arena alias intern out of range"
          let (ti, store) := store.internExprFast cv.type
          let ds := st.decls.push
            (.defnDecl ⟨cv.name, cv.levelParams, ti⟩ vi .abbrev)
          st := { st with store := store, decls := ds }
        return .inl st
  else
    throw "unrecognized line"

/-- Read-only pre-scan of a declaration record: its declared names and
its declaration-level expression-table indices (type, value, and — for
inductive blocks — every member type and recursor-rule right-hand
side; exactly the indices `getDeclEIdx'`/`getDeclExpr'` would check).
`none` for table entries and `meta` lines.  Used by `processLine` to
decide a taint skip *before* `processLineCore` runs: a handler that
inspected the state after a thrown sentinel would keep a second live
reference to the state across the record's arena inserts, turning each
into a whole-table copy. -/
private def declRecordScan (st : State) (j : Json) :
    M (Option (List Name × List Nat)) := do
  for k in ["axiom", "quot"] do
    if let .ok v := j.getObjVal? k then
      return some ([← getName' st v "name"], [← getIdx v "type"])
  for k in ["def", "thm", "opaque"] do
    if let .ok v := j.getObjVal? k then
      return some ([← getName' st v "name"],
        [← getIdx v "type", ← getIdx v "value"])
  if let .ok v := j.getObjVal? "inductive" then
    let mut names := []
    let mut idxs := []
    for key in ["types", "ctors", "recs"] do
      for t in (← (← v.getObjVal? key).getArr?) do
        names := (← getName' st t "name") :: names
        idxs := (← getIdx t "type") :: idxs
    for r in (← (← v.getObjVal? "recs").getArr?) do
      for ru in (← (← r.getObjVal? "rules").getArr?) do
        idxs := (← getIdx ru "rhs") :: idxs
    return some (names.reverse, idxs)
  return none

/-- `processLineCore` under the taint policy (user ruling: only the
tolerated axiom whitelist may be *declared*, and uses of a tolerated
axiom are never accepted; user directive 2026-08-24: maximize coverage
by skipping instead of declining the whole stream):

* a tolerated axiom record (exactly `sorryAx` since task #95 — the
  compiler-trust family now *installs* through the checker instead)
  is dropped and its name tainted *without parsing its type at all*;
  the record was never installed anyway;
* a declaration that (transitively) references a tainted constant is
  *skipped*: not checked, not installed, its declared names tainted
  (so transitive users are skipped too), recorded in
  `State.taintSkipped`; the stream continues and the driver declines
  the input as a whole at the end;
* the tree-size sentinel stays a decline at the record level. -/
private def processLine (st : State) (j : Json)
    (modeled : Bool := false) : M (State ⊕ String) := do
  if let .ok v := j.getObjVal? "axiom" then
    let name ← getName' st v "name"
    if toleratedAxiomNames.contains name then
      let m := st.taintedNames
      let st := { st with taintedNames := {} }
      return .inl { st with taintedNames := m.insert name name }
  if let some (names, idxs) ← declRecordScan st j then
    if let some root := idxs.findSome? (fun i => st.tainted[i]?) then
      let m := st.taintedNames
      let sk := st.taintSkipped
      let st := { st with taintedNames := {}, taintSkipped := #[] }
      let m := names.foldl (fun m n => m.insert n root) m
      return .inl { st with
        taintedNames := m,
        taintSkipped := sk.push (names.headD .anonymous, root) }
  tryCatch (processLineCore st j modeled) fun e =>
    if e = taintSentinel then
      -- backstop, unreachable when `declRecordScan` is complete: keep
      -- the pre-skip decline verdict rather than crash
      pure (.inr "declaration uses a skipped (non-pinned) axiom")
    else if e = sizeSentinel then
      pure (.inr "declaration's unshared tree size exceeds the frontend budget (heavily DAG-shared input; this record kind still materializes trees)")
    else throw e

/-- Initial parse state: the implicit level-table index 0 (`zero`)
and name-table index 0 (`anonymous`) pre-interned. -/
private def initState : State :=
  let (z0, store0) := WFStore.empty.internL .zero
    (by simp [LNode.children])
  let (a0, store1) := store0.internN .anonymous
    (by simp [NNode.children])
  { store := store1, levels := .ofList [(0, z0)],
    names := .ofList [(0, a0)] }

/-- Feed one line of the export (trailing newline already stripped) into
the parse state; blank lines are skipped.  The state is threaded
linearly (moved in, moved out) so the arena keeps its exclusive
reference across lines. -/
private def feedLine (st : State) (line : String) (lineNo : Nat)
    (modeled : Bool) : Except FrontendError State :=
  if line.trimAscii.isEmpty then .ok st
  else
    match Json.parse line >>= (fun j => processLine st j modeled) with
    | .error msg => .error (.parseError lineNo msg)
    | .ok (.inr what) => .error (.unsupported what)
    | .ok (.inl st) => .ok st

/-- A parsed export stream. -/
structure ParseResult where
  /-- The parse arena, well-formed by construction (task #103): the
  checker consumes it without re-validating. -/
  store : WFStore
  /-- The declarations, in stream order.  Declarations skipped by
  taint are *absent*: they can never reach the checker, so nothing
  that uses a tolerated axiom is ever installed. -/
  decls : Array DeclP
  /-- Declarations skipped because they (transitively) use a tolerated
  axiom — (name, whitelisted axiom root), in stream order.  Nonempty
  means the driver must *decline* the input as a whole even when every
  declaration in `decls` checks. -/
  taintSkipped : Array (Name × Name)

/-- Diagnostic summary of the taint skips: total, per-root counts, and
the first few skipped names. -/
def taintSummary (skips : Array (Name × Name)) : String :=
  let perRoot := toleratedAxiomNames.filterMap fun r =>
    match skips.foldl (fun c p => if p.2 == r then c + 1 else c) 0 with
    | 0 => none
    | c => some s!"{c} via {r}"
  let names := (skips.toList.take 8).map (fun p => s!"{p.1}")
  let more := if skips.size > 8 then ", …" else ""
  s!"skipped {skips.size} declarations that use a tolerated axiom ({String.intercalate "; " perRoot}); first skipped: {String.intercalate ", " names}{more}"

/-- Parse a whole in-memory export into the parse arena and the
declarations it contains, in order.  (Wholesale entry point, kept for
tests and small inputs; the driver streams via `parseExportStream`.) -/
def parseExport (contents : String) (modeled : Bool := false) :
    Except FrontendError ParseResult := do
  let mut st := initState
  let mut lineNo := 0
  for line in contents.splitToList (· == '\n') do
    lineNo := lineNo + 1
    st ← feedLine st line lineNo modeled
  return ⟨st.store, st.decls, st.taintSkipped⟩

/-- Streaming parse (task #57): read the export line by line from the
file, feeding each record into the parse arena as it arrives — the raw
text is transient (one line at a time), so retained memory is
proportional to the arena and the declaration records, never to the
text.  Explicit recursion with the state as a plain argument, not a
`for`/`while` loop: a loop's boxed state tuple keeps the arena shared
across the step, and the first insert then copies the whole node/hash
tables (see `progressLoop` in `Main.lean`). -/
partial def parseExportStream (path : System.FilePath)
    (modeled : Bool := false) :
    IO (Except FrontendError ParseResult) := do
  let h ← IO.FS.Handle.mk path .read
  let rec loop (lineNo : Nat) (st : State) :
      IO (Except FrontendError ParseResult) := do
    let raw ← h.getLine
    if raw.isEmpty then
      return .ok ⟨st.store, st.decls, st.taintSkipped⟩
    -- strip exactly the trailing newline (mirroring the wholesale
    -- entry point's `splitToList (· == '\n')`; a `\r` before it is
    -- kept, as there).  `copy` detaches the line from the read buffer.
    let line := if raw.back == '\n' then (raw.dropEnd 1).copy else raw
    match feedLine st line (lineNo + 1) modeled with
    | .error e => return .error e
    | .ok st => loop (lineNo + 1) st
  loop 0 initState

end Setlec.Frontend
