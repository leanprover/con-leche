import Lean.Data.Json
import Setlec.Kernel.Env
import Setlec.Kernel.ExprOps
import Setlec.Kernel.Basis
import Setlec.Kernel.StdAxioms
import Setlec.Kernel.Core

/-!
# Reading lean4export ndjson files: the shared scaffolding

The lean4export NDJSON format (version 3.x, see `format_ndjson.md` in
the lean4export repository) is a sequence of JSON objects: an initial
`meta` object, then name/level/expression table entries (keys
`in`/`il`/`ie` give the table index) interleaved with declarations.
Index 0 of the name table is `Name.anonymous`, index 0 of the level
table is `Level.zero`; both are implicit.  Indices need not be dense or
in order (hand-crafted arena tests have gaps), so the tables are maps;
entries are resolved eagerly when inserted, so a later re-binding of an
index cannot retroactively change anything built earlier.

**This file is the representation-free half** — the pieces the parse
proper is written against and would otherwise duplicate:

* `canonLevel`/`canonExpr`/`ConstantInfo.canon`, the `_model`-name
  canonicalization;
* `FrontendError`, the taint and tree-size sentinels, the budget and
  the budgeted-name predicate;
* the small `Json` readers (`getIdx`, `getIdxs`, `parseBinderInfo`,
  `exprEntryChildren`, `parseHints`);
* the byte-level fast path for hot table entries (perf-eng E5:
  `FastNode`/`FastLine`/`fastParse` — 88 % of preprocessed
  init-prelude lines are `{"ie":…}`), which is a pure
  bytes-to-record decoder and mentions no representation;
* `taintSummary`, the driver's decline message.

**The parse proper is `Setlec/Frontend/ExportC.lean`** (task #171): it
reads the stream *directly* to `ExprC` — no arena, no conversion
detour.  Until task #172 this file also held a second parse into an
interned arena (`State`, `parseExport`, `parseExportStream`,
producing `DeclP` over a `WFStore`); that went with the interned
representation.

Declaration kinds the checker cannot represent yet map to
`FrontendError.unsupported`, which the driver turns into the arena's
"declined" exit code — as opposed to malformed input, which is a hard
error.
-/

namespace Setlec.Frontend

open Lean (Json)

/-- Rename level parameters (for basis-block matching up to
level-parameter names). -/
def canonLevel (m : Name → Name) : Level → Level
  | .zero => .zero
  | .succ u => .succ (canonLevel m u)
  | .max u v => .max (canonLevel m u) (canonLevel m v)
  | .imax u v => .imax (canonLevel m u) (canonLevel m v)
  | .param n => .param (m n)

/-- Erase binder names *and binder annotations* and rename level
parameters: the alpha/renaming canonical form used to match a parsed
inductive block against a pinned basis block (Lean's exports use
auto-bound universe names and hygienic binder names, both semantically
irrelevant).

Task #142, pin-side normalization: the parser already maps every
stream binder to `.default`, but the pinned declarations keep the real
`BinderInfo`s of the toolchain signatures they were generated from
(`Setlec/Kernel/Basis/*`, `Setlec/Kernel/StdAxioms.lean` — the
`TTVerify` layer pins those literals).  Both sides of every
`ConstantInfo.canon` comparison go through here, so erasing the
annotation here is what keeps the two sides consistent; without it the
strip would *invert* the bug and no basis block would ever match. -/
def canonExpr (m : Name → Name) : Expr → Expr
  | .bvar i => .bvar i
  | .fvar idx _ ty => .fvar idx .anonymous (canonExpr m ty)
  | .sort u => .sort (canonLevel m u)
  | .const n us => .const n (us.map (canonLevel m))
  | .app f a => .app (canonExpr m f) (canonExpr m a)
  | .lam _ ty b _ => .lam .anonymous (canonExpr m ty) (canonExpr m b) ⟨.default, .never⟩
  | .forallE _ ty b _ =>
      .forallE .anonymous (canonExpr m ty) (canonExpr m b) ⟨.default, .never⟩
  | .letE _ ty v b => .letE .anonymous (canonExpr m ty) (canonExpr m v)
      (canonExpr m b)
  | .lit l => .lit l
  | .proj s i e => .proj s i (canonExpr m e)

/-- Canonical form of a stored constant for basis matching. -/
def ConstantInfo.canon (ci : ConstantInfo) : ConstantInfo :=
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

/-- Internal sentinel: a declaration-level expression lookup hit a
tainted entry.  Backstop only — `processLine`'s read-only pre-scan
(`declRecordScan`) skips tainted declarations before any parsing, so
this should be unreachable; if it fires anyway it is converted to a
decline at the record level (the pre-change behavior). -/
def taintSentinel : String := "\x00uses-skipped-axiom"

/-- Internal sentinel converted to a decline at the record level. -/
def sizeSentinel : String := "\x00tree-size-budget"

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
def anyComponentModel : Name → Bool
  | .anonymous => false
  | .str p s => s == "_model" || anyComponentModel p
  | .num p _ => anyComponentModel p

/-- Does the budget apply to a definition/theorem/opaque record of
this name?  (Inductive, quotient and axiom records are always
budgeted.) -/
def budgetedName (n : Name) : Bool :=
  anyComponentModel n || natOpNames.contains n || natDivModNames.contains n

private abbrev M := Except String

def getIdx (j : Json) (key : String) : M Nat := do
  (← j.getObjVal? key).getNat?

def getIdxs (j : Json) (key : String) : M (Array Nat) := do
  (← (← j.getObjVal? key).getArr?).mapM (·.getNat?)

/-- Validate a binder record's `binderInfo` field and **discard** it
(task #142).  Kernel typing erases binder annotations — the official
kernel accepts a declaration however its binders are marked — so the
frontend maps every parsed binder to `.default`, and an
annotation-only deviation cannot exist anywhere downstream (in
particular it can no longer make a basis block miss its pin).  The
field is still parsed: an unknown spelling is a malformed record, not
a silently ignored one. -/
def parseBinderInfo (j : Json) : M Unit := do
  match (← (← j.getObjVal? "binderInfo").getStr?) with
  | "default" | "implicit" | "strictImplicit" | "instImplicit" => pure ()
  | s => throw s!"unknown binderInfo {s}"

/-- The child expression-table indices of an entry (for taint and size
propagation). -/
def exprEntryChildren (j : Json) : M (List Nat) := do
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

/-- Parse a `def` record's `hints` field: `"abbrev"`, `"opaque"`, or
`{"regular": n}`.  A missing field defaults to `regular 0` — hints
steer only the unfolding order of lazy delta, so any default is
behaviorally safe. -/
def parseHints (v : Json) : M ReducibilityHint := do
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

/-! ### perf-eng E5: byte-level fast path for hot table entries

The stream is dominated by tiny table-entry records — on preprocessed
init-prelude, 88 % of lines are `{"ie":…}` and 9 % are `{"in":…}` —
and the generic `Lean.Json` DOM (Parsec + `DTreeMap` object per line)
is pure overhead for them.  This fast path pattern-matches the exact
emitter byte layouts of the hot shapes and interns directly; on ANY
mismatch (unknown kind, `pw` field present, escaped/odd strings,
taint-active const entries, trailing bytes) it returns `.fallback`
with the state untouched and the generic path runs as before.  A
handled line performs the byte-identical state update the generic
path would (`parseNameEntry`/`parseExprEntry` semantics, including
the taint/size bookkeeping); intern-time errors reuse the generic
error strings.  No verified module imports the frontend. -/

/-- A parsed hot expression-table node, still in stream indices. -/
inductive FastNode where
  | app (f a : Nat)
  | binder (isAll : Bool) (name ty body : Nat)
  | letE (name ty vl body : Nat)
  | const (name : Nat) (us : List Nat)
  | bvar (k : Nat)
  | sort (l : Nat)

/-- A parsed hot line. -/
inductive FastLine where
  | ie (i : Nat) (n : FastNode)
  | inStr (i pre : Nat) (s : String)

private def bIE : ByteArray := "{\"ie\":".toUTF8
private def bIN : ByteArray := "{\"in\":".toUTF8
private def bAPP : ByteArray := ",\"app\":{\"arg\":".toUTF8
private def bFN : ByteArray := ",\"fn\":".toUTF8
private def bLAM : ByteArray := ",\"lam\":{\"binderInfo\":\"".toUTF8
private def bFORALL : ByteArray := ",\"forallE\":{\"binderInfo\":\"".toUTF8
private def bBODYQ : ByteArray := "\",\"body\":".toUTF8
private def bNAME : ByteArray := ",\"name\":".toUTF8
private def bTYPE : ByteArray := ",\"type\":".toUTF8
private def bCONST : ByteArray := ",\"const\":{\"name\":".toUTF8
private def bUS : ByteArray := ",\"us\":[".toUTF8
private def bBVAR : ByteArray := ",\"bvar\":".toUTF8
private def bSORT : ByteArray := ",\"sort\":".toUTF8
private def bLETE : ByteArray := ",\"letE\":{\"body\":".toUTF8
private def bVALUE : ByteArray := ",\"value\":".toUTF8
private def bSTRPRE : ByteArray := ",\"str\":{\"pre\":".toUTF8
private def bSTRK : ByteArray := ",\"str\":".toUTF8
private def bCLOSE2 : ByteArray := "}}".toUTF8
private def bCLOSE1 : ByteArray := "}".toUTF8
private def bBIdefault : ByteArray := "default".toUTF8
private def bBIimplicit : ByteArray := "implicit".toUTF8
private def bBIstrict : ByteArray := "strictImplicit".toUTF8
private def bBIinst : ByteArray := "instImplicit".toUTF8

/-- Match a literal byte string at `i`; the position after it. -/
def fsLit (b : ByteArray) (i : Nat) (lit : ByteArray) :
    Option Nat := Id.run do
  let n := lit.size
  if i + n > b.size then return none
  for k in [0:n] do
    if b[i + k]! != lit[k]! then return none
  return some (i + n)

/-- Parse a decimal `Nat` at `i` (≤ 20 digits; longer falls back). -/
def fsNat (b : ByteArray) (i0 : Nat) : Option (Nat × Nat) := Id.run do
  let mut acc : Nat := 0
  let mut i := i0
  let mut seen := false
  for _ in [0:20] do
    if h : i < b.size then
      let c := b[i]
      if 48 ≤ c.toNat ∧ c.toNat ≤ 57 then
        acc := acc * 10 + (c.toNat - 48)
        i := i + 1
        seen := true
      else break
    else break
  if h : i < b.size then
    if 48 ≤ b[i].toNat ∧ b[i].toNat ≤ 57 then return none
  if seen then return some (acc, i) else return none

/-- Parse a JSON string at `i` with no escapes (backslash falls back;
multi-byte UTF-8 passes through `String.fromUTF8?` validation). -/
def fsStr (b : ByteArray) (i0 : Nat) : Option (String × Nat) := Id.run do
  if h : i0 < b.size then
    if b[i0] != 34 then return none
  else return none
  let mut close : Option Nat := none
  for k in [i0 + 1 : b.size] do
    let c := b[k]!
    if c == 34 then
      close := some k
      break
    else if c == 92 ∨ c < 32 then return none
  match close with
  | none => return none
  | some k =>
    match String.fromUTF8? (b.extract (i0 + 1) k) with
    | some s => return some (s, k + 1)
    | none => return none

/-- The four `binderInfo` spellings (validated and discarded, as
`parseBinderInfo`). -/
def fsBinderInfo (b : ByteArray) (i : Nat) : Option Nat :=
  (fsLit b i bBIstrict) <|> (fsLit b i bBIinst) <|>
  (fsLit b i bBIimplicit) <|> (fsLit b i bBIdefault)

/-- `NAT ("," NAT)* "]"` or `"]"` — the `us` list tail. -/
def fsNatList (b : ByteArray) (i0 : Nat) :
    Option (List Nat × Nat) := Id.run do
  if h : i0 < b.size then
    if b[i0] == 93 then return some ([], i0 + 1)  -- ']'
  else return none
  let mut i := i0
  let mut acc : List Nat := []
  for _ in [0 : b.size] do
    match fsNat b i with
    | none => return none
    | some (v, j) =>
      acc := v :: acc
      if h : j < b.size then
        if b[j] == 44 then i := j + 1  -- ','
        else if b[j] == 93 then return some (acc.reverse, j + 1)
        else return none
      else return none
  return none

/-- Parse one hot line; `none` = not a handled shape. -/
def fastParse (b : ByteArray) : Option FastLine := do
  let n := b.size
  let ate (i : Nat) (lit : ByteArray) : Option Nat := fsLit b i lit
  let atEnd2 (i : Nat) : Option Unit := do
    let j ← ate i bCLOSE2
    if j = n then pure () else none
  let atEnd1 (i : Nat) : Option Unit := do
    let j ← ate i bCLOSE1
    if j = n then pure () else none
  match fsLit b 0 bIE with
  | some i =>
    let (idx, i) ← fsNat b i
    -- dispatch on the byte after `,"`
    if i + 2 < b.size then
      match b[i + 2]! with
      | 97 => do  -- 'a' → app
        let i ← ate i bAPP
        let (a, i) ← fsNat b i
        let i ← ate i bFN
        let (f, i) ← fsNat b i
        atEnd2 i
        pure (.ie idx (.app f a))
      | 108 => do  -- 'l' → lam / letE
        match ate i bLAM with
        | some i => do
          let i ← fsBinderInfo b i
          let i ← ate i bBODYQ
          let (bd, i) ← fsNat b i
          let i ← ate i bNAME
          let (nm, i) ← fsNat b i
          let i ← ate i bTYPE
          let (ty, i) ← fsNat b i
          atEnd2 i
          pure (.ie idx (.binder false nm ty bd))
        | none => do
          let i ← ate i bLETE
          let (bd, i) ← fsNat b i
          let i ← ate i bNAME
          let (nm, i) ← fsNat b i
          let i ← ate i bTYPE
          let (ty, i) ← fsNat b i
          let i ← ate i bVALUE
          let (vl, i) ← fsNat b i
          atEnd2 i
          pure (.ie idx (.letE nm ty vl bd))
      | 102 => do  -- 'f' → forallE
        let i ← ate i bFORALL
        let i ← fsBinderInfo b i
        let i ← ate i bBODYQ
        let (bd, i) ← fsNat b i
        let i ← ate i bNAME
        let (nm, i) ← fsNat b i
        let i ← ate i bTYPE
        let (ty, i) ← fsNat b i
        atEnd2 i
        pure (.ie idx (.binder true nm ty bd))
      | 99 => do  -- 'c' → const
        let i ← ate i bCONST
        let (nm, i) ← fsNat b i
        let i ← ate i bUS
        let (us, i) ← fsNatList b i
        atEnd2 i
        pure (.ie idx (.const nm us))
      | 98 => do  -- 'b' → bvar
        let i ← ate i bBVAR
        let (k, i) ← fsNat b i
        atEnd1 i
        pure (.ie idx (.bvar k))
      | 115 => do  -- 's' → sort
        let i ← ate i bSORT
        let (l, i) ← fsNat b i
        atEnd1 i
        pure (.ie idx (.sort l))
      | _ => none
    else none
  | none => do
    let i ← fsLit b 0 bIN
    let (idx, i) ← fsNat b i
    let i ← ate i bSTRPRE
    let (pre, i) ← fsNat b i
    let i ← ate i bSTRK
    let (s, i) ← fsStr b i
    atEnd2 i
    pure (.inStr idx pre s)

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

end Setlec.Frontend
