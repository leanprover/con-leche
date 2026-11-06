module

public import ConLeche.Frontend.Olean.Emit
public import ConLeche.Frontend.Olean.Closure
public import ConLeche.Frontend.ExportC

@[expose] public section

/-!
# `con-leche --olean`: the import closure as one record stream

`con-leche --olean M₁ … Mₙ` checks the modules `Mᵢ` and everything they
import, read from their `.olean` files.  This file ends the reader's
pipeline in the same `Declaration` records the lean4export reader produces
(`ConLeche/Frontend/ExportC.lean`), so that everything after the parse — the
prelude preparation, the install and the check, and the main theorem about
them — is the stream path's.

A theorem's record holds a reference to its value (`valueRef`), which its check
reads (`readValue`, task #481).

**What is merged is what lean4export exports**: the closure loaded at the
PRIVATE level (each module-system module's `.olean.private`, whose
`ModuleData` holds the full constants; a module outside the module system has
only its `.olean`), merged as Lean's own `finalizeImport` merges them, and
emitted in lean4export's order.  Each emitted record becomes a `Declaration`
through the stream reader's own builder `declOfF`, so the validation of
inductive records (`validateIndF`) and every decline are the stream path's.
The tool `olean-compare` compares the two readers record for record.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- A name of the emitter's table, for the stream reader's builder. -/
def Emit.nm (em : Emit) (i : Nat) : M Name :=
  match em.names[i]? with
  | some n => pure n
  | none => throw s!"undefined name index {i}"

/-- The emitter has no level table: its expressions are whole. -/
def Emit.lv (_ : Emit) (_ : Nat) : M Level := throw "no level table"

/-- An expression of the emitter's table, for the stream reader's builder. -/
def Emit.ex (em : Emit) (i : Nat) : M Expr :=
  match em.exprs[i]? with
  | some e => pure e
  | none => throw s!"undefined expr index {i}"

/-- `declsOf`'s walk: `k` the position of the first of `rs`. -/
def declsGo (em : Emit) (k : Nat) : List DeclRec → Array Declaration →
    Except (CheckError × Nat) (Array Declaration)
  | [], ds => .ok ds
  | r :: rs, ds =>
    match declOfF em.nm em.lv em.ex r with
    | .ok (.inl d) => declsGo em (k + 1) rs (ds.push d)
    | .ok (.inr v) => .error (v.toError, k)
    | .error msg => .error (.internal msg, k)

/-- **The `Declaration` records**, through the stream reader's builder.
A record's verdict (a decline, a contradiction between its fields) is
the stream path's, at the record's position. -/
def declsOf (em : Emit) : Except (CheckError × Nat) (Array Declaration) :=
  declsGo em 0 em.out.toList #[]

/-- The constants the emission starts from: the named ones, each of which the closure
must hold, or all of them. -/
def rootConstants (mg : Merged) : Option (Array Name) → Except CheckError (Array Name)
  | none => pure mg.order
  | some cs =>
    match cs.find? (!mg.map.contains ·) with
    | some c => throw (.internal s!"the constant {c} is not in the import closure")
    | none => pure cs

/-- What a theorem's check needs of a module of the closure's order. -/
structure ModRef where
  name : Name
  frontier : Frontier

instance : Inhabited ModRef := ⟨⟨.anonymous, {}⟩⟩

/-- **What a read gives**: the records, a theorem's value as its reference; what its check
needs to read it, by the reference's module; and the merged constants, for what a value
mentions (`OleanRead.thmUses`). -/
structure OleanRead where
  decls : Array Declaration
  values : Array ModRef
  merged : Merged

/-- **What a theorem's record mentions**, which its reference does not say: what the load
read off the file.  `none` for any other record, whose own expressions say it. -/
def OleanRead.thmUses (rd : OleanRead) : Declaration → Option (Array Name)
  | .thmDecl cv _ => rd.merged.map[cv.name]?.map (·.uses.toArray)
  | _ => none

/-- **The whole read**: load, merge, emit, build.  `constants` names the constants to
start from, as lean4export's arguments after `--` do; `none` is every constant of the
closure. -/
def readOleans {μ : Type → Type} [CheckerIO μ] (sp : SearchPath)
    (roots : Array Name) (constants : Option (Array Name) := none) (jobs : Nat := 1)
    (pace : Pace := .off) : μ (Except (CheckError × Nat) OleanRead) := do
  let n ← CheckerIO.liftIO (ReadNotes.new pace)
  match ← loadClosure sp n roots jobs with
  | .error e => pure (.error (e, 0))
  | .ok ls =>
    CheckerIO.liftIO (n.say s!"merging the constants of {ls.size} modules")
    match mergeAll ls with
    | .error e => pure (.error (e, 0))
    | .ok mg =>
      CheckerIO.liftIO (n.say s!"checking the blocks of {mg.order.size} constants")
      match blocksOk mg with
      | .error e => pure (.error (e, 0))
      | .ok () =>
        match rootConstants mg constants with
        | .error e => pure (.error (e, 0))
        | .ok cs =>
          CheckerIO.liftIO (n.say s!"emitting records from {cs.size} constants")
          match declsOf (emitAll mg cs) with
          | .error e => pure (.error e)
          | .ok ds =>
            pure (.ok ⟨ds, ls.map fun l => ⟨l.name, l.frontier⟩, mg⟩)

/-! ## A theorem's value, read -/

/-- **What a worker keeps between its checks**: the region of the module it read last.  The
checks of one module are next to each other in the records, and a module's files are
read again for each worker that reaches it. -/
structure ValueCache where
  idx : Nat := 0
  region : Option Region := none

/-- The region of module `idx`, from the cache or the files, with the cache to go on with. -/
def regionFor {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (m : Name) (idx : Nat)
    (c : ValueCache) : μ (ValueCache × Except CheckError Region) := do
  match c.region with
  | some r =>
    if c.idx == idx then return (c, .ok r)
    else readRegion
  | none => readRegion
where
  readRegion : μ (ValueCache × Except CheckError Region) := do
    match ← readFiles sp m .private with
    | .error e => pure ({}, .error e)
    | .ok f =>
      match f.viewRegion .private with
      | none => pure ({}, .error (viewError m f .private))
      | some (r, _) => pure ({ idx, region := some r }, .ok r)

/-- **A theorem's value, from its reference's code**: the files of its module (`regionFor`),
then the value, over the module's frontier (`frontierExpr`). -/
def readValue {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (values : Array ModRef)
    (c : ValueCache) (code : Nat) : μ (ValueCache × Except CheckError Expr) := do
  match values[refModule code]? with
  | none => pure (c, .error (.internal s!"a theorem's value in module {refModule code}, of {values.size}"))
  | some md =>
    match ← regionFor sp md.name (refModule code) c with
    | (c, .error e) => pure (c, .error e)
    | (c, .ok r) =>
      match frontierExpr r md.frontier (refLoc code) with
      | some e => pure (c, .ok e)
      | none => pure (c, .error (undecodable md.name))

/-- A record with its theorem's value read, if it is a theorem's. -/
def fillRecord {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (values : Array ModRef)
    (c : ValueCache) : Declaration → μ (ValueCache × Except CheckError Declaration)
  | .thmDecl cv (.bvar code) => do
    match ← readValue sp values c code with
    | (c, .ok e) => pure (c, .ok (.thmDecl cv e))
    | (c, .error e) => pure (c, .error e)
  | d => pure (c, .ok d)

/-- `fillRecord` of each record, in order. -/
def fillRecords {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (values : Array ModRef)
    (c : ValueCache) : List Declaration → Array Declaration → μ (Except CheckError (Array Declaration))
  | [], acc => pure (.ok acc)
  | d :: ds, acc => do
    match ← fillRecord sp values c d with
    | (_, .error e) => pure (.error e)
    | (c, .ok d) => fillRecords sp values c ds (acc.push d)

/-- **The records with every theorem's value read**, for the tools that compare them: the
checker itself reads a value in its check. -/
def readOleansFull {μ : Type → Type} [CheckerIO μ] (sp : SearchPath)
    (roots : Array Name) (constants : Option (Array Name) := none) (jobs : Nat := 1) :
    μ (Except (CheckError × Nat) (Array Declaration)) := do
  match ← readOleans sp roots constants jobs with
  | .error e => pure (.error e)
  | .ok rd =>
    match ← fillRecords sp rd.values {} rd.decls.toList #[] with
    | .error e => pure (.error (e, 0))
    | .ok ds => pure (.ok ds)

end ConLeche.Frontend.Olean
