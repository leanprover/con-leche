module

public import ConLeche.Frontend.Olean.Header
public import ConLeche.Frontend.Olean.Reads

@[expose] public section

/-!
# Reading `.olean` files: a module's views

A module of the module system has three files, each holding one `ModuleData`, the
view of the module at one level (`OLeanLevel`, Lean's own):

| level | file | |
|---|---|---|
| `.exported` | `M.olean` | what an importer in a module of the module system sees |
| `.server` | `M.olean.server` | the language server's |
| `.private` | `M.olean.private` | what a file outside the module system, and lean4export, sees |

They are written by one compactor, in that order: one address space, a later file's
objects pointing into the earlier ones.  So **a view reads the files up to its own**
(`ModFiles.viewRegion`), and an importer needs `M.olean` alone.  A classic module
has its `M.olean`, and every level is that.

**`decodeModuleSpec` is the specification** of a view, `noncomputable`: it says what
a valid view is.  `parseView` is one view, fast (it decodes what that view reaches);
`parseAllViews` is all three, each object once.  Both are proved to be the
specification (`parseView_eq_spec`, `parseAllViews_eq`,
`ConLeche/Verify/Frontend/Olean/View.lean`).

The imports the start of `M.olean` holds (`importsPre`, what a closure's walk reads)
must be the view's, at every level, so that the prefix read follows from any full
one.
-/

namespace ConLeche.Frontend.Olean

open ConLeche

/-- **The level of a view** (Lean's `OLeanLevel`).  Each level includes the previous
ones. -/
inductive OLeanLevel where
  | exported
  | server
  | «private»
  deriving DecidableEq, Repr, Inhabited

/-- **A module's files**: `M.olean`, and those of `M.olean.server` and
`M.olean.private` that are at hand. -/
structure ModFiles where
  exported : Part
  server : Option Part := none
  «private» : Option Part := none

/-- Does `M.olean` say it is of a module of the module system. -/
def ModFiles.isModule (f : ModFiles) : Bool :=
  match moduleSkel (Region.single f.exported) f.exported.moduleDataAddr with
  | some sk => sk.isModule
  | none => false

/-- **The region and the address of a view**: the files up to its own (the whole
of a classic module). -/
def ModFiles.viewRegion (f : ModFiles) : OLeanLevel → Option (Region × UInt64)
  | .exported => some (Region.single f.exported, f.exported.moduleDataAddr)
  | .server =>
    if f.isModule then do
      let s ← f.server
      let r ← (Region.ofParts #[f.exported, s]).toOption
      pure (r, s.moduleDataAddr)
    else some (Region.single f.exported, f.exported.moduleDataAddr)
  | .private =>
    if f.isModule then do
      let s ← f.server
      let p ← f.private
      let r ← (Region.ofParts #[f.exported, s, p]).toOption
      pure (r, p.moduleDataAddr)
    else some (Region.single f.exported, f.exported.moduleDataAddr)

/-- **THE SPECIFICATION of a view**: the `ModuleData` of that level, in the region of
the files up to its own, with the imports the start of `M.olean` holds. -/
noncomputable def decodeModuleSpec (f : ModFiles) (level : OLeanLevel) : Option ModDecoded := do
  let (r, a) ← f.viewRegion level
  let d ← decodeAt r a
  unless importsPre f.exported.bytes == some d.imports do none
  pure d

/-- **One view**, fast: what it reaches, each object once. -/
def parseView (f : ModFiles) (level : OLeanLevel) : Option ModDecoded := do
  let (r, a) ← f.viewRegion level
  let d ← parseAt r a
  unless importsPre f.exported.bytes == some d.imports do none
  pure d

/-- All three views of a module. -/
structure AllViews where
  exported : ModDecoded
  server : ModDecoded
  «private» : ModDecoded

/-- **All three views, each object once**, whatever views reach it.  A view must
keep to the files up to its own, as its specification does: `M.olean`'s and
`M.olean.server`'s `ModuleData` are looked for in the region of those files; below
that a pointer can only point down. -/
def parseAllViews (f : ModFiles) : Option AllViews := do
  if f.isModule then
    let s ← f.server
    let p ← f.private
    let ae := f.exported.moduleDataAddr
    let as := s.moduleDataAddr
    let ap := p.moduleDataAddr
    unless ((Region.single f.exported).loc ae).isSome do none
    let r2 ← (Region.ofParts #[f.exported, s]).toOption
    unless (r2.loc as).isSome do none
    let r ← (Region.ofParts #[f.exported, s, p]).toOption
    match parseMany r [ae, as, ap] with
    | some [de, ds, dp] =>
      let pre := importsPre f.exported.bytes
      unless pre == some de.imports && pre == some ds.imports && pre == some dp.imports do none
      pure ⟨de, ds, dp⟩
    | _ => none
  else
    let d ← parseView f .exported
    pure ⟨d, d, d⟩

/-- A view at a level. -/
def AllViews.at (v : AllViews) : OLeanLevel → ModDecoded
  | .exported => v.exported
  | .server => v.server
  | .private => v.private

/-- **The files a view reads** of a module's. -/
def ModFiles.upTo (f : ModFiles) : OLeanLevel → ModFiles
  | .exported => { exported := f.exported }
  | .server => { f with «private» := none }
  | .private => f

/-! ## The reads of a part of a view

Each returns its part of the full view, where that reads
(`ConLeche/Verify/Frontend/Olean/View.lean`).  The converse does not hold, on
purpose: a read looks only at what it needs, so it can succeed on a file whose full
parse fails on an object the read never visits.  A reader may rely on a file only
through a full parse of it (at the module's home); the reads then cannot fail or
disagree. -/

/-- **Per constant of a view, its position, name, kind and filter**; no expression
is read.  A name two constants bear fails it. -/
def readNamePositions (f : ModFiles) (level : OLeanLevel) : Option NamePositions := do
  let (r, a) ← f.viewRegion level
  namePositionsAt r a

/-- **The constant at a position of a view**, read with a memo of its own. -/
def readEntry (f : ModFiles) (level : OLeanLevel) (c : Nat) : Option (CEntryF Name Expr) := do
  let (r, _) ← f.viewRegion level
  entryAt r c

/-- **The statements of the constants at some positions of a view**, read together. -/
def readStmts (f : ModFiles) (level : OLeanLevel) (cs : List Nat) : Option (List ConstantVal) := do
  let (r, _) ← f.viewRegion level
  stmtsAt r cs

/-! ## The errors -/

/-- The module's files do not decode. -/
def undecodable (m : Name) : CheckError :=
  .internal s!"module {m}: malformed .olean data (an object of the wrong shape, or a \
    pointer that does not point below its object)"

/-- Why a view does not read. -/
def viewError (m : Name) (f : ModFiles) (level : OLeanLevel) : CheckError :=
  match f.viewRegion level with
  | none => .internal s!"module {m}: the .olean files of a module overlap"
  | some (r, a) =>
    if constNamesOk r a then
      match parseAt r a with
      | some _ => .internal s!"module {m}: the {repr level} part's imports are not those at the \
          start of its .olean"
      | none => undecodable m
    else
      .internal s!"module {m}: the {repr level} part's name table (constNames) does not list \
        its constants' names, each once"

end ConLeche.Frontend.Olean
