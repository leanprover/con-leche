module

public import ConLeche.Cached.ModStore

@[expose] public section

/-!
# The isolated check of a module (task #373)

A modular run (`ConLeche/Driver/Modular.lean`) installs and checks every
module at a **view** of one store (`Store.view`): the store's name index
and every module's unit, gated by the viewing module's levels.  This file
holds the specification that view stands for, a module checked **in
isolation**:

* `isoCtx` — module `M`'s context built from `M`'s imports' units alone:
  for every module `M` loads, in module order, every constant of its
  unit as `M`'s level presents it (`presentAt`: at the private level the
  installed constant, read from the private record `prv`; at the
  exported level its exported presentation, read from the interface
  `exp` alone, through its gates), with its projection table if it is
  presented as a type former; each name once, the first presentation
  (`firstNamed`);
* `checkModuleIsolated` — the checker's own declaration fold (the
  install step `installDeclStep` over the records, then every recorded
  check `checkPendingList`, as `checkDecls`) started at the canonical
  index of that context, `mkFEnv (isoCtx …)`: no store, no view.

The store run is the same fold started at the module's view
(`checkAtView`).  `Mod.checkAtView_isolated`
(`ConLeche/Verify/Modular/Iso.lean`) proves the two equal — the same
verdict, the same error at the same position, the same installed
constants — whenever the store's name index lists every unit constant
under its name, each name's alternates in module order (`idxOk`, checked
by every modular run).

`ownView` is a module's own constants over its view's base: the store
run's final view, rebuilt from an isolated run's constants (the unit's
bookkeeping — exported presentations, gates, qualified names — reads
the name index through it, in both modes).
-/

namespace ConLeche.Cached.Mod

open ConLeche

/-! ## A module's context from its imports' units -/

/-- A gate is open for a viewer with levels `lv` (`MBase.gateOk`). -/
def gateOpen (lv : ByteArray) (g : Array (Nat × UInt8)) : Bool :=
  g.all fun (h, l) => lvlAt lv h ≥ l

/-- **A unit's constant `j`, as a viewer with levels `lv` that loads its
module at level `l` sees it**: at the private level (`2`) the installed
constant, from the private record; at the exported level (`1`) its
exported presentation, from the interface alone — absent unless its
gate is open, the assumption of its statement unless its value gate is
open too; nothing at any other level. -/
def presentAt (lv : ByteArray) (s : ModSlot) (l : UInt8) (j : Nat) : Option ConstantInfo :=
  if l == 2 then s.prv.priv[j]?
  else if l == 1 then
    match (s.exp.at1[j]?).join with
    | some ci =>
      if gateOpen lv ((s.exp.g1[j]?).getD #[]) then
        if gateOpen lv ((s.exp.v1[j]?).getD #[]) then some ci
        else some (.axiomInfo ci.toConstantVal)
      else none
    | none => none
  else none

/-- The projection table of a unit's constant `j` at level `l`. -/
def presentTbl (s : ModSlot) (l : UInt8) (j : Nat) : Option ProjTable :=
  if l == 2 then (s.prv.tbls[j]?).join else (s.exp.tbls[j]?).join

/-- **A presented constant**, with its module, its position in the
module's unit, and its projection table if it is presented as a type
former. -/
structure IsoEntry where
  h : Nat
  j : Nat
  ci : ConstantInfo
  tbl : Option ProjTable

/-- The table a presented constant brings: a type former's own table
(named by the type former), nothing for any other kind. -/
def entryTbl (ci : ConstantInfo) (t : Option ProjTable) : Option ProjTable :=
  match ci with
  | .indInfo .. => t.filter (·.structName == ci.name)
  | _ => none

/-- The positions of a unit a level reads: the private record's at the
private level, the interface's otherwise. -/
def posCount (s : ModSlot) (l : UInt8) : Nat :=
  if l == 2 then s.prv.priv.size else s.exp.at1.size

/-- **Module `h`'s presented constants**, in unit order: none of a
module the viewer does not load, whose unit is not read at all (it may
not be published yet: a later module, or the viewer itself). -/
def entriesOf (lv : ByteArray) (h : Nat) (slot : Nat → ModSlot) : List IsoEntry :=
  if lvlAt lv h == 0 then [] else
  (List.range (posCount (slot h) (lvlAt lv h))).filterMap fun j =>
    (presentAt lv (slot h) (lvlAt lv h) j).map fun ci =>
      ⟨h, j, ci, entryTbl ci (presentTbl (slot h) (lvlAt lv h) j)⟩

/-- **Every presented constant of a viewer's context**, module by module
in module order. -/
def isoEntries (slot : Nat → ModSlot) (lv : ByteArray) : List IsoEntry :=
  (List.range lv.size).flatMap fun h => entriesOf lv h slot

/-- The walk of `firstNamed`: an entry whose name was seen is dropped. -/
def firstNamedGo : List IsoEntry → Std.HashSet Name → List IsoEntry → List IsoEntry
  | [], _, acc => acc
  | e :: es, seen, acc =>
    if seen.contains e.ci.name then firstNamedGo es seen acc
    else firstNamedGo es (seen.insert e.ci.name) (e :: acc)

/-- **The first entry of every name** (in reverse order: the order of an
environment of distinct names is immaterial). -/
def firstNamed (es : List IsoEntry) : List IsoEntry := firstNamedGo es {} []

/-- **Module `M`'s context, from its imports' units alone**: the first
presentation of every name its levels `lv` present, with the tables of
the type formers among them. -/
def isoCtx (slot : Nat → ModSlot) (lv : ByteArray) : Env :=
  let es := firstNamed (isoEntries slot lv)
  ⟨es.map (·.ci), es.filterMap (·.tbl)⟩

/-- **The canonical index of module `M`'s context** (the specification:
`mkFEnv` of `isoCtx`).  It runs as `isoIndexFast`, one pass over the
units with no intermediate lists (`Mod.isoIndex_eq_fast`, `@[csimp]`,
`ConLeche/Verify/Modular/IsoFast.lean`). -/
def isoIndex (slot : Nat → ModSlot) (lv : ByteArray) : FEnv := mkFEnv (isoCtx slot lv)

/-- The state of `isoIndexFast`: the context so far (its constants
newest first, its tables), its name index and table map, and its size. -/
structure IsoAcc where
  n : Nat
  consts : List ConstantInfo
  tables : List ProjTable
  idx : Std.HashMap Name (Nat × ConstantInfo)
  tbls : Std.HashMap Name ProjTable

/-- One presented constant added, unless its name is there already. -/
@[inline] def IsoAcc.add (a : IsoAcc) (ci : ConstantInfo) (t : Option ProjTable) : IsoAcc :=
  if a.idx.contains ci.name then a else
  match t with
  | some t => ⟨a.n + 1, ci :: a.consts, t :: a.tables, a.idx.insert ci.name (a.n, ci),
      a.tbls.insert t.structName t⟩
  | none => ⟨a.n + 1, ci :: a.consts, a.tables, a.idx.insert ci.name (a.n, ci), a.tbls⟩

/-- Module `h`'s presented constants added (none of a module the viewer
does not load, whose unit is not read). -/
def isoAccModule (lv : ByteArray) (slot : Nat → ModSlot) (a : IsoAcc) (h : Nat) : IsoAcc :=
  if lvlAt lv h == 0 then a else
  (List.range (posCount (slot h) (lvlAt lv h))).foldl (fun a j =>
    match presentAt lv (slot h) (lvlAt lv h) j with
    | some ci => a.add ci (entryTbl ci (presentTbl (slot h) (lvlAt lv h) j))
    | none => a) a

/-- **The canonical index of a module's context, in one pass**: what
`isoIndex` computes. -/
def isoIndexFast (slot : Nat → ModSlot) (lv : ByteArray) : FEnv :=
  let a := (List.range lv.size).foldl (isoAccModule lv slot) ⟨0, [], [], {}, {}⟩
  ⟨⟨a.consts, a.tables⟩, a.idx, a.n, {}, [], a.tbls⟩

/-! ## The checks -/

/-- **The declaration fold from an index**: every record installed by
the fold's step from `fe₀`, every recorded check run at the final index,
the final environment.  `checkDecls` is this fold from the empty
environment's index (`checkDecls_eq_checkDeclsAt`). -/
def checkDeclsAt (mode : CheckMode) (pins : List NatOpPinSet) (fe₀ : FEnv)
    (ds : Array Declaration) : Except (CheckError × Nat) Env := do
  let p ← ds.foldlM (installDeclStep mode pins) (0, fe₀, #[])
  checkPendingList mode p.2.1 p.2.2.toList
  pure p.2.1.env

theorem checkDecls_eq_checkDeclsAt (mode : CheckMode) (pins : List NatOpPinSet)
    (ds : Array Declaration) : checkDecls mode pins ds = checkDeclsAt mode pins (mkFEnv Env.empty) ds :=
  rfl

/-- **A module checked in isolation**: its records, installed and
checked by the declaration fold from the canonical index of its context
built from its imports' units (`isoCtx`); the result is its own
environment (its constants and tables, then the context's). -/
def checkModuleIsolated (mode : CheckMode) (pins : List NatOpPinSet) (slot : Nat → ModSlot)
    (lv : ByteArray) (ds : Array Declaration) : Except (CheckError × Nat) Env :=
  checkDeclsAt mode pins (isoIndex slot lv) ds

/-- **A module checked at a view of the store** (what the store run
does): the same fold from the view; the result is the module's own
constants and tables (the view's environment holds nothing else). -/
def checkAtView (mode : CheckMode) (pins : List NatOpPinSet) (mb : MBase) (ds : Array Declaration) :
    Except (CheckError × Nat) Env :=
  checkDeclsAt mode pins (viewOf mb) ds

/-- An environment over a context: its own constants and tables, then
the context's. -/
def Env.over (own C : Env) : Env := ⟨own.consts ++ C.consts, own.tables ++ C.tables⟩

/-- The own part of an environment over a context (`Env.over`): what
stands before the context's constants and tables. -/
def ownPart (C E : Env) : Env :=
  ⟨E.consts.take (E.consts.length - C.consts.length),
    E.tables.take (E.tables.length - C.tables.length)⟩

/-- **A module's own constants over a store's lookup**: the store run's
final view of a module whose install pushed `own` (the canonical index
of `own`, the store below). -/
def ownView (own : Env) (mb : MBase) : FEnv := { mkFEnv own with base := { mb := some mb } }

/-! ## The name index lists every unit constant -/

/-- Pairs in strictly increasing lexicographic order. -/
def sortedLex : List (Nat × Nat) → Bool
  | a :: b :: rest => (a.1 < b.1 || (a.1 == b.1 && a.2 < b.2)) && sortedLex (b :: rest)
  | _ => true

/-- **The store's name index lists every unit constant under its name,
in module order**: every alternate list strictly increasing, and every
constant of every unit — of its private record, and every exported
presentation — an alternate of its name. -/
def idxOk (S : Store) : Bool :=
  S.idx.all (fun m => m.toList.all fun (_, l) => sortedLex l) &&
  (List.range S.slots.size).all fun h =>
    (List.range (S.slot h).prv.priv.size).all (fun j => match (S.slot h).prv.priv[j]? with
      | some c => (S.alts c.name).contains (h, j)
      | none => true) &&
    (List.range (S.slot h).exp.at1.size).all (fun j => match ((S.slot h).exp.at1[j]?).join with
      | some c => (S.alts c.name).contains (h, j)
      | none => true)

end ConLeche.Cached.Mod
