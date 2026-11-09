module

public import ConLeche.Frontend.Olean

@[expose] public section

/-!
# The tables a run reads up front: each module located once

A worker reads a module's files in several phases (its header in the header fixpoint, its name
positions, its views in the reach), and each read names the module, not its files.  Locating a
module on the search path (`findModule`) asks where its root is, so a process that located a
module at every read would locate most modules two or three times (task #509), and a process
resolves each root once (`Roots`, task #511).  The
tables hold what a run has read of a module once: where its files are (`loc`), and, where read,
its imports and its two parts' name positions.  The reads answered from them (`ModTables.reads`)
take a module's location from its table and read its files there; what a table does not hold
is read at that location, and a module without a table is read on the search path.

* The one-process mode (`ConLeche/Driver/Modular.lean`) reads every module's table, all of it,
  up front.
* A worker (`--module`, `workerTables`) reads its own module's table (its location, its private
  view's files, which the home then takes from it, and its private part's name positions), then runs its header fixpoint once up front with each
  module's header read at its location and the location entered in the tables (the state of
  the fixpoint's run, `tabImports`); the worker's phases then read every loaded module at the
  location found there.

In the model, every table is read off the snapshot (`TablesOk`), so the reads answered from the
tables refine the search path's (`modTables_within`, `ConLeche/Verify/Driver/Tables.lean`).
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-- **What a run has read of a module.** -/
structure ModTable where
  name : Name
  /-- where its files are -/
  loc : Located
  /-- its imports, off its header, where read -/
  imports : Option (Array ImportRec)
  /-- its private part's name positions, where read -/
  priv : Option NamePositions
  /-- its exported part's name positions, where read -/
  expo : Option NamePositions
  /-- its private view's files, where read (a worker's own module: the home reads them, task
  #508) -/
  files : Option ModFiles := none

/-- **The tables**, by module name. -/
structure ModTables where
  index : Std.HashMap Name Nat := {}
  mods : Array ModTable := #[]

/-- The tables with one more module's. -/
def ModTables.push (T : ModTables) (t : ModTable) : ModTables :=
  { index := T.index.insert t.name T.mods.size, mods := T.mods.push t }

/-- The tables of a list of modules. -/
def ModTables.ofArray (ts : Array ModTable) : ModTables :=
  { index := ts.foldl (fun (acc : Std.HashMap Name Nat × Nat) t =>
      (acc.1.insert t.name acc.2, acc.2 + 1)) ({}, 0) |>.1, mods := ts }

/-- A module's table, if the tables hold one of that name. -/
def ModTables.find (T : ModTables) (m : Name) : Option ModTable :=
  match T.index[m]? with
  | some i =>
    match T.mods[i]? with
    | some t => if t.name == m then some t else none
    | none => none
  | none => none

/-- **The reads answered from the tables**: what a module's table holds from it, the rest read
at the location in it; a module without a table, on the search path. -/
def ModTables.reads {μ : Type → Type} [CheckerIO μ] (sp : Roots) (T : ModTables) :
    OleanReads μ where
  imports m := match T.find m with
    | some t =>
      match t.imports with
      | some is => pure (.ok is)
      | none => readImportsAt t.loc m
    | none => moduleImports sp m
  files m level := match T.find m with
    | some t =>
      match level, t.files with
      | .private, some f => pure (.ok f)
      | _, _ => readFilesAt t.loc m level
    | none => readFiles sp m level
  names x := match T.find x.1 with
    | some t =>
      match x.2, t.priv, t.expo with
      | .private, some p, _ => pure (.ok p)
      | .exported, _, some e => pure (.ok e)
      | _, _, _ => readPartNamesAt t.loc x
    | none => readPartNames sp x

/-- **A module's imports, its location entered in the tables**: its root resolved, the module
located, its header read there. -/
def tabImports {μ : Type → Type} [CheckerIO μ] (n : Name) :
    StateT (Roots × ModTables) μ (Except CheckError (Array ImportRec)) := fun (R, T) => do
  let R ← R.resolve n
  match ← findModule R n with
  | .error e => pure (.error e, (R, T))
  | .ok loc =>
    match ← readImportsAt loc n with
    | .error e => pure (.error e, (R, T))
    | .ok is =>
      pure (.ok is, (R, T.push { name := n, loc, imports := some is, priv := none, expo := none }))

/-- **A worker's tables** at module `m`: `m` located, its private view's files read there and
kept (the home reads them, so that they are read once), its private part's name positions off
them, then its header fixpoint (`headerFixpoint`) over `tabImports`, which locates each module it
loads once; beside them, the search path with the roots of those modules resolved, each once.
Nothing here fails: where a read fails, the tables hold what was read before it, and the
worker's own read of the rest reports the failure. -/
def workerTables {μ : Type → Type} [CheckerIO μ] (sp : Roots) (m : Name) :
    μ (Roots × ModTables) := do
  let R ← sp.resolve m
  match ← findModule R m with
  | .error _ => pure (R, {})
  | .ok loc =>
    match ← readFilesAt loc m .private with
    | .error _ =>
      pure (R, ModTables.push {} { name := m, loc, imports := none, priv := none, expo := none })
    | .ok f =>
    match namesOf m f .private with
    | .error _ =>
      pure (R, ModTables.push {} { name := m, loc, imports := none, priv := none, expo := none,
                                   files := some f })
    | .ok own =>
      let T0 := ModTables.push {} { name := m, loc, imports := none, priv := some own, expo := none,
                                    files := some f }
      let (_, RT) ← (headerFixpoint tabImports own.header.isModule own.header.imports).run (R, T0)
      pure RT

end ConLeche.Driver
