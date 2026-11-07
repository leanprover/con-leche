module

public import ConLeche.Driver.Worker
public import ConLeche.Driver.Graph

@[expose] public section

/-!
# The one-process mode: every module of a closure checked as its worker checks it

`con-leche --olean --modular --search-path=DIRS -- ROOT` checks every module of `ROOT`'s import
closure on its own, as the worker (`checkModuleG`, `ConLeche/Driver/Worker.lean`) checks it, in
one process (DESIGN #460 §3, ruling 8):

1. **The graph** (`graphOf`, `ConLeche/Driver/Graph.lean`): the closure's headers read, its
   import graph checked acyclic, every import resolved, as `--check-graph` does.
2. **The tables, read once** (`readModTable`, on the parallel map): every module of the closure
   located (`findModule`), and its two parts' name positions (`readPartNamesAt`, the private and
   the exported level); its imports are the graph's.  The tables are marked persistent before
   any worker thread starts.
3. **Every module, its worker's steps** (`checkModuleG` at `alone := false`), on the worker map
   (`CheckerIO.parMapWorkers`, one module claimed at a time), its reads answered from the tables
   (`ModTables.reads`): a module's imports and name positions from them, a view's files read at
   the location found once; a read the tables do not hold is the search path's.  Each module's
   own checks run on one thread; nothing a module builds is marked persistent, so it is freed
   with the module.
4. **The verdict**: a line per module (the worker's, naming the module), then the run's: exit 0
   exactly when every module's worker step answered 0; otherwise the code of the first module,
   in the graph's order, that did not.

Since the reads refine the search path's (`ConLeche/Verify/Driver/Shared.lean`), what an exit 0
of the worker at a module establishes (`WorkerAccepted`) holds of every module of a run that
exits 0 (`ConLeche/Verify/Driver/Modular.lean`).
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-- **What the one-process mode reads of a module up front.** -/
structure ModTable where
  name : Name
  /-- where its files are -/
  loc : Located
  /-- its imports, off its header -/
  imports : Array ImportRec
  /-- its private part's name positions -/
  priv : NamePositions
  /-- its exported part's name positions -/
  expo : NamePositions

/-- **A module's table**: located, its two parts' name positions read; its imports the graph's. -/
def readModTable {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (e : Graph.Node) :
    μ (Except CheckError ModTable) := do
  match ← findModule sp e.1 with
  | .error err => pure (.error err)
  | .ok loc =>
    match ← readPartNamesAt loc (e.1, .private) with
    | .error err => pure (.error err)
    | .ok priv =>
      match ← readPartNamesAt loc (e.1, .exported) with
      | .error err => pure (.error err)
      | .ok expo => pure (.ok { name := e.1, loc, imports := e.2, priv, expo })

/-- **The tables of a closure**, by module name. -/
structure ModTables where
  index : Std.HashMap Name Nat
  mods : Array ModTable

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

/-- **The reads answered from the tables**: a module's imports and its parts' name positions
from its table, a view's files read at the location in it; what the tables do not hold, on the
search path. -/
def ModTables.reads {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (T : ModTables) :
    OleanReads μ where
  imports m := match T.find m with
    | some t => pure (.ok t.imports)
    | none => moduleImports sp m
  files m level := match T.find m with
    | some t => readFilesAt t.loc m level
    | none => readFiles sp m level
  names x := match T.find x.1 with
    | some t =>
      match x.2 with
      | .private => pure (.ok t.priv)
      | .exported => pure (.ok t.expo)
      | .server => readPartNamesAt t.loc x
    | none => readPartNames sp x

/-- One module of the run: its worker's steps over the tables, its code. -/
def modularStep {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (T : ModTables)
    (mode : CheckMode) (_ : Unit) (m : Name) : μ (Unit × Except Empty (Name × UInt8)) := do
  let c ← checkModuleG (T.reads sp) sp m mode .off 1 false
  pure ((), .ok (m, c))

/-- **The one-process mode**, generic in the IO class (see the module docstring). -/
def checkModularG {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (root : Name)
    (mode : CheckMode) (pace : Pace) (jobs : Nat) : μ UInt8 := do
  let t0 ← clockMs
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let say (line : String) : μ Unit := do
    if pace.on then
      let now ← clockMs
      diagLine s!"con-leche: modular: {line} t={ConLeche.Cached.msSecs (now - t0)}s"
  match ← Graph.graphOf sp [root] jobs with
  | .error e =>
    diagLine s!"con-leche: graph: {e}"
    return e.exitCode
  | .ok C =>
    say s!"graph: acyclic, {C.size} modules"
    match ← CheckerIO.parMapExcept jobs (readModTable sp) C.toList with
    | .error e =>
      diagLine s!"con-leche: {e} ({modeTag})"
      return e.exitCode
    | .ok ts =>
      let T := ModTables.ofArray ts.toArray
      CheckerIO.liftIO (markShared T)
      say s!"tables read: {T.mods.size} modules, \
        {T.mods.foldl (fun n t => n + t.priv.consts.size) 0} names"
      let (_, res) ← CheckerIO.parMapWorkers jobs (fun _ => ()) (modularStep sp T mode)
        (C.toList.map (·.1))
      match res with
      | .error e => nomatch e
      | .ok rs =>
        say "done"
        match rs.find? (·.2 != 0) with
        | none =>
          outLine s!"con-leche: accepted {rs.length} modules ({modeTag})"
          return 0
        | some (m, c) =>
          diagLine s!"con-leche: {(rs.filter (·.2 != 0)).length} of {rs.length} modules not \
            accepted; the first in the graph's order: {m} ({modeTag})"
          return c

end ConLeche.Driver
