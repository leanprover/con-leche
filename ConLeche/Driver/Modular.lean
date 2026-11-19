module

public import ConLeche.Driver.Worker
public import ConLeche.Driver.Graph
public import ConLeche.Driver.Tables
public import ConLeche.Driver.CompareModule

@[expose] public section

/-!
# The one-process mode: every module of a closure checked as its worker checks it

`con-leche --olean --modular --search-path=DIRS -- ROOT` checks every module of `ROOT`'s import
closure on its own, as the worker (`checkModuleG`, `ConLeche/Driver/Worker.lean`) checks it, in
one process (DESIGN #460 §3, ruling 8):

1. **The graph** (`graphOf`, `ConLeche/Driver/Graph.lean`): the closure's headers read, its
   import graph checked acyclic, every import resolved, as `--check-graph` does; the roots of
   its modules resolved there once, for every later read.
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
With `--compare` (`sol`: the solution `S` of the challenge `root`, task #608), the graph is the
closure of the challenge and its solution (`Graph.cmpExtra`: the solution added to the
challenge's header), every module's table holds its header's imports, and the challenge's step is
the compare worker's (`checkCmpModuleG`).  The challenge's closure is read through the
challenge's lookup `spC` (with `--trusted-search-path`, the trusted path alone): its graph walked
there (a module of it only the search path holds is invalid input, `why` saying so), its tables
read there, and its modules' steps read through those tables and that lookup; every other
module through the solution's lookup `sp` (the trusted path, then the search path).

4. **The verdict**: a line per module (the worker's, naming the module), then the run's: exit 0
   exactly when every module's worker step answered 0; otherwise the code of the first module,
   in the graph's order, that did not.

Since the reads refine the search path's (`ConLeche/Verify/Driver/Shared.lean`), what an exit 0
of the worker at a module establishes (`WorkerAccepted`) holds of every module of a run that
exits 0 (`ConLeche/Verify/Driver/Modular.lean`).
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-- **A module's table**: located, its two parts' name positions read; its imports the graph's. -/
def readModTable {μ : Type → Type} [CheckerIO μ] (sp : Roots) (e : Graph.Node) :
    μ (Except CheckError ModTable) := do
  match ← findModule sp e.1 with
  | .error err => pure (.error err)
  | .ok loc =>
    match ← readPartNamesAt loc (e.1, .private) with
    | .error err => pure (.error err)
    | .ok priv =>
      match ← readPartNamesAt loc (e.1, .exported) with
      | .error err => pure (.error err)
      | .ok expo => pure (.ok { name := e.1, loc, imports := some e.2, priv := some priv,
                                expo := some expo })

/-- One module's code: its worker's steps over the tables; at a compared challenge (`cmp`: the
challenge and its solution), the compare worker's, and a module of the challenge's closure
(`chal`) through the challenge's lookup `spC` and its tables `TC`. -/
def stepCode {μ : Type → Type} [CheckerIO μ] (spC sp : Roots) (TC T : ModTables)
    (chal : Name → Bool) (cmp : Option (Name × Name)) (mode : CheckMode) (maxNatSize : Nat)
    (m : Name) : μ UInt8 :=
  match cmp with
  | some (C, S) =>
    if m == C then checkCmpModuleG (TC.reads spC) (T.reads sp) C S mode .off 1
    else if chal m then checkModuleG (TC.reads spC) spC m mode maxNatSize .off 1 false
    else checkModuleG (T.reads sp) sp m mode maxNatSize .off 1 false
  | none => checkModuleG (T.reads sp) sp m mode maxNatSize .off 1 false

/-- One module of the run, with its code. -/
def modularStep {μ : Type → Type} [CheckerIO μ] (spC sp : Roots) (TC T : ModTables)
    (chal : Name → Bool) (cmp : Option (Name × Name)) (mode : CheckMode) (maxNatSize : Nat)
    (_ : Unit) (m : Name) : μ (Unit × Except Empty (Name × UInt8)) := do
  let c ← stepCode spC sp TC T chal cmp mode maxNatSize m
  pure ((), .ok (m, c))

/-- The imports a compared run adds: the solution's to the challenge's header. -/
def modExtra (root : Name) : Option Name → Name → Array ImportRec
  | some S => Graph.cmpExtra root S
  | none => fun _ => #[]

/-- A node of the graph with its header's imports (the added ones dropped). -/
def headerNode (extra : Name → Array ImportRec) (e : Graph.Node) : Graph.Node :=
  (e.1, e.2.extract 0 (e.2.size - (extra e.1).size))

/-- **The challenge's closure** of a compared run, through the challenge's lookup `spC`: its
graph and the lookup with its roots resolved; none for a run that compares nothing.  A failed walk
is the run's exit code, after its line (`why`: a module of the closure only the search path
holds). -/
def chalGraph {μ : Type → Type} [CheckerIO μ] (spC : Roots) (root : Name) (sol : Option Name)
    (why : μ (Option String)) (modeTag : String) (jobs : Nat) :
    μ (Except UInt8 (Array Graph.Node × Roots)) :=
  match sol with
  | none => pure (.ok (#[], spC))
  | some _ => do
    match ← Graph.graphOf spC [root] jobs with
    | .error e =>
      if let some w := ← why then
        diagLine s!"con-leche: {w} ({modeTag})"
        return .error 1
      diagLine s!"con-leche: graph: {e}"
      return .error e.exitCode
    | .ok r => pure (.ok r)

/-- **The one-process mode**, generic in the IO class (see the module docstring). -/
def checkModularG {μ : Type → Type} [CheckerIO μ] (spC sp : Roots) (root : Name)
    (sol : Option Name) (why : μ (Option String)) (mode : CheckMode) (maxNatSize : Nat)
    (pace : Pace) (jobs : Nat) : μ UInt8 := do
  let t0 ← clockMs
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
  let say (line : String) : μ Unit := do
    if pace.on then
      let now ← clockMs
      diagLine s!"con-leche: modular: {line} t={ConLeche.Cached.msSecs (now - t0)}s"
  match ← Graph.graphOf sp [root] jobs (modExtra root sol) with
  | .error e =>
    diagLine s!"con-leche: graph: {e}"
    return e.exitCode
  | .ok (C, sp) =>
    say s!"graph: acyclic, {C.size} modules"
    match ← chalGraph spC root sol why modeTag jobs with
    | .error c => return c
    | .ok (CC, spC) =>
    match ← CheckerIO.parMapExcept jobs (readModTable sp)
        (C.toList.map (headerNode (modExtra root sol))) with
    | .error e =>
      diagLine s!"con-leche: {e} ({modeTag})"
      return e.exitCode
    | .ok ts =>
    match ← CheckerIO.parMapExcept jobs (readModTable spC) CC.toList with
    | .error e =>
      diagLine s!"con-leche: {e} ({modeTag})"
      return e.exitCode
    | .ok tsC =>
      let T := ModTables.ofArray ts.toArray
      let TC := ModTables.ofArray tsC.toArray
      CheckerIO.liftIO (markShared T)
      CheckerIO.liftIO (markShared TC)
      say s!"tables read: {T.mods.size} modules, \
        {T.mods.foldl (fun n t => n + (t.priv.map (·.consts.size)).getD 0) 0} names"
      let chal := Graph.namesOf CC.toList
      let (_, res) ← CheckerIO.parMapWorkers jobs (fun _ => ())
        (modularStep spC sp TC T chal.contains (sol.map (root, ·)) mode maxNatSize)
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
