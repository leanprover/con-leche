module

public import ConLeche.Driver.Modular
public import ConLeche.Driver.Schedule
public import ConLeche.Driver.Compare
public import ConLeche.Driver.CompareModule

/-!
# What a run does, by its request, generic in the IO class (task #424)

`runArgs` (`ConLeche/Driver/Cli.lean`) reads its arguments into a request (`Req`): a
lean4export stream, the import closure of root modules from their `.olean` files, one module
checked alone against its context (`checkModuleG`, `ConLeche/Driver/Worker.lean`), or the
closure's import graph alone (`Graph.checkGraphG`, `ConLeche/Driver/Graph.lean`).  `runReq` runs the request's driver,
`checkMainG`, generic in the IO class: the binary runs it at `IO`
(`ConLeche/Driver/Cli.lean`, `Main.lean`), and `runArgs_accept`
(`ConLeche/Verify/Driver/Main.lean`) is about the whole run in the
model, at the arguments `-- <file>`.
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche

/-- **A run's request**: the driver and its configuration. -/
inductive Req where
  /-- a lean4export stream (`checkMainG` on `.ndjson`) -/
  | stream (file : String) (mode : CheckMode) (maxNatSize : Nat) (pace : Pace) (jobs : Nat)
  /-- the import closure of root modules (`checkMainG` on `.oleans`) -/
  | oleans (searchPath : List System.FilePath) (roots : Array Name)
      (constants : Option (Array Name)) (mode : CheckMode) (maxNatSize : Nat) (pace : Pace)
      (jobs : Nat)
  /-- the import graph of root modules' closure (`Graph.checkGraphG`); `cmp`: the solution, the
  root a challenge whose header it is added to (`cmpExtra`, task #608) -/
  | graph (searchPath : List System.FilePath) (roots : List Name) (jobs : Nat)
      (cmp : Option Name)
  /-- every module of a closure, each against its context, in one process (`checkModularG`) -/
  | modular (searchPath : List System.FilePath) (root : Name) (mode : CheckMode)
      (maxNatSize : Nat) (pace : Pace) (jobs : Nat)
  /-- every module of a closure, one worker process each (`scheduleG`, outside the theorem);
  `jobsGiven`: `--jobs` was given -/
  | schedule (searchPath : List System.FilePath) (root : Name) (cmp : Option Name)
      (opts : List String) (mode : CheckMode) (maxNatSize : Nat) (pace : Pace) (jobs : Nat)
      (jobsGiven : Bool)
  /-- a challenge and its solution, compared, and the solution's closure checked
  (`compareG`) -/
  | compare (r : CmpReq) (mode : CheckMode) (maxNatSize : Nat) (pace : Pace) (jobs : Nat)
  /-- one module against its context (`checkModuleG`) -/
  | module (searchPath : List System.FilePath) (m : Name) (mode : CheckMode) (maxNatSize : Nat)
      (pace : Pace) (jobs : Nat)
  /-- a challenge against its solution, as one module of a modular run (`checkCmpModuleG`,
  task #608) -/
  | cmpModule (searchPath : List System.FilePath) (c s : Name) (mode : CheckMode) (pace : Pace)
      (jobs : Nat)

/-- **A request run** by its driver. -/
def runReq {μ : Type → Type} [CheckerIO μ] : Req → μ UInt8
  | .stream file mode maxNatSize pace jobs => checkMainG (.ndjson file) mode maxNatSize pace jobs
  | .oleans sp roots cs mode maxNatSize pace jobs =>
    checkMainG (.oleans sp roots cs) mode maxNatSize pace jobs
  | .graph sp roots jobs cmp =>
    Graph.checkGraphG sp roots jobs (match cmp, roots with
      | some s, [c] => Graph.cmpExtra c s
      | _, _ => fun _ => #[])
  | .modular sp root mode maxNatSize pace jobs => checkModularG sp root mode maxNatSize pace jobs
  | .schedule sp root cmp opts mode maxNatSize pace jobs jobsGiven =>
    scheduleG sp root cmp opts mode maxNatSize pace jobs jobsGiven
  | .compare r mode maxNatSize pace jobs => compareG r mode maxNatSize pace jobs
  | .module sp m mode maxNatSize pace jobs => do
    let (R, T) ← workerTables sp m
    checkModuleG (T.reads R) R m mode maxNatSize pace jobs
  | .cmpModule sp c s mode pace jobs => do
    let (R, T) ← workerTables sp c
    checkCmpModuleG (T.reads R) c s mode pace jobs

end ConLeche.Driver
