module

public import ConLeche.Driver.Modular
public import ConLeche.Driver.Schedule

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
  /-- the import graph of root modules' closure (`Graph.checkGraphG`) -/
  | graph (searchPath : List System.FilePath) (roots : List Name) (jobs : Nat)
  /-- every module of a closure, each against its context, in one process (`checkModularG`) -/
  | modular (searchPath : List System.FilePath) (root : Name) (mode : CheckMode)
      (maxNatSize : Nat) (pace : Pace) (jobs : Nat)
  /-- every module of a closure, one worker process each (`scheduleG`, outside the theorem);
  `jobsGiven`: `--jobs` was given; `stackKb`: the workers' stack size, KiB -/
  | schedule (searchPath : List System.FilePath) (root : Name) (opts : List String)
      (mode : CheckMode) (maxNatSize : Nat) (pace : Pace) (jobs : Nat) (jobsGiven : Bool)
      (stackKb : Option Nat)
  /-- one module against its context (`checkModuleG`) -/
  | module (searchPath : List System.FilePath) (m : Name) (mode : CheckMode) (maxNatSize : Nat)
      (pace : Pace) (jobs : Nat)

/-- **A request run** by its driver. -/
def runReq {μ : Type → Type} [CheckerIO μ] : Req → μ UInt8
  | .stream file mode maxNatSize pace jobs => checkMainG (.ndjson file) mode maxNatSize pace jobs
  | .oleans sp roots cs mode maxNatSize pace jobs =>
    checkMainG (.oleans sp roots cs) mode maxNatSize pace jobs
  | .graph sp roots jobs => Graph.checkGraphG sp roots jobs
  | .modular sp root mode maxNatSize pace jobs => checkModularG sp root mode maxNatSize pace jobs
  | .schedule sp root opts mode maxNatSize pace jobs jobsGiven stackKb =>
    scheduleG sp root opts mode maxNatSize pace jobs jobsGiven stackKb
  | .module sp m mode maxNatSize pace jobs => do
    let (R, T) ← workerTables sp m
    checkModuleG (T.reads R) R m mode maxNatSize pace jobs

end ConLeche.Driver
