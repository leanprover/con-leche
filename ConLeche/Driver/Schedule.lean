module

public import ConLeche.Driver.Graph
public import ConLeche.Driver.Schedule.Run

@[expose] public section

/-!
# The scheduler: one worker process per module (outside the theorem)

`con-leche --olean --schedule[-OPT=VALUE…] --search-path=DIRS -- ROOT`: the root's closure by
the graph check (`graphOf`, as `--check-graph`), then one worker process per module of it
(`con-leche --olean --module --jobs=T`, the binary itself; `--jobs` is the run's thread budget
and `T` each worker's share, `Schedule.threadCap`), and the run's verdict from their exit codes
(`Schedule.summary`).  With `--schedule-commands` it starts nothing and prints the commands that
check the closure instead (`Schedule.printCommands`).  This module is the glue: the closure, the
workers' arguments, `declCount`, and the one `CheckerIO.liftIO` call.  The scheduler itself is
the subtree `ConLeche/Driver/Schedule/`:

* `Engine.lean`: the policy, pure and generic in what a job is: admission against the memory
  budget, the planning budget learned from surprises, the head slot, the kills' victims, the
  thread budget, the known sizes, the start order;
* `Worker.lean`: what con-leche is to it: the worker's arguments, the commands, shell quoting,
  what the worker printed and its verdict from its exit;
* `Log.lean`: the log's lines, reading it back, the state a resumed run starts from;
* `Status.lean`: the status part, the finish and heartbeat lines, the estimate, the statistics;
* `Proc.lean`: what it reads of the system (`/proc`, the cgroup's OOM-kill counter);
* `Run.lean`: the IO loop: the processes started, watched and killed, the log written, the
  signals; the one module that starts a process, kills one or writes a file.

**What it claims: nothing a theorem needs.**  The modular statement is a composition of what
each worker's exit 0 and the graph check's exit 0 say (`runArgs_module_accept`,
`runArgs_graph_accept`), on one snapshot (`ConLeche/Frontend/CheckerIO.lean`'s assumption for
several runs); the scheduler only starts those runs and reports their exits, and the commands it
prints are those runs.  Its own exit code is `liftIO`'s answer, which the model leaves free, and
no theorem is about a `--schedule` run.
-/

namespace ConLeche.Driver

open ConLeche ConLeche.Frontend.Olean

/-- **A module's declarations, read cheaply before its worker starts** (`Schedule.threadsFor`):
the constants of its private view, `readFiles` at `.private` (the module's own files) and
`moduleSkel` over the view's region: the constants array's length, no name or expression decoded.
The reads are the class's own (`CheckerIO.readBinFile`); the scheduler runs this at the binary's
`IO`, inside its `liftIO`, and the worker reads the same files moments later, from the page
cache.  `none` where they do not read (the worker then says why). -/
def Schedule.declCount {μ : Type → Type} [CheckerIO μ] (sp : Roots) (m : Name) :
    μ (Option Nat) := do
  match ← readFiles sp m .private with
  | .error _ => return none
  | .ok f =>
    return (f.viewRegion .private).bind fun (r, a) => (moduleSkel r a).map (·.consts.length)

/-- **The scheduler**, generic in the IO class (see the module docstring); `opts` the values of
its `--schedule` flags, `jobsGiven` whether `--jobs` was given (the printed commands carry it only
then). -/
def scheduleG {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (root : Name)
    (opts : List String) (mode : CheckMode) (maxNatSize : Nat) (pace : Pace) (jobs : Nat)
    (jobsGiven : Bool) : μ UInt8 := do
  -- the heartbeat: `--progress=N` after N ms without a line (at least a second), `Ss` after S
  -- seconds; a percentage has no meaning here (every module's line says how far the run is)
  let beat : Except String Nat := match pace with
    | .off => .ok 0
    | .every n => .ok (max n 1000)
    | .seconds s => .ok (s * 1000)
    | .percent _ => .error "--schedule takes --progress=N (milliseconds) or --progress=Ss, \
        not a percentage"
  match beat >>= fun h => (Schedule.Opts.parse opts { heartbeat := h }) with
  | .error msg =>
    diagLine s!"con-leche: {msg}"
    return 3
  | .ok o =>
    match ← Graph.graphOf ↑sp [root] jobs with
    | .error e =>
      diagLine s!"con-leche: graph: {e}"
      return e.exitCode
    | .ok (C, _) =>
      let mods := C.map (·.1)
      let dirs := ":".intercalate (sp.map toString)
      if o.commands then
        CheckerIO.liftIO (Schedule.printCommands dirs root mods o
          (Schedule.workerArgs mode maxNatSize dirs (if jobsGiven then some jobs else none)))
      else
        CheckerIO.liftIO (Schedule.runAll parseModName
          (fun m t => Schedule.workerArgs mode maxNatSize dirs (some t) m)
          (Schedule.declCount (μ := IO) ↑sp) mods o jobs (Schedule.modeTag mode))

end ConLeche.Driver
