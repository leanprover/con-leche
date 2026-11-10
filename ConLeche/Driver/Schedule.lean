module

public import ConLeche.Driver.Graph
public import ConLeche.Driver.ScheduleIO

@[expose] public section

/-!
# The scheduler: one worker process per module (outside the theorem)

`con-leche --olean --schedule[-OPT=VALUE…] --search-path=DIRS -- ROOT`: the root's closure by
the graph check (`graphOf`, as `--check-graph`), then one worker process per module of it
(`con-leche --olean --module --jobs=T`, the binary itself; `--jobs` is the run's thread budget
and `T` each worker's share, `Schedule.threadCap`), started, watched, killed and
logged by `Schedule.run` (`ConLeche/Driver/ScheduleIO.lean`, through `CheckerIO.liftIO`), and
the run's verdict from their exit codes (`Schedule.summary`).

**What it claims: nothing a theorem needs.**  The modular statement is a composition of what
each worker's exit 0 and the graph check's exit 0 say (`runArgs_module_accept`,
`runArgs_graph_accept`), on one snapshot (`ConLeche/Frontend/CheckerIO.lean`'s assumption for
several runs); the scheduler only starts those runs and reports their exits.  Its own exit code
is `liftIO`'s answer, which the model leaves free, and no theorem is about a `--schedule` run.
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
its `--schedule` flags. -/
def scheduleG {μ : Type → Type} [CheckerIO μ] (sp : SearchPath) (root : Name)
    (opts : List String) (mode : CheckMode) (maxNatSize : Nat) (pace : Pace) (jobs : Nat) :
    μ UInt8 := do
  let modeTag : String := match mode with
    | .verified => "--verified"
    | .trusted => "--trusted"
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
      let args (m : Name) (t : Nat) : Array String :=
        #["--olean", "--module", s!"--jobs={t}", modeTag, s!"--max-nat-size={maxNatSize}",
          "--search-path=" ++ dirs, "--",
          Schedule.spell m]
      CheckerIO.liftIO (Schedule.runAll parseModName args (Schedule.declCount (μ := IO) ↑sp) mods
        o jobs modeTag)

end ConLeche.Driver
