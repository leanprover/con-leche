module

public import ConLeche.Driver.ParInstall
public import ConLeche.Driver.CheckPool

/-!
# The driver: `checkDeclsIO` and the phase sequencing

Part of the proof-carrying driver (`ConLeche/Driver/*`; the CLI —
argument parsing, I/O, exit codes — is `Cli.lean`, `Main.lean`).

`checkDeclsIO` is **the driver**: the install (`installPhase`,
`Driver/ParInstall.lean`: the commit thread with `n` workers at
`--jobs=<n>`, alone at `--jobs=1`) then the check phase, `checkPool`
(`Driver/CheckPool.lean`), and what comes out is
the environment together with the proof that the fold `checkDecls`
(`ConLeche/Cached/Installed.lean`) returns it — the subject of the main
theorem `ConLeche.model_exists` (`ConLeche/MainTheorem.lean`).
The driver's sequencing `checkMainG` (`ConLeche/Driver/CheckMain.lean`,
generic in the IO class) runs it through `CheckerIO.liftIO` and turns
the result into the verdict line and the exit code `Main.lean`'s `main`
returns.
-/

@[expose] public section

open ConLeche

namespace ConLeche.Driver

/-- The end-of-run statistics (performance-only): the phase times, the
install's and the check's reports (`PoolRep.line`, the slowest five of
each), the peak resident set.  Every line starts `con-leche: stats:`. -/
def printStats (err : IO.FS.Stream) (parseMs installMs : Nat) (checkMs : Option Nat)
    (inst : PoolRep) (instLabel : Nat → String)
    (chk : Option PoolRep) (chkLabel : Nat → String) : IO Unit := do
  let line (l : String) : IO Unit := err.putStr s!"con-leche: stats: {l}\n"
  let secs := ConLeche.Cached.msSecs
  line s!"phases: parse {secs parseMs}s, install {secs installMs}s, check \
    {match checkMs with | some c => s!"{secs c}s" | none => "not reached"}"
  line inst.line
  line (inst.topLine "installs" instLabel)
  if let some c := chk then
    line c.line
    line (c.topLine "checks" chkLabel)
  if let some r ← peakRss then line s!"peak RSS {r}"
  err.flush

/-- What the install hands the check phase, and when it finished. -/
structure Installed (mode : ConLeche.CheckMode) (ds : Array ConLeche.Declaration) where
  tCheck : Nat
  run : ConLeche.Cached.DeferredRun mode ConLeche.natOpPinSets ds.toList (0, mkFEnv Env.empty, #[])
  /-- the jobs in fold order -/
  order : Array ConLeche.Cached.Job
  horder : order = ConLeche.Cached.jobOrder run.p.2.2 run.D

/-- The check phase's jobs of an install: the recorded value checks and the deferred
block checks, in fold order. -/
def Installed.jobs {mode : ConLeche.CheckMode} {ds : Array ConLeche.Declaration}
    (i : Installed mode ds) : Jobs :=
  ⟨i.run.p.2.1, i.run.p.2.2, i.run.D, i.order⟩

/-- A heartbeat line (`--progress`). -/
def beat (err : IO.FS.Stream) (pace : Pace) (line : String) : IO Unit := do
  if pace.on then
    err.putStr s!"con-leche: {line}\n"
    err.flush

/-- The first line of a run: what it is reading. -/
def readStarts (pace : Pace) (label : String) : IO Unit := do
  beat (← IO.getStderr) pace s!"reading {label}"

/-- The persistent mark of what the check phase reads (`installAndMark` says why). -/
def markJobs (fe : ConLeche.FEnv) (pend : Array ConLeche.Cached.PendingCheck)
    (order : Array ConLeche.Cached.Job) : IO Unit := do
  let _ ← unsafe Runtime.markPersistent fe
  let _ ← unsafe Runtime.markPersistent pend
  let _ ← unsafe Runtime.markPersistent order

/-- **The install, up to the check phase**: `installPhase` (with `jobs` workers beside the
commit thread at `--jobs=<n>`, none at `--jobs=1`), its heartbeat, and the persistent mark
at the phase boundary.  A failed install prints its summary here.  `joinWorkers` holds the
join of the install's workers, once they are started: the caller's on every path out, at
the very end. -/
def installAndMark (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (pace : Pace) (total t0 tParse jobs : Nat)
    (instRepR : IO.Ref (IO PoolRep)) (joinWorkers : IO.Ref (BaseIO Unit))
    (ds : Array ConLeche.Declaration) (instLabel : Nat → String) :
    IO (Except (ConLeche.CheckError × Nat) (Installed mode ds)) := do
  let secs (ms : Nat) : String := ConLeche.Cached.msSecs ms
  -- the install's worker count: none at `--jobs=1`, where the commit
  -- thread installs every record itself
  let installed ← installPhase mode err (pace.strideFor total) total t0 (if jobs ≤ 1 then 0 else jobs)
    instRepR joinWorkers ds
  match installed with
  | .error e =>
    let now ← IO.monoMsNow
    beat err pace s!"install failed at {e.2}/{total} t={secs (now - t0)}s \
      (install {secs (now - tParse)}s)"
    beat err pace s!"done: parse {secs (tParse - t0)}s, install {secs (now - tParse)}s, \
      check not reached t={secs (now - t0)}s"
    printStats err (tParse - t0) (now - tParse) none (← (← instRepR.get)) instLabel none (fun _ => "")
    return .error e
  | .ok dr =>
    let tCheck ← IO.monoMsNow
    let i : Installed mode ds := ⟨tCheck, dr, ConLeche.Cached.jobOrder dr.p.2.2 dr.D, rfl⟩
    let J := i.jobs
    beat err pace s!"install done: {total} declarations installed, \
      {J.order.size} checks pending ({dr.D.size} of them inductive blocks) t={secs (tCheck - t0)}s \
      (install {secs (tCheck - tParse)}s)"
    -- **THE PERSISTENT MARK AT THE PHASE BOUNDARY.**  The installed
    -- environment is complete and READ-ONLY from here on: every
    -- recorded check reads a prefix view of it from a fresh memo state
    -- and writes nothing back.  The check phase runs on worker threads
    -- at every `--jobs=<n>`, so the runtime marks that graph
    -- MULTI-THREADED and every reference count on it becomes an atomic
    -- read-modify-write on a cache line all the workers touch — pure
    -- overhead, since nothing in the graph is freed or mutated again.
    -- Marking it PERSISTENT instead removes the counting altogether:
    -- on the pool that is worth 19-50 % of the run's cycles and
    -- 18-32 % of its WALL TIME, growing with the worker count, and
    -- 3.5 % at `--jobs=1`.  (The check phase is on a thread of its own
    -- in that lane too, because phase B's per-record memo state is
    -- allocated out of the running thread's own mimalloc heap and the
    -- main thread's heap is the one parse and install have just
    -- fragmented: the same instructions out of a FRESH heap run at
    -- 2.68 IPC against 1.29, with 24x fewer demand fills from DRAM per
    -- instruction — a factor of two in wall time at Mathlib scale.
    -- The measurement is DESIGN.md's task #269 section.)
    --
    -- The result is DISCARDED and the original `fe`/`pend` are what the
    -- phase below reads: `Runtime.markPersistent` is the identity on
    -- the value and marks the object graph in place, so nothing
    -- downstream — the `InstalledEnv` above, the `InstallRun` it
    -- carries — has to be transported across it, and no verdict can
    -- turn on it.  Term-level `unsafe`, the escape
    -- `Lean.Environment.finalizeImport` uses for this same call; it is
    -- unsafe only in that the marked closure is never freed, and the
    -- process exits right after.
    -- (the deferred block checks are NOT marked: a worker view's slots
    -- are thunks over promises the install resolved, objects the
    -- install's workers may still be counting — the mark would race with
    -- them; there are few block checks, their counts stay atomic)
    markJobs J.fe J.pend J.order
    let tMark ← IO.monoMsNow
    beat err pace s!"persistent mark {secs (tMark - tCheck)}s"
    beat err pace s!"checking: {J.order.size} jobs on {max 1 (min jobs J.order.size)} workers \
      t={secs (tMark - t0)}s"
    return .ok i

/-- **The end of the check phase**, whatever its result: the heartbeat's lines, the summary
with the three phase durations, and the statistics. -/
def checkDone (err : IO.FS.Stream) (pace : Pace) (t0 tParse tCheck jobs : Nat) (J : Jobs)
    (instRepR : IO.Ref (IO PoolRep)) (instLabel : Nat → String) (chkRep : PoolRep)
    (failure : Option (ConLeche.CheckError × Nat)) : IO Unit := do
  let secs (ms : Nat) : String := ConLeche.Cached.msSecs ms
  let now ← IO.monoMsNow
  let workers := max 1 (min jobs J.order.size)
  match failure with
  | some e' =>
    beat err pace s!"check failed at fold position {e'.2} t={secs (now - t0)}s \
      (check {secs (now - tCheck)}s)"
  | none =>
    beat err pace s!"check done: {J.order.size} jobs t={secs (now - t0)}s \
      (check {secs (now - tCheck)}s)"
  beat err pace s!"done: parse {secs (tParse - t0)}s, install {secs (tCheck - tParse)}s, \
    check {secs (now - tCheck)}s, {workers} worker{if workers = 1 then "" else "s"} \
    t={secs (now - t0)}s"
  printStats err (tParse - t0) (tCheck - tParse) (some (now - tCheck)) (← (← instRepR.get))
    instLabel (some chkRep) (jobLabel J)

/-- A record's label in the install's statistics. -/
def recordLabel (ds : Array ConLeche.Declaration) (k : Nat) : String :=
  match ds[k]? with
  | some d => s!"{ConLeche.Cached.declCLabel d} (#{k})"
  | none => s!"record {k}"

/-- **The driver**: the install (`installAndMark`) then the check phase (`checkPool`), and
what comes out is the environment together with the proof that the fold `checkDecls`
(`ConLeche/Cached/Installed.lean`) returns it — the subject of the main
theorem `ConLeche.model_exists` (`ConLeche/MainTheorem.lean`).  The
loops are the fold's two phases with the heartbeat printed between the
steps.  At every job count the install pushes an inductive block as
stored and the block's checked install is a job of the check phase,
beside the definitions' value checks, in fold order (tasks #411, #431:
the fold's run is assembled once every job passed); the fully checked environment they assemble
is an accept of the fold (`ConLeche.Cached.fullyChecked_checkDecls`), so
the success line `checkMainG` prints is printed from an accept of
`checkDecls` and from nothing else.  A rejection carries the fold
position of the declaration it names.  With `--progress`, one line at
the phase boundary, one when the check phase ends, and a summary with
the three phase durations (`tParse` is when the parse finished) and
the worker count.

**The install's workers are joined here**, on every path out, an
exception's included, at the very end (the `finally` below): the process
ends with `IO.Process.exit` (`Main.lean`), and `exit()`'s teardown must
not run under a worker still inside an install.  After a rejection at
more than one worker a stopped worker may be inside the install of a
record past the rejected one, so the verdict line waits for it (the
rejection path need not be fast; maintainer's ruling); after the check
phase every worker has long returned and the join is immediate, which
is why it is here and not at the end of the install phase, where it
would wait for the threads' exit.

**The statistics** (`printStats`, always, flag or not): after the
phases that ran, a few `con-leche: stats:` lines on stderr — the phase
times, each pool's utilisation and tail, the slowest installs and
checks, the peak resident set.  Performance-only: printed after the
verdict is known, from timings the loops accumulate beside their
proofs; stdout and the exit code do not see them. -/
def checkDeclsIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (pace : Pace) (total t0 tParse jobs : Nat)
    (ds : Array ConLeche.Declaration) :
    IO (Except (ConLeche.CheckError × Nat)
      { env : ConLeche.Env // ConLeche.Cached.checkDecls mode ConLeche.natOpPinSets ds = .ok env }) := do
  -- the install's report (performance-only), left here by `installPhase`
  let instRepR ← IO.mkRef (pure default : IO PoolRep)
  -- the join of the install's workers, left here by `installPhase` once
  -- they are started
  let joinWorkers ← IO.mkRef (pure () : BaseIO Unit)
  try
    match ← installAndMark mode err pace total t0 tParse jobs instRepR joinWorkers ds
        (recordLabel ds) with
    | .error e => return .error e
    | .ok i =>
      let (chkRep, res) ← checkPool mode err pace t0 jobs i.jobs
      match res with
      | .error e' =>
        checkDone err pace t0 tParse i.tCheck jobs i.jobs instRepR (recordLabel ds) chkRep (some e')
        return .error e'
      | .ok ⟨hall⟩ =>
        checkDone err pace t0 tParse i.tCheck jobs i.jobs instRepR (recordLabel ds) chkRep none
        -- every deferred block check passed: the serial fold's run
        let e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds.toList :=
          ⟨i.run.p.2.1, i.run.p.2.2, ⟨i.run.p.1, i.run.run hall.2⟩⟩
        let fc : ConLeche.Cached.FullyChecked mode ConLeche.natOpPinSets ds.toList :=
          ⟨e, ConLeche.Cached.groupChecked_of_pendOk mode ConLeche.natOpPinSets hall.1⟩
        return .ok ⟨fc.env, ConLeche.Cached.fullyChecked_checkDecls mode fc⟩
  finally
    (← joinWorkers.get)

/-! ## What an `--olean` run does at the runtime

The check phase of an `--olean` run reads files, through the class
(`checkOleansG`, `ConLeche/Driver/CheckMain.lean`); the rest of what it does is here, as
`IO` actions it hands to `CheckerIO.liftIO`. -/

/-- An `--olean` run's output and its install's report and workers. -/
structure OleanRun where
  err : IO.FS.Stream
  pace : Pace
  total : Nat
  t0 : Nat
  tParse : Nat
  jobs : Nat
  instRepR : IO.Ref (IO PoolRep)
  joinWorkers : IO.Ref (BaseIO Unit)

def OleanRun.new (pace : Pace) (total t0 tParse jobs : Nat) : IO OleanRun := do
  return { err := ← IO.getStderr, pace, total, t0, tParse, jobs,
           instRepR := ← IO.mkRef (pure default), joinWorkers := ← IO.mkRef (pure ()) }

/-- The install, up to the check phase (`installAndMark`). -/
def OleanRun.install (run : OleanRun) (mode : ConLeche.CheckMode) (ds : Array ConLeche.Declaration) :
    IO (Except (ConLeche.CheckError × Nat) (Installed mode ds)) :=
  installAndMark mode run.err run.pace run.total run.t0 run.tParse run.jobs run.instRepR
    run.joinWorkers ds (recordLabel ds)

/-- What every worker reads of the read, marked persistent as the install's result is
(`installAndMark` says why). -/
def markShared {α : Type} (x : α) : IO Unit := do
  let _ ← unsafe Runtime.markPersistent x

/-- The pool's heartbeat lane, and what every worker reads of the read marked (`markShared`). -/
def OleanRun.pool {α : Type} (run : OleanRun) (workers : Nat) (values : α) :
    IO (PoolLive × Nat) := do
  markShared values
  let pl ← PoolLive.new run.pace workers
  return (pl, ← IO.monoNanosNow)

/-- The check phase's end (`checkDone`); `sts` the workers' statistics. -/
def OleanRun.done (run : OleanRun) (ds : Array ConLeche.Declaration) (tCheck tStart workers : Nat)
    (J : Jobs) (sts : List WStats) (failure : Option (ConLeche.CheckError × Nat)) : IO Unit := do
  let tEnd ← IO.monoNanosNow
  let rep : PoolRep := { name := poolName workers, workers, tStart, tEnd, stats := sts.toArray }
  checkDone run.err run.pace run.t0 run.tParse tCheck run.jobs J run.instRepR (recordLabel ds)
    rep failure

/-- The join of the install's workers: on every path out, at the very end
(`checkDeclsIO` says why). -/
def OleanRun.join (run : OleanRun) : IO Unit := do
  (← run.joinWorkers.get)

/-- A job ended on worker `w`: its time, and if it passed its heartbeat (`jobEnd`). -/
def OleanRun.jobEnded (run : OleanRun) (J : Jobs) (pl : PoolLive) (w t ts : Nat) (st : WStats)
    (ok : Bool) : IO WStats := do
  if ok then jobEnd run.err run.pace run.t0 J pl w t ts st
  else
    let te ← IO.monoNanosNow
    return st.add t ts te

end ConLeche.Driver
