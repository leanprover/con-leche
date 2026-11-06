module

public import ConLeche.Driver.CheckPool
public import ConLeche.Verify.Cached.StreamIndex

/-!
# The driver: `checkDeclsIO`

Part of the proof-carrying driver (`ConLeche/Driver/*`; the CLI -- argument parsing, I/O, exit codes
-- is `Cli.lean`, `Main.lean`).

`checkDeclsIO` is **the driver's check phase**: `checkPool` (`Driver/CheckPool.lean`) on
`--jobs=<n>` worker threads, and what comes out is the proof that the fold `checkDecls`
(`ConLeche/Cached/Decls.lean`) accepts the records -- the subject of the main theorem
`ConLeche.model_exists` (`ConLeche/MainTheorem.lean`).  The driver's sequencing `checkMainG`
(`ConLeche/Driver/CheckMain.lean`, generic in the IO class) runs it through `CheckerIO.liftIO` and
turns the result into the verdict line and the exit code `Main.lean`'s `main` returns.
-/

@[expose] public section

open ConLeche

namespace ConLeche.Driver

/-- A heartbeat line (`--progress`). -/
def beat (err : IO.FS.Stream) (pace : Pace) (line : String) : IO Unit := do
  if pace.on then
    err.putStr s!"con-leche: {line}\n"
    err.flush

/-- The first line of a run: what it is reading. -/
def readStarts (pace : Pace) (label : String) : IO Unit := do
  beat (← IO.getStderr) pace s!"reading {label}"

/-- The end-of-run statistics (performance-only): the phase times, the check's report (`PoolRep.line`,
the slowest five), the peak resident set.  Every line starts `con-leche: stats:`. -/
def printStats (err : IO.FS.Stream) (parseMs indexMs checkMs : Nat)
    (chk : PoolRep) (chkLabel : Nat → String) : IO Unit := do
  let line (l : String) : IO Unit := err.putStr s!"con-leche: stats: {l}\n"
  let secs := ConLeche.Cached.msSecs
  line s!"phases: parse {secs parseMs}s (index {secs indexMs}s), check {secs checkMs}s"
  line chk.line
  line (chk.topLine "checks" chkLabel)
  if let some r ← peakRss then line s!"peak RSS {r}"
  err.flush

/-- The check phase's first line: how many jobs, on how many workers. -/
def checkStarts (err : IO.FS.Stream) (pace : Pace) (t0 n jobs : Nat) : IO Unit := do
  let now ← IO.monoMsNow
  beat err pace s!"checking: {n} declarations on {max 1 (min jobs n)} workers \
    t={ConLeche.Cached.msSecs (now - t0)}s"

/-- **The end of the check phase**, whatever its result: the heartbeat's lines, the summary with
the two phase durations (`tParse` is when the read finished, the index included; `tIndex` is when
the index build started), and the statistics. -/
def checkDone (err : IO.FS.Stream) (pace : Pace) (t0 tIndex tParse jobs : Nat)
    (ds : Array ConLeche.Declaration) (chkRep : PoolRep)
    (failure : Option (ConLeche.CheckError × Nat)) : IO Unit := do
  let secs (ms : Nat) : String := ConLeche.Cached.msSecs ms
  let now ← IO.monoMsNow
  let workers := max 1 (min jobs ds.size)
  match failure with
  | some e =>
    beat err pace s!"check failed at fold position {e.2} t={secs (now - t0)}s \
      (check {secs (now - tParse)}s)"
  | none =>
    beat err pace s!"check done: {ds.size} declarations t={secs (now - t0)}s \
      (check {secs (now - tParse)}s)"
  beat err pace s!"done: parse {secs (tParse - t0)}s, check {secs (now - tParse)}s, \
    {workers} worker{if workers = 1 then "" else "s"} t={secs (now - t0)}s"
  printStats err (tParse - t0) (tParse - tIndex) (now - tParse) chkRep (jobLabel ds)

/-- **The check phase**: every record's job at the frozen index, on `checkPool`, and what comes out
is the proof that the fold `checkDecls` accepts the records (`ConLeche.Cached.checkDecls_of_jobs`),
so the success line `checkMainG` prints is printed from an accept of `checkDecls` and from nothing
else.  A rejection carries the fold position of the declaration it names.  With `--progress`, a line
when the phase starts, the pool's lines, one when it ends, and a summary with the two phase durations
and the worker count.

**The statistics** (`printStats`, always, flag or not): after the check phase, a few
`con-leche: stats:` lines on stderr -- the phase times, the pool's utilisation and tail, the slowest
checks, the peak resident set.  Performance-only: printed after the verdict is known, from timings the
workers accumulate beside their proofs; stdout and the exit code do not see them. -/
def checkDeclsIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (pace : Pace) (t0 tIndex tParse jobs : Nat)
    {ds : Array ConLeche.Declaration} (J : Jobs ds) :
    IO (Except (ConLeche.CheckError × Nat)
      (PLift (∃ env, ConLeche.Cached.checkDecls mode ConLeche.natOpPinSets ds = .ok env))) := do
  checkStarts err pace t0 ds.size jobs
  let (chkRep, res) ← checkPool mode err pace t0 jobs J
  match res with
  | .error e =>
    checkDone err pace t0 tIndex tParse jobs ds chkRep (some e)
    return .error e
  | .ok ⟨hall⟩ =>
    checkDone err pace t0 tIndex tParse jobs ds chkRep none
    return .ok ⟨⟨_, ConLeche.Cached.checkDecls_of_jobs (J.hI ▸ hall)⟩⟩

/-! ## What an `--olean` run does at the runtime

The check phase of an `--olean` run reads files, through the class (`checkOleansG`,
`ConLeche/Driver/CheckMain.lean`); the rest of what it does is here, as `IO` actions it hands to
`CheckerIO.liftIO`. -/

/-- An `--olean` run's output and clocks. -/
structure OleanRun where
  err : IO.FS.Stream
  pace : Pace
  t0 : Nat
  tIndex : Nat
  tParse : Nat
  jobs : Nat

def OleanRun.new (pace : Pace) (t0 tIndex tParse jobs : Nat) : IO OleanRun := do
  return { err := ← IO.getStderr, pace, t0, tIndex, tParse, jobs }

/-- The check phase's first line, the pool's heartbeat lane, and what every worker reads of the read
marked (`markShared`). -/
def OleanRun.pool {α : Type} (run : OleanRun) (n workers : Nat) (values : α) :
    IO (PoolLive × Nat) := do
  markShared values
  checkStarts run.err run.pace run.t0 n run.jobs
  let pl ← PoolLive.new run.pace workers
  return (pl, ← IO.monoNanosNow)

/-- The check phase's end (`checkDone`); `sts` the workers' statistics. -/
def OleanRun.done (run : OleanRun) (ds : Array ConLeche.Declaration) (tStart workers : Nat)
    (sts : List WStats) (failure : Option (ConLeche.CheckError × Nat)) : IO Unit := do
  let tEnd ← IO.monoNanosNow
  let rep : PoolRep := { name := poolName workers, workers, tStart, tEnd, stats := sts.toArray }
  checkDone run.err run.pace run.t0 run.tIndex run.tParse run.jobs ds rep failure

end ConLeche.Driver
