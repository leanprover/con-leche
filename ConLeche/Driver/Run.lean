module

public import ConLeche.Driver.CheckPool
public import ConLeche.Verify.Cached.StreamIndex

/-!
# The driver: `checkDeclsIO`

Part of the proof-carrying driver (`ConLeche/Driver/*`; the CLI -- argument parsing, I/O, exit codes
-- is `Cli.lean`, `Main.lean`).

`checkDeclsIO` is **the driver's check phase**: `checkLoop` on one dedicated worker thread at
`--jobs=1`, `checkPool` otherwise (`Driver/CheckPool.lean`), and what comes out is the proof that the
fold `checkDecls` (`ConLeche/Cached/Decls.lean`) accepts the records -- the subject of the main theorem
`ConLeche.model_exists` (`ConLeche/MainTheorem.lean`).  The driver's sequencing `checkMainG`
(`ConLeche/Driver/CheckMain.lean`, generic in the IO class) runs it through `CheckerIO.liftIO` and
turns the result into the verdict line and the exit code `Main.lean`'s `main` returns.
-/

@[expose] public section

open ConLeche

namespace ConLeche.Driver

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

/-- **The check phase**: every record's job at the frozen index -- `checkLoop` on one dedicated worker
thread at `--jobs=1`, `checkPool` otherwise -- and what comes out is the proof that the fold
`checkDecls` accepts the records (`ConLeche.Cached.checkDecls_of_jobs`), so the success line
`checkMainG` prints is printed from an accept of `checkDecls` and from nothing else.  A rejection
carries the fold position of the declaration it names.  With `--progress`, one line per `stride`
completed checks, one when the phase ends, and a summary with the two phase durations (`tParse` is
when the parse finished, the index included; `tIndex` is when the index build started) and the worker
count.

**The statistics** (`printStats`, always, flag or not): after the check phase, a few
`con-leche: stats:` lines on stderr -- the phase times, the pool's utilisation and tail, the slowest
checks, the peak resident set.  Performance-only: printed after the verdict is known, from timings the
loops accumulate beside their proofs; stdout and the exit code do not see them. -/
def checkDeclsIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 tIndex tParse jobs : Nat)
    {ds : Array ConLeche.Declaration} (J : Jobs ds) :
    IO (Except (ConLeche.CheckError × Nat)
      (PLift (∃ env, ConLeche.Cached.checkDecls mode ConLeche.natOpPinSets ds = .ok env))) := do
  let heartbeat (line : String) : IO Unit := do
    if stride > 0 then
      err.putStr s!"con-leche: {line}\n"
      err.flush
  let secs (ms : Nat) : String := ConLeche.Cached.msSecs ms
  let workers := max 1 (min jobs ds.size)
  let tC0 ← IO.monoNanosNow
  let (chkRep, res) ← if jobs ≤ 1 then
      -- ONE worker, and no pool: no shared claim counter, the same table and walk -- only the thread
      -- is new.  A worker that fails as an `IO` action (not a check failing) is an internal error,
      -- exit 3, never a verdict.
      let (st, r) ← match ← IO.wait (← IO.asTask (prio := .dedicated) do
          let (st, tab) ← checkLoop mode err stride t0 J 0 (Array.replicate ds.size none) {}
          pure (st, collect mode J tab)) with
        | .ok r => pure r
        | .error ioe =>
          pure ({}, .error (.internal s!"check phase: the worker failed: {ioe}", 0))
      let tC1 ← IO.monoNanosNow
      let rep : PoolRep := { name := "check (one worker)", workers := 1, tStart := tC0,
                             tEnd := tC1, stats := #[st] }
      pure (rep, r)
    else
      checkPool mode err stride t0 jobs J
  let now ← IO.monoMsNow
  let summary := s!"done: parse {secs (tParse - t0)}s, check {secs (now - tParse)}s, \
    {workers} worker{if workers = 1 then "" else "s"} t={secs (now - t0)}s"
  let stats : IO Unit :=
    printStats err (tParse - t0) (tParse - tIndex) (now - tParse) chkRep (jobLabel ds)
  match res with
  | .error e =>
    heartbeat s!"check failed at fold position {e.2} t={secs (now - t0)}s \
      (check {secs (now - tParse)}s)"
    heartbeat summary
    stats
    return .error e
  | .ok ⟨hall⟩ =>
    heartbeat s!"check done: {ds.size}/{ds.size} t={secs (now - t0)}s \
      (check {secs (now - tParse)}s)"
    heartbeat summary
    stats
    return .ok ⟨⟨_, ConLeche.Cached.checkDecls_of_jobs (J.hI ▸ hall)⟩⟩

end ConLeche.Driver
