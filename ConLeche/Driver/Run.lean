module

public import ConLeche.Driver.ParInstall
public import ConLeche.Driver.CheckPool

/-!
# The driver: `checkDeclsIO` and the phase sequencing

Part of the proof-carrying driver (`ConLeche/Driver/*`; the CLI —
argument parsing, I/O, exit codes — is `Cli.lean`, `Main.lean`).

`checkDeclsIO` is **the driver**: the install (`installPhase`,
`Driver/ParInstall.lean`: the commit thread with `n` workers at
`--jobs=<n>`, alone at `--jobs=1`) then the check phase — `checkLoop` on
one dedicated worker thread at `--jobs=1`, `checkPool` otherwise
(`Driver/CheckPool.lean`) — and what comes out is
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

/-- **The driver**: the install (`installPhase`, with `jobs` workers
beside the commit thread at `--jobs=<n>`, none at `--jobs=1`) then the
check phase — `checkLoop` on one dedicated worker thread at `--jobs=1`,
`checkPool` otherwise — and what comes out is the environment together
with the proof that the fold `checkDecls`
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
def checkDeclsIO (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride total t0 tParse jobs : Nat)
    (noMark : Bool) (ds : Array ConLeche.Declaration) :
    IO (Except (ConLeche.CheckError × Nat)
      { env : ConLeche.Env // ConLeche.Cached.checkDecls mode ConLeche.natOpPinSets ds = .ok env }) := do
  let heartbeat (line : String) : IO Unit := do
    if stride > 0 then
      err.putStr s!"con-leche: {line}\n"
      err.flush
  let secs (ms : Nat) : String := ConLeche.Cached.msSecs ms
  let instLabel (k : Nat) : String := match ds[k]? with
    | some d => s!"{ConLeche.Cached.declCLabel d} (#{k})"
    | none => s!"record {k}"
  -- the install's report (performance-only), left here by `installPhase`
  let instRepR ← IO.mkRef (pure default : IO PoolRep)
  -- the join of the install's workers, left here by `installPhase` once
  -- they are started
  let joinWorkers ← IO.mkRef (pure () : BaseIO Unit)
  try
    -- the install's worker count: none at `--jobs=1`, where the commit
    -- thread installs every record itself
    let installed ← installPhase mode err stride total t0 (if jobs ≤ 1 then 0 else jobs)
      noMark instRepR joinWorkers ds
    let instRep : IO PoolRep := do (← instRepR.get)
    match installed with
    | .error e =>
      let now ← IO.monoMsNow
      heartbeat s!"install failed at {e.2}/{total} t={secs (now - t0)}s \
        (install {secs (now - tParse)}s)"
      heartbeat s!"done: parse {secs (tParse - t0)}s, install {secs (now - tParse)}s, \
        check not reached t={secs (now - t0)}s"
      printStats err (tParse - t0) (now - tParse) none (← instRep) instLabel none (fun _ => "")
      return .error e
    | .ok ⟨(n, fe, pend), D, r⟩ =>
      -- the check phase's jobs: the recorded value checks and the deferred
      -- block checks, in fold order
      let J : Jobs := ⟨fe, pend, D, ConLeche.Cached.jobOrder pend D⟩
      let tCheck ← IO.monoMsNow
      heartbeat s!"install done: {total}/{total} declarations installed, \
        {J.order.size} checks pending ({D.size} of them inductive blocks) t={secs (tCheck - t0)}s \
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
      -- process exits right after.  `--no-mark-persistent` turns it off,
      -- which is how the A/B above is measured on the shipped binary.
      -- (the deferred block checks are NOT marked: a worker view's slots
      -- are thunks over promises the install resolved, objects the
      -- install's workers may still be counting — the mark would race with
      -- them; there are few block checks, their counts stay atomic)
      if !noMark then
        let _ ← unsafe Runtime.markPersistent fe
        let _ ← unsafe Runtime.markPersistent pend
        let _ ← unsafe Runtime.markPersistent J.order
      let tMark ← IO.monoMsNow
      heartbeat s!"persistent mark {secs (tMark - tCheck)}s"
      let workers := max 1 (min jobs J.order.size)
      let tC0 ← IO.monoNanosNow
      let (chkRep, res) ← if jobs ≤ 1 then
          -- ONE worker, and no pool: no shared claim counter, the same
          -- table and walk — only the thread is new.  A worker that fails
          -- as an `IO` action (not a check failing) is an internal error,
          -- exit 3, never a verdict.
          let (st, r) ← match ← IO.wait (← IO.asTask (prio := .dedicated) do
              let (st, tab) ← checkLoop mode err stride t0 J 0 (Array.replicate J.order.size none) {}
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
      let stats : IO Unit :=
        printStats err (tParse - t0) (tCheck - tParse) (some (now - tCheck)) (← instRep)
          instLabel (some chkRep) (jobLabel J)
      let summary := s!"done: parse {secs (tParse - t0)}s, install {secs (tCheck - tParse)}s, \
        check {secs (now - tCheck)}s, {workers} worker{if workers = 1 then "" else "s"} \
        t={secs (now - t0)}s"
      match res with
      | .error e' =>
        heartbeat s!"check failed at fold position {e'.2} t={secs (now - t0)}s \
          (check {secs (now - tCheck)}s)"
        heartbeat summary
        stats
        return .error e'
      | .ok ⟨hall⟩ =>
        heartbeat s!"check done: {J.order.size}/{J.order.size} t={secs (now - t0)}s \
          (check {secs (now - tCheck)}s)"
        heartbeat summary
        stats
        -- every deferred block check passed: the serial fold's run
        let e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds.toList :=
          ⟨fe, pend, ⟨n, r hall.2⟩⟩
        let fc : ConLeche.Cached.FullyChecked mode ConLeche.natOpPinSets ds.toList :=
          ⟨e, ConLeche.Cached.groupChecked_of_pendOk mode ConLeche.natOpPinSets hall.1⟩
        return .ok ⟨fc.env, ConLeche.Cached.fullyChecked_checkDecls mode fc⟩
  finally
    (← joinWorkers.get)

end ConLeche.Driver
