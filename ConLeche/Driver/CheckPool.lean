module

public import ConLeche.Verify.Cached.Defer
public import Std.Sync.Mutex
public import ConLeche.Driver.Stats
public import ConLeche.Frontend.CheckerIO
public import ConLeche.Frontend.Pace

/-!
# Phase B: the check pool

Phase B's pool: `checkPool`, with its heartbeat, over the worker map
(`CheckerIO.parMapWorkers`).
Part of the proof-carrying driver (`ConLeche/Driver/*`; the CLI is
`Cli.lean`).

The check phase's jobs are the recorded value checks and the deferred
checks of the inductive blocks (tasks #411, #431: phase A pushes a block
as stored, `ConLeche/Verify/Cached/Defer.lean`), in fold order
(`ConLeche.Cached.jobOrder`).  They are independent by construction —
a value check reads the installed index at its own prefix view, its own
record, and a fresh memo state; a block check runs the block's checked
install at a view of its own (the install's worker view)
from a fresh memo state
— so phase B is handed to `n` long-lived worker tasks
(`IO.asTask` on dedicated threads: exactly `n` threads whatever the
runtime's own pool size).  The work is millions of mostly tiny checks
with a skewed tail (single bodies of an hour exist) and the heavy ones
sit CLOSE TOGETHER in the stream, so a worker claims ONE job per
atomic claim off one shared counter: a cluster of heavy declarations is
spread over the whole pool instead of serialising inside one claimed
range, and the only item that can strand the pool is the single largest
check.  The claim costs one `modifyGet` on an `IO.Ref` per job,
which is below the third decimal of a run.  A job's result (`JRes`) is
its fact (the record's `PendOk`, the block's
`BlockCheck.Ok`) or its tagged error (`ConLeche.Cached.runJob`).  The
worker map gives the results in job order, and the pool walks them
(`ConLeche.Cached.collectJobs`): the first
failing job in FOLD order is the verdict — and the declaration the
rejection names — whatever the workers'
timing.  **Determinism on a failure**: a worker
that fails job `f` lowers the shared `limit` to `f`, and no worker
starts a job at or above the limit — every job below `f` was
claimed before `f` was (the counter is monotone) and is finished by
the worker that claimed it, so the table is complete below the first
failure; jobs above it may be missing, and the walk never reaches
them.  A worker cannot be cancelled mid-check (a check is a pure
computation), so the pool drains.

Each worker thread reserves 1 GiB of address space — see
`jobsCount` (`Cli.lean`); the default count is the hardware thread
count.

Nothing in the pool touches the driver's type: what a worker returns
carries its own evidence, and `collectJobs` assembles from the table
alone every record's check and every block check, which the driver
turns into the serial fold's run and the fully checked environment.
The transfer theorem is untouched.

The runtime marks everything reachable from a task's closure — the
installed index and the records — for multi-threaded reference
counting once, on the first spawn (an object already marked is not
walked again); every reference-count operation on those objects is
atomic from then on, which is the pool's instruction overhead.  A plain run pays, on top of that, one atomic
claim per job and two clock reads (the statistics, `WStats`, kept
in the worker's own loop and merged at the end); the heartbeat lane (`--progress`) pays one lock of a
mutex per completed job, for an exact completed-count.  The bump
and its line are ONE critical section: with the count taken
atomically but printed after, a worker descheduled between the two let
a later count's line overtake its own (`check 1, 3, 2` — measured
under load, the arena's `counting up` check).  Under the lock the
lines leave in count order, so the lane's lines count up by one
whatever the scheduling.
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche

/-- The jobs of a check phase (task #411): the installed index, the
recorded value checks, the deferred block checks, and the jobs in fold
order (`jobOrder`). -/
structure Jobs where
  fe : ConLeche.FEnv
  pend : Array ConLeche.Cached.PendingCheck
  D : Array ConLeche.Cached.BlockCheck
  order : Array ConLeche.Cached.Job

/-- A job's result, at the shipped pin list. -/
abbrev JRes (mode : ConLeche.CheckMode) (J : Jobs) : Type :=
  ConLeche.Cached.JobResult mode ConLeche.natOpPinSets J.fe J.pend J.D

/-- What the check phase establishes. -/
abbrev JAll (mode : ConLeche.CheckMode) (J : Jobs) : Prop :=
  ConLeche.Cached.AllOk mode ConLeche.natOpPinSets J.fe J.pend J.D

/-- Job `t`'s label for the statistics: kind, name and fold position. -/
def jobLabel (J : Jobs) (t : Nat) : String :=
  match J.order[t]? with
  | some (false, k) => match J.pend[k]? with
    | some p => s!"{p.vg.kind.word} {p.vg.cv.name} (#{p.pos})"
    | none => s!"check {t}"
  | some (true, k) => match J.D[k]? with
    | some b => s!"inductive {b.name} (#{b.pos})"
    | none => s!"check {t}"
  | none => s!"check {t}"

/-- The check phase's heartbeat: when `pace` says a line is due, with `n`
checks completed so far, job `t` the one just completed, one line,
naming it if every check gets one (`Pace.trace`).  The counter is the number of COMPLETED checks, so in the
pool it is monotone whichever worker finished, and the line is printed
after the check rather than before it: a check that is running is not
on any line, the gap between two lines is where it sits.  In the pool
(`live`), the line ends with the number of busy workers and the oldest
check in flight with its age (`Live.report`). -/
def checkHeartbeat (err : IO.FS.Stream) (pace : Pace) (t0 : Nat) (J : Jobs)
    (last : IO.Ref Nat) (live : Option Live) (n t : Nat) : IO Unit := do
  if ← pace.due last n J.order.size then
    let now ← IO.monoMsNow
    let extra ← match live with
      | some lv => lv.report (jobLabel J) (if pace.trace then 0 else oldestAge)
      | none => pure ""
    let l := if !pace.trace then "" else match J.order[t]? with
      | some (false, k) => match J.pend[k]? with
        | some p => s!" {p.vg.kind.word} {p.vg.cv.name}"
        | none => s!" check {t}"
      | some (true, k) => match J.D[k]? with
        | some b => s!" inductive {b.name}"
        | none => s!" check {t}"
      | none => s!" check {t}"
    err.putStr s!"con-leche: check {n} ({n * 100 / max 1 J.order.size}%){l} \
      t={ConLeche.Cached.msSecs (now - t0)}s{extra}\n"
    err.flush

/-- Job `t`, run: the job of slot `t` of the order. -/
def runAt (mode : ConLeche.CheckMode) (J : Jobs) (t : Nat) : JRes mode J :=
  match J.order[t]? with
  | some j => ConLeche.Cached.runJob mode ConLeche.natOpPinSets J.fe J.pend J.D j
  | none => .error (.internal s!"check phase: no job {t}", 0)

/-- The table walked into the check phase's facts. -/
def collect (mode : ConLeche.CheckMode) (J : Jobs) (tab : Array (Option (JRes mode J))) :
    Except (ConLeche.CheckError × Nat) (PLift (JAll mode J)) :=
  ConLeche.Cached.collectJobs mode ConLeche.natOpPinSets J.fe J.pend J.D tab 0 0 0
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))

/-! ### The pool: phase B on `--jobs=<n>` threads -/

/-- What a pool shares, for its heartbeat: the completed-count and the workers' current
jobs. -/
structure PoolLive where
  done : Std.Mutex Nat
  live : Option Live
  /-- when the last line was -/
  last : IO.Ref Nat

/-- The heartbeat's lane, for `workers` workers. -/
def PoolLive.new (pace : Pace) (workers : Nat) : IO PoolLive := do
  let done ← Std.Mutex.new 0
  let live ← if workers > 1 then some <$> Live.new (if pace.on then workers else 0)
    else pure none
  return ⟨done, live, ← Pace.clock⟩

/-- A job starts on worker `w`: the clock, and on the heartbeat lane the job it is on. -/
def jobBegin (pl : PoolLive) (pace : Pace) (w t : Nat) : IO Nat := do
  let ts ← IO.monoNanosNow
  if pace.on then
    if let some lv := pl.live then lv.begin w t ts
  return ts

/-- A job ended well on worker `w`: on the heartbeat lane the completed-count is bumped
and its line printed under one lock, so the lines count up.  Its time, into the worker's
statistics. -/
def jobEnd (err : IO.FS.Stream) (pace : Pace) (t0 : Nat) (J : Jobs) (pl : PoolLive) (w t ts : Nat)
    (st : WStats) : IO WStats := do
  let te ← IO.monoNanosNow
  if pace.on then
    if let some lv := pl.live then lv.idle w
    pl.done.atomically do
      let n ← modifyGet fun d => (d + 1, d + 1)
      checkHeartbeat err pace t0 J pl.last pl.live n t
  return st.add t ts te

/-- One job of the pool, on worker `s.1`: run and timed (the job is forced before the
clock, by the branch on its result). -/
def checkStep (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (pace : Pace) (t0 : Nat) (J : Jobs)
    (pl : PoolLive) (s : Nat × WStats) (t : Nat) : IO ((Nat × WStats) × JRes mode J) := do
  let ts ← jobBegin pl pace s.1 t
  let r := runAt mode J t
  if r matches .error _ then
    let te ← IO.monoNanosNow
    return ((s.1, s.2.add t ts te), r)
  else
    let st ← jobEnd err pace t0 J pl s.1 t ts s.2
    return ((s.1, st), r)

/-- A pool's name in the statistics. -/
def poolName (workers : Nat) : String :=
  if workers ≤ 1 then "check (one worker)" else "check pool"

/-- **Phase B on `jobs` worker threads** (`parMapWorkersIO`): one job per atomic claim, a
worker that fails a job stops every job above it, and the result is the walk over the
jobs in order, which stops at the first failure in FOLD order whatever the workers'
timing.  It runs on a dedicated thread at every count, one included: the check's memo
state comes out of the running thread's own heap, and the main thread's heap after the
install is two gigabytes of live environment with the parse's and the install's freed
temporaries scattered through it, which costs a factor of two in wall time at Mathlib
scale for the same instructions.  A worker that fails as an `IO` action (not a check
failing) is an internal error, exit 3, never a verdict.  Beside the result, the pool's
timing report (`PoolRep`, performance-only). -/
def checkPool (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (pace : Pace) (t0 jobs : Nat) (J : Jobs) :
    IO (PoolRep × Except (ConLeche.CheckError × Nat) (PLift (JAll mode J))) := do
  let m := J.order.size
  let workers := max 1 (min jobs m)
  let pl ← PoolLive.new pace workers
  let tStart ← IO.monoNanosNow
  try
    let (ss, res) ← parMapWorkersIO jobs (fun w => (w, ({} : WStats)))
      (checkStep mode err pace t0 J pl) (List.range m)
    let tEnd ← IO.monoNanosNow
    let rep : PoolRep := { name := poolName workers, workers, tStart, tEnd,
                           stats := (ss.map (·.2)).toArray }
    match res with
    | .error e => return (rep, .error e)
    | .ok rs => return (rep, collect mode J (rs.toArray.map fun r => some (.ok r)))
  catch ioe =>
    let tEnd ← IO.monoNanosNow
    let rep : PoolRep := { name := poolName workers, workers, tStart, tEnd, stats := #[] }
    return (rep, .error (.internal s!"check phase: a worker failed: {ioe}", 0))

end ConLeche.Driver
