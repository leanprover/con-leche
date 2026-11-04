module

public import ConLeche.Verify.Cached.Defer
public import Std.Sync.Mutex
public import ConLeche.Driver.Stats

/-!
# Phase B: the check pool

Phase B's loops: `checkLoop`, the sequential loop at `--jobs=1`, and
`checkPool`, the pool at `--jobs=<n>`, with the heartbeat they share.
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
which is below the third decimal of a run.  Each worker keeps
its results in its own array (job index, `JRes`), which
is what a job IS: its fact (the record's `PendOk`, the block's
`BlockCheck.Ok`) or its tagged error (`ConLeche.Cached.runJob`).  The
pool merges the arrays by index into one table and walks it in job
order (`ConLeche.Cached.collectJobs`): the walk stops at the first
failing job in FOLD order, so the verdict — and the declaration the
rejection names — is the sequential walk's whatever the workers'
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
atomic from then on, which is the pool's instruction overhead over
the sequential loop.  A plain run pays, on top of that, one atomic
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

/-- The check phase's heartbeat: on the `stride`-th completed check
(`n` completed so far, job `t` the one just completed), one line
naming it.  The counter is the number of COMPLETED checks, so in the
pool it is monotone whichever worker finished, and the line is printed
after the check rather than before it: a check that is running is not
on any line, the gap between two lines is where it sits.  In the pool
(`live`), the line ends with the number of busy workers and the oldest
check in flight with its age (`Live.report`). -/
def checkHeartbeat (err : IO.FS.Stream) (stride t0 : Nat) (J : Jobs)
    (live : Option Live) (n t : Nat) : IO Unit := do
  if stride > 0 && n % stride == 0 then
    let now ← IO.monoMsNow
    let extra ← match live with
      | some lv => lv.report (jobLabel J)
      | none => pure ""
    let l := match J.order[t]? with
      | some (false, k) => match J.pend[k]? with
        | some p => s!"{p.vg.kind.word} {p.vg.cv.name}"
        | none => s!"check {t}"
      | some (true, k) => match J.D[k]? with
        | some b => s!"inductive {b.name}"
        | none => s!"check {t}"
      | none => s!"check {t}"
    err.putStr s!"con-leche: check {n}/{J.order.size} {l} \
      t={ConLeche.Cached.msSecs (now - t0)}s{extra}\n"
    err.flush

/-- Job `t`, run: the job of slot `t` of the order. -/
def runAt (mode : ConLeche.CheckMode) (J : Jobs) (t : Nat) : JRes mode J :=
  match J.order[t]? with
  | some j => ConLeche.Cached.runJob mode ConLeche.natOpPinSets J.fe J.pend J.D j
  | none => .error (.internal s!"check phase: no job {t}", 0)

/-- **Phase B in one thread — the check pass at `--jobs=1`.**  The jobs
in fold order, each from a fresh memo state (`ConLeche.Cached.runJob`),
each result in its slot of the table, until the first failure; the
table is then walked (`ConLeche.Cached.collectJobs`) into every record
checked and every block check passed.  Nothing is shared with any other
thread and no counter is claimed: this loop is the sequential baseline
the pool below is measured against.  It runs on ONE DEDICATED WORKER
THREAD all the same: the loop's cost is dominated by the per-check memo
state, that state comes out of the running thread's own mimalloc heap,
and the main thread's heap after the install phase is two gigabytes of
live environment with the parse's and the install's freed temporaries
scattered through it — allocating phase B out of that scatter costs a
factor of two in wall time at Mathlib scale for the same instructions.
With `--progress`, one line per `stride` completed checks.  `st` is
the timing (`WStats`, performance-only), returned beside the result. -/
def checkLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat) (J : Jobs) :
    (t : Nat) → Array (Option (JRes mode J)) → WStats →
      IO (WStats × Array (Option (JRes mode J)))
  | t, tab, st =>
    if t < J.order.size then do
      let ts ← IO.monoNanosNow
      let r := runAt mode J t
      let bad := r matches .error _
      -- (read in a branch on `bad`, so the check is forced before the clock)
      let te ← if bad then IO.monoNanosNow else IO.monoNanosNow
      let tab := tab.set! t (some r)
      if bad then return (st.add t ts te, tab)
      checkHeartbeat err stride t0 J none (t + 1) t
      checkLoop mode err stride t0 J (t + 1) tab (st.add t ts te)
    else
      return (st, tab)
  termination_by t => J.order.size - t

/-- The table walked into the check phase's facts. -/
def collect (mode : ConLeche.CheckMode) (J : Jobs) (tab : Array (Option (JRes mode J))) :
    Except (ConLeche.CheckError × Nat) (PLift (JAll mode J)) :=
  ConLeche.Cached.collectJobs mode ConLeche.natOpPinSets J.fe J.pend J.D tab 0 0 0
    (fun _ h => absurd h (Nat.not_lt_zero _)) (fun _ h => absurd h (Nat.not_lt_zero _))

/-! ### The pool: phase B on `--jobs=<n>` threads -/

/-- One claimed job of one worker: below the shared `limit` it is run
and its result appended; a failure lowers the limit to its index; on
the heartbeat lane the completed-count is bumped and its line printed
under one lock, so the lines count up.  A job at or above the limit is
skipped — it is above a known failure and the walk will never ask for
it.  The job is timed into the worker's own `st`; on the heartbeat lane
worker `w` also publishes the job it is on (`live`). -/
def checkOne (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat) (J : Jobs)
    (limit : IO.Ref Nat) (done : Std.Mutex Nat) (live : Live) (w : Nat) (t : Nat)
    (acc : Array (Nat × JRes mode J)) (st : WStats) :
    IO (Array (Nat × JRes mode J) × WStats) := do
  if t < (← limit.get) then
    let ts ← IO.monoNanosNow
    if stride > 0 then live.begin w t ts
    let r := runAt mode J t
    let bad := r matches .error _
    -- (read in a branch on `bad`, so the check is forced before the clock)
    let te ← if bad then IO.monoNanosNow else IO.monoNanosNow
    if bad then
      limit.modify (min · t)
    let acc := acc.push (t, r)
    if stride > 0 then
      live.idle w
      done.atomically do
        let n ← modifyGet fun d => (d + 1, d + 1)
        checkHeartbeat err stride t0 J (some live) n t
    return (acc, st.add t ts te)
  else return (acc, st)

/-- One worker: claim ONE job off the shared counter, run it, repeat
until the counter is past the jobs.  The fuel is exact: every claim
advances the counter by exactly one, so `order.size + 1` claims see it
past the end whatever the other workers do. -/
def checkWorker (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat) (J : Jobs)
    (next limit : IO.Ref Nat) (done : Std.Mutex Nat) (live : Live) (w : Nat) :
    (fuel : Nat) → Array (Nat × JRes mode J) → WStats →
      IO (Array (Nat × JRes mode J) × WStats)
  | 0, acc, st => pure (acc, st)
  | fuel + 1, acc, st => do
    let t ← next.modifyGet fun a => (a, a + 1)
    if t < J.order.size then
      let (acc, st) ← checkOne mode err stride t0 J limit done live w t acc st
      checkWorker mode err stride t0 J next limit done live w fuel acc st
    else pure (acc, st)

/-- The workers' arrays merged by job index into one table. -/
def mergeResults {mode : ConLeche.CheckMode} {J : Jobs}
    (tab : Array (Option (JRes mode J))) :
    List (Array (Nat × JRes mode J)) → Array (Option (JRes mode J))
  | [] => tab
  | rs :: rest => mergeResults (rs.foldl (fun tab (k, r) => tab.set! k (some r)) tab) rest

/-- **Phase B on a pool of `jobs` worker threads.**  Spawns
`min jobs order.size` workers, waits for all of them, merges their
results and walks the table in job order.  A worker that failed as an
`IO` action (not a check failing — the pool's own machinery) is an
internal error, exit 3, never a verdict on the input.  Beside the
result, the pool's timing report (`PoolRep`, performance-only). -/
def checkPool (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 jobs : Nat) (J : Jobs) :
    IO (PoolRep × Except (ConLeche.CheckError × Nat) (PLift (JAll mode J))) := do
  let m := J.order.size
  let workers := max 1 (min jobs m)
  let next ← IO.mkRef 0
  let limit ← IO.mkRef m
  let done ← Std.Mutex.new 0
  let live ← Live.new (if stride > 0 then workers else 0)
  let tStart ← IO.monoNanosNow
  let mut tasks : Array (Task (Except IO.Error (Array (Nat × JRes mode J) × WStats))) := #[]
  for w in [0:workers] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated)
      (checkWorker mode err stride t0 J next limit done live w (m + 1) #[] {}))
  let mut results : List (Array (Nat × JRes mode J)) := []
  let mut stats : Array WStats := #[]
  let mut failure : Option IO.Error := none
  for t in tasks do
    match ← IO.wait t with
    | .ok (rs, st) =>
      results := rs :: results
      stats := stats.push st
    | .error ioe => failure := some ioe
  let tEnd ← IO.monoNanosNow
  let rep : PoolRep := { name := "check pool", workers, tStart, tEnd, stats }
  if let some ioe := failure then
    return (rep, .error (.internal s!"check phase: a worker failed: {ioe}", 0))
  let tab := mergeResults (Array.replicate m none) results
  return (rep, collect mode J tab)

end ConLeche.Driver
