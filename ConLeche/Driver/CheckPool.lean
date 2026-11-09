module

public import ConLeche.Cached.StreamIndex
public import Std.Sync.Mutex
public import ConLeche.Driver.Stats
public import ConLeche.Frontend.CheckerIO
public import ConLeche.Frontend.Pace

/-!
# The check pool

The run's check phase: `checkPool`, with its heartbeat, over the worker map
(`CheckerIO.parMapWorkers`, at `IO` `parMapWorkersIO`).  Part of the proof-carrying driver
(`ConLeche/Driver/*`; the CLI is `Cli.lean`).

A job is a position of the record array: the record's check at the frozen index's view of that
position, from a fresh memo state (`ConLeche.Cached.recordJob`).  The jobs are independent by
construction, so they are handed to `n` long-lived worker threads.  The work is millions of mostly
tiny checks with a skewed tail (single bodies of an hour exist) and the heavy ones sit CLOSE
TOGETHER in the stream, so a worker claims ONE job per atomic claim off one shared counter: a
cluster of heavy declarations is spread over the whole pool instead of serialising inside one
claimed range, and the only item that can strand the pool is the single largest check.  The worker
map gives the results in job order, and the pool walks them in position order (`collect`): the
first failing job in FOLD order is the verdict -- and the declaration the rejection names --
whatever the workers' timing.

Each worker thread reserves 1 GiB of address space -- see `jobsCount` (`Cli.lean`); the default
count is the hardware thread count.

Nothing in the pool touches the driver's type: what a worker returns carries its own evidence, and
`collect` assembles from the results alone the fact `checkDecls_of_jobs` takes.

The index and the records are marked persistent before the workers start (`Jobs.build`), so a
reference count on them is no operation at all.  A plain run pays one atomic claim per job and two
clock reads (the statistics, `WStats`, kept in the worker's own state and merged at the end); the
heartbeat lane (`--progress`) pays one lock of a mutex per completed job, for an exact
completed-count.  The bump and its line are ONE critical section: with the count taken atomically but
printed after, a worker descheduled between the two let a later count's line overtake its own
(`check 1, 3, 2` -- measured under load, the arena's `counting up` check).  Under the lock the lines
leave in count order, so the lane's lines count up by one whatever the scheduling.
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche

/-- The records' frozen index: what the check phase reads. -/
structure Jobs (ds : Array Declaration) where
  I : ConLeche.Cached.StreamIndex
  hI : I = ConLeche.Cached.buildIndex ds

/-- **The step between the read and the check**: the frozen index of the records, built here, and
the records and the index marked PERSISTENT.  Both are read-only from here on.  The check phase runs
on worker threads at every `--jobs=<n>`, so the runtime would mark that graph MULTI-THREADED, and
every reference count on it would be an atomic read-modify-write on a cache line all the workers
touch; nothing in the graph is freed or mutated again, and marking it persistent removes the counting
altogether (DESIGN.md's task #269 section: 18-32 % of the wall time on the pool, growing with the
worker count, and 3.5 % at `--jobs=1`).

The mark's result is DISCARDED: `Runtime.markPersistent` is the identity on the value and marks the
object graph in place, so nothing downstream has to be transported across it and no verdict can turn
on it.  It is unsafe only in that the marked closure is never freed, and the process exits right
after. -/
def Jobs.build (ds : Array Declaration) : IO (Jobs ds) := do
  let _ ← unsafe Runtime.markPersistent ds
  let J : Jobs ds := ⟨ConLeche.Cached.buildIndex ds, rfl⟩
  let _ ← unsafe Runtime.markPersistent J
  return J

/-- What every worker reads besides the records and the index (an `--olean` run's references to
the values still in their files), marked persistent as they are (`Jobs.build` says why). -/
def markShared {α : Type} (x : α) : IO Unit := do
  let _ ← unsafe Runtime.markPersistent x

/-- What the check phase establishes: every job passes. -/
abbrev JAll (mode : ConLeche.CheckMode) (maxNatSize : Nat) {ds : Array Declaration} (J : Jobs ds) : Prop :=
  ∀ k (hk : k < ds.size), ConLeche.Cached.recordJob mode ConLeche.natOpPinSets maxNatSize J.I k ds[k] = .ok ()

/-- A job that passed: its position, with the evidence. -/
abbrev JPass (mode : ConLeche.CheckMode) (maxNatSize : Nat) {ds : Array Declaration} (J : Jobs ds) : Type :=
  { t : Nat // ∀ ht : t < ds.size,
      ConLeche.Cached.recordJob mode ConLeche.natOpPinSets maxNatSize J.I t ds[t] = .ok () }

/-- A job's result: the position whose job passed, or the failure with its position. -/
abbrev JRes (mode : ConLeche.CheckMode) (maxNatSize : Nat) {ds : Array Declaration} (J : Jobs ds) : Type :=
  Except (ConLeche.CheckError × Nat) (JPass mode maxNatSize J)

/-- Job `t`'s label for the statistics: kind, name and fold position. -/
def jobLabel (ds : Array Declaration) (t : Nat) : String :=
  match ds[t]? with
  | some d => s!"{ConLeche.Cached.declCLabel d} (#{t})"
  | none => s!"record {t}"

/-- The check phase's heartbeat: when `pace` says a line is due, with `n` checks completed so far,
job `t` the one just completed, one line, naming it if every check gets one (`Pace.trace`).  The
counter is the number of COMPLETED checks, so in the pool it is monotone whichever worker finished,
and the line is printed after the check rather than before it: a check that is running is not on any
line, the gap between two lines is where it sits.  In the pool (`live`), the line ends with the
number of busy workers and the oldest check in flight with its age (`Live.report`). -/
def checkHeartbeat (err : IO.FS.Stream) (pace : Pace) (t0 : Nat) (ds : Array Declaration)
    (last : IO.Ref Nat) (live : Option Live) (n t : Nat) : IO Unit := do
  if ← pace.due last n ds.size then
    let now ← IO.monoMsNow
    let extra ← match live with
      | some lv => lv.report (jobLabel ds) (if pace.trace then 0 else oldestAge)
      | none => pure ""
    let l := if !pace.trace then "" else match ds[t]? with
      | some d => s!" {ConLeche.Cached.declCLabel d}"
      | none => s!" record {t}"
    err.putStr s!"con-leche: check {n} ({n * 100 / max 1 ds.size}%){l} \
      t={ConLeche.Cached.msSecs (now - t0)}s{extra}\n"
    err.flush

/-- Job `t`, run. -/
def runAt (mode : ConLeche.CheckMode) (maxNatSize : Nat) {ds : Array Declaration} (J : Jobs ds) (t : Nat) :
    JRes mode maxNatSize J :=
  if ht : t < ds.size then
    match h : ConLeche.Cached.recordJob mode ConLeche.natOpPinSets maxNatSize J.I t ds[t] with
    | .ok () => .ok ⟨t, fun _ => h⟩
    | .error e => .error (e, t)
  else .error (.internal s!"check phase: no job {t}", t)

/-- The results walked in position order, from `k`: the first failure, or every job's pass. -/
def collectFrom (mode : ConLeche.CheckMode) (maxNatSize : Nat) {ds : Array Declaration} (J : Jobs ds)
    (tab : Array (JPass mode maxNatSize J)) (k : Nat)
    (acc : ∀ j (hj : j < ds.size), j < k →
      ConLeche.Cached.recordJob mode ConLeche.natOpPinSets maxNatSize J.I j ds[j] = .ok ()) :
    Except (ConLeche.CheckError × Nat) (PLift (JAll mode maxNatSize J)) :=
  if hk : k < ds.size then
    match tab[k]? with
    | some ⟨t, h⟩ =>
      if ht : t = k then
        collectFrom mode maxNatSize J tab (k + 1) fun j hj hlt =>
          if hjk : j = k then by subst hjk; subst ht; exact h hk
          else acc j hj (by omega)
      else .error (.internal s!"check phase: job {k} answered for {t}", k)
    | none => .error (.internal s!"check phase: no result for job {k}", k)
  else .ok ⟨fun j hj => acc j hj (by omega)⟩
  termination_by ds.size - k

/-- The results, in job order, walked into the check phase's fact. -/
def collect (mode : ConLeche.CheckMode) (maxNatSize : Nat) {ds : Array Declaration} (J : Jobs ds)
    (rs : List (JPass mode maxNatSize J)) : Except (ConLeche.CheckError × Nat) (PLift (JAll mode maxNatSize J)) :=
  collectFrom mode maxNatSize J rs.toArray 0 (fun _ _ h => absurd h (Nat.not_lt_zero _))

/-! ### The pool -/

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

/-- A job ended on worker `w`: if it passed, on the heartbeat lane the completed-count is bumped
and its line printed under one lock, so the lines count up.  Its time, into the worker's
statistics. -/
def jobEnd (err : IO.FS.Stream) (pace : Pace) (t0 : Nat) (ds : Array Declaration) (pl : PoolLive)
    (w t ts : Nat) (ok : Bool) (st : WStats) : IO WStats := do
  let te ← IO.monoNanosNow
  if ok && pace.on then
    if let some lv := pl.live then lv.idle w
    pl.done.atomically do
      let n ← modifyGet fun d => (d + 1, d + 1)
      checkHeartbeat err pace t0 ds pl.last pl.live n t
  return st.add t ts te

/-- One job of the pool, on worker `s.1`: run and timed (the job is forced before the clock, by
the branch on its result). -/
def checkStep (mode : ConLeche.CheckMode) (maxNatSize : Nat) (err : IO.FS.Stream) (pace : Pace) (t0 : Nat)
    {ds : Array Declaration} (J : Jobs ds) (pl : PoolLive) (s : Nat × WStats) (t : Nat) :
    IO ((Nat × WStats) × JRes mode maxNatSize J) := do
  let ts ← jobBegin pl pace s.1 t
  let r := runAt mode maxNatSize J t
  let st ← jobEnd err pace t0 ds pl s.1 t ts (r matches .ok _) s.2
  return ((s.1, st), r)

/-- A pool's name in the statistics. -/
def poolName (workers : Nat) : String :=
  if workers ≤ 1 then "check (one worker)" else "check pool"

/-- **The check phase on `jobs` worker threads** (`parMapWorkersIO`): one job per atomic claim, a
worker that fails a job stops every job above it, and the result is the walk over the jobs in
order, which stops at the first failure in FOLD order whatever the workers' timing.  It runs on a
dedicated thread at every count, one included: the check's memo state comes out of the running
thread's own heap, and the main thread's heap after the read is the live records with the read's
freed temporaries scattered through it, which costs a factor of two in wall time at Mathlib scale
for the same instructions.  A worker that fails as an `IO` action (not a check failing) is an
internal error, exit 3, never a verdict.  Beside the result, the pool's timing report (`PoolRep`,
performance-only). -/
def checkPool (mode : ConLeche.CheckMode) (maxNatSize : Nat) (err : IO.FS.Stream) (pace : Pace) (t0 jobs : Nat)
    {ds : Array Declaration} (J : Jobs ds) :
    IO (PoolRep × Except (ConLeche.CheckError × Nat) (PLift (JAll mode maxNatSize J))) := do
  let m := ds.size
  let workers := max 1 (min jobs m)
  let pl ← PoolLive.new pace workers
  let tStart ← IO.monoNanosNow
  try
    let (ss, res) ← parMapWorkersIO jobs (fun w => (w, ({} : WStats)))
      (checkStep mode maxNatSize err pace t0 J pl) (List.range m)
    let tEnd ← IO.monoNanosNow
    let rep : PoolRep := { name := poolName workers, workers, tStart, tEnd,
                           stats := (ss.map (·.2)).toArray }
    match res with
    | .error e => return (rep, .error e)
    | .ok rs => return (rep, collect mode maxNatSize J rs)
  catch ioe =>
    let tEnd ← IO.monoNanosNow
    let rep : PoolRep := { name := poolName workers, workers, tStart, tEnd, stats := #[] }
    return (rep, .error (.internal s!"check phase: a worker failed: {ioe}", 0))

end ConLeche.Driver
