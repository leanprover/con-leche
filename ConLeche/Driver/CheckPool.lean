module

public import ConLeche.Cached.StreamIndex
public import Std.Sync.Mutex
public import ConLeche.Driver.Stats

/-!
# The check pool

The loops of the run's check phase: `checkLoop`, the sequential loop at `--jobs=1`, and `checkPool`,
the pool at `--jobs=<n>`, with the heartbeat they share.  Part of the proof-carrying driver
(`ConLeche/Driver/*`; the CLI is `Cli.lean`).

A job is a position of the record array: the record's check at the frozen index's view of that
position, from a fresh memo state (`ConLeche.Cached.recordJob`).  The jobs are independent by
construction, so they are handed to `n` long-lived worker tasks (`IO.asTask` on dedicated threads:
exactly `n` threads whatever the runtime's own pool size).  The work is millions of mostly tiny
checks with a skewed tail (single bodies of an hour exist) and the heavy ones sit CLOSE TOGETHER in
the stream, so a worker claims ONE job per atomic claim off one shared counter: a cluster of heavy
declarations is spread over the whole pool instead of serialising inside one claimed range, and the
only item that can strand the pool is the single largest check.  The claim costs one `modifyGet` on
an `IO.Ref` per job, which is below the third decimal of a run.  Each worker keeps its results in
its own array (job index, `JRes`).  The pool merges the arrays by index into one table and walks it
in position order (`collect`): the walk stops at the first failing job in FOLD order, so the verdict
-- and the declaration the rejection names -- is the sequential walk's whatever the workers' timing.
**Determinism on a failure**: a worker that fails job `f` lowers the shared `limit` to `f`, and no
worker starts a job at or above the limit -- every job below `f` was claimed before `f` was (the
counter is monotone) and is finished by the worker that claimed it, so the table is complete below
the first failure; jobs above it may be missing, and the walk never reaches them.  A worker cannot be
cancelled mid-check (a check is a pure computation), so the pool drains.

Each worker thread reserves 1 GiB of address space -- see `jobsCount` (`Cli.lean`); the default count
is the hardware thread count.

Nothing in the pool touches the driver's type: what a worker returns carries its own evidence, and
`collect` assembles from the table alone the fact `checkDecls_of_jobs` takes.

The index and the records are marked persistent before the workers start (`Jobs.build`), so a
reference count on them is no operation at all.  A plain run pays one atomic claim per job and two
clock reads (the statistics, `WStats`, kept in the worker's own loop and merged at the end); the
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

/-- **The step between the parse and the check**: the frozen index of the records, built here, and
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

/-- What the check phase establishes: every job passes. -/
abbrev JAll (mode : ConLeche.CheckMode) {ds : Array Declaration} (J : Jobs ds) : Prop :=
  ∀ k (hk : k < ds.size), ConLeche.Cached.recordJob mode ConLeche.natOpPinSets J.I k ds[k] = .ok ()

/-- A job's result: the position whose job passed, or the failure with its position. -/
abbrev JRes (mode : ConLeche.CheckMode) {ds : Array Declaration} (J : Jobs ds) : Type :=
  Except (ConLeche.CheckError × Nat)
    { t : Nat // ∀ ht : t < ds.size,
      ConLeche.Cached.recordJob mode ConLeche.natOpPinSets J.I t ds[t] = .ok () }

/-- Job `t`'s label for the statistics: kind, name and fold position. -/
def jobLabel (ds : Array Declaration) (t : Nat) : String :=
  match ds[t]? with
  | some d => s!"{ConLeche.Cached.declCLabel d} (#{t})"
  | none => s!"record {t}"

/-- The check phase's heartbeat: on the `stride`-th completed check (`n` completed so far, job `t` the
one just completed), one line naming it.  The counter is the number of COMPLETED checks, so in the
pool it is monotone whichever worker finished, and the line is printed after the check rather than
before it: a check that is running is not on any line, the gap between two lines is where it sits.  In
the pool (`live`), the line ends with the number of busy workers and the oldest check in flight with
its age (`Live.report`). -/
def checkHeartbeat (err : IO.FS.Stream) (stride t0 : Nat) (ds : Array Declaration)
    (live : Option Live) (n t : Nat) : IO Unit := do
  if stride > 0 && n % stride == 0 then
    let now ← IO.monoMsNow
    let extra ← match live with
      | some lv => lv.report (jobLabel ds)
      | none => pure ""
    let l := match ds[t]? with
      | some d => ConLeche.Cached.declCLabel d
      | none => s!"record {t}"
    err.putStr s!"con-leche: check {n}/{ds.size} {l} \
      t={ConLeche.Cached.msSecs (now - t0)}s{extra}\n"
    err.flush

/-- Job `t`, run. -/
def runAt (mode : ConLeche.CheckMode) {ds : Array Declaration} (J : Jobs ds) (t : Nat) :
    JRes mode J :=
  if ht : t < ds.size then
    match h : ConLeche.Cached.recordJob mode ConLeche.natOpPinSets J.I t ds[t] with
    | .ok () => .ok ⟨t, fun _ => h⟩
    | .error e => .error (e, t)
  else .error (.internal s!"check phase: no job {t}", t)

/-- **The check phase in one thread -- the check pass at `--jobs=1`.**  The jobs in fold order, each
result in its slot of the table, until the first failure; the table is then walked (`collect`).
Nothing is shared with any other thread and no counter is claimed: this loop is the sequential
baseline the pool below is measured against.  It runs on ONE DEDICATED WORKER THREAD all the same: the
loop's cost is dominated by the per-check memo state, that state comes out of the running thread's own
mimalloc heap, and the main thread's heap after the parse is the live records with the parse's freed
temporaries scattered through it -- allocating the check phase out of that scatter costs a factor of
two in wall time at Mathlib scale for the same instructions.  With `--progress`, one line per `stride`
completed checks.  `st` is the timing (`WStats`, performance-only), returned beside the result. -/
def checkLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : Array Declaration} (J : Jobs ds) :
    (t : Nat) → Array (Option (JRes mode J)) → WStats →
      IO (WStats × Array (Option (JRes mode J)))
  | t, tab, st =>
    if t < ds.size then do
      let ts ← IO.monoNanosNow
      let r := runAt mode J t
      let bad := r matches .error _
      -- (read in a branch on `bad`, so the check is forced before the clock)
      let te ← if bad then IO.monoNanosNow else IO.monoNanosNow
      let tab := tab.set! t (some r)
      if bad then return (st.add t ts te, tab)
      checkHeartbeat err stride t0 ds none (t + 1) t
      checkLoop mode err stride t0 J (t + 1) tab (st.add t ts te)
    else
      return (st, tab)
  termination_by t => ds.size - t

/-- The table walked in position order, from `k`: the first failure, or every job's pass. -/
def collectFrom (mode : ConLeche.CheckMode) {ds : Array Declaration} (J : Jobs ds)
    (tab : Array (Option (JRes mode J))) (k : Nat)
    (acc : ∀ j (hj : j < ds.size), j < k →
      ConLeche.Cached.recordJob mode ConLeche.natOpPinSets J.I j ds[j] = .ok ()) :
    Except (ConLeche.CheckError × Nat) (PLift (JAll mode J)) :=
  if hk : k < ds.size then
    match tab[k]? with
    | some (some (.ok ⟨t, h⟩)) =>
      if ht : t = k then
        collectFrom mode J tab (k + 1) fun j hj hlt =>
          if hjk : j = k then by subst hjk; subst ht; exact h hk
          else acc j hj (by omega)
      else .error (.internal s!"check phase: job {k} answered for {t}", k)
    | some (some (.error e)) => .error e
    | _ => .error (.internal s!"check phase: no result for job {k}", k)
  else .ok ⟨fun j hj => acc j hj (by omega)⟩
  termination_by ds.size - k

/-- The table walked into the check phase's fact. -/
def collect (mode : ConLeche.CheckMode) {ds : Array Declaration} (J : Jobs ds)
    (tab : Array (Option (JRes mode J))) :
    Except (ConLeche.CheckError × Nat) (PLift (JAll mode J)) :=
  collectFrom mode J tab 0 (fun _ _ h => absurd h (Nat.not_lt_zero _))

/-! ### The pool: the check phase on `--jobs=<n>` threads -/

/-- One claimed job of one worker: below the shared `limit` it is run
and its result appended; a failure lowers the limit to its index; on
the heartbeat lane the completed-count is bumped and its line printed
under one lock, so the lines count up.  A job at or above the limit is
skipped — it is above a known failure and the walk will never ask for
it.  The job is timed into the worker's own `st`; on the heartbeat lane
worker `w` also publishes the job it is on (`live`). -/
def checkOne (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : Array Declaration} (J : Jobs ds)
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
        checkHeartbeat err stride t0 ds (some live) n t
    return (acc, st.add t ts te)
  else return (acc, st)

/-- One worker: claim ONE job off the shared counter, run it, repeat
until the counter is past the jobs.  The fuel is exact: every claim
advances the counter by exactly one, so `ds.size + 1` claims see it
past the end whatever the other workers do. -/
def checkWorker (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : Array Declaration} (J : Jobs ds)
    (next limit : IO.Ref Nat) (done : Std.Mutex Nat) (live : Live) (w : Nat) :
    (fuel : Nat) → Array (Nat × JRes mode J) → WStats →
      IO (Array (Nat × JRes mode J) × WStats)
  | 0, acc, st => pure (acc, st)
  | fuel + 1, acc, st => do
    let t ← next.modifyGet fun a => (a, a + 1)
    if t < ds.size then
      let (acc, st) ← checkOne mode err stride t0 J limit done live w t acc st
      checkWorker mode err stride t0 J next limit done live w fuel acc st
    else pure (acc, st)

/-- The workers' arrays merged by job index into one table. -/
def mergeResults {mode : ConLeche.CheckMode} {ds : Array Declaration} {J : Jobs ds}
    (tab : Array (Option (JRes mode J))) :
    List (Array (Nat × JRes mode J)) → Array (Option (JRes mode J))
  | [] => tab
  | rs :: rest => mergeResults (rs.foldl (fun tab (k, r) => tab.set! k (some r)) tab) rest

/-- **The check phase on a pool of `jobs` worker threads.**  Spawns
`min jobs ds.size` workers, waits for all of them, merges their
results and walks the table in job order.  A worker that failed as an
`IO` action (not a check failing — the pool's own machinery) is an
internal error, exit 3, never a verdict on the input.  Beside the
result, the pool's timing report (`PoolRep`, performance-only). -/
def checkPool (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 jobs : Nat)
    {ds : Array Declaration} (J : Jobs ds) :
    IO (PoolRep × Except (ConLeche.CheckError × Nat) (PLift (JAll mode J))) := do
  let m := ds.size
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
