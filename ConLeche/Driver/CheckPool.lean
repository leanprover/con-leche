module

public import ConLeche.Cached.Installed
public import Std.Sync.Mutex

/-!
# Phase B: the check pool (task #329)

Phase B's loops, pulled out of `Main.lean` when the driver split into
`ConLeche/Driver/*` (the CLI stays in `Main.lean`; the proof-carrying
driver moved here, to `Driver/CheckPool.lean`, `Driver/ParInstall.lean`
and `Driver/Run.lean`).  A pure move: no logic changed, only the
module boundary.

The records' checks are independent by construction — each reads the
installed index at its own prefix view, its own record, and a fresh
memo state — so phase B is handed to `n` long-lived worker tasks
(`IO.asTask` on dedicated threads: exactly `n` threads whatever the
runtime's own pool size).  The work is millions of mostly tiny checks
with a skewed tail (single bodies of an hour exist) and the heavy ones
sit CLOSE TOGETHER in the stream, so a worker claims ONE record per
atomic claim off one shared counter: a cluster of heavy declarations is
spread over the whole pool instead of serialising inside one claimed
range, and the only item that can strand the pool is the single largest
check.  The claim costs one `modifyGet` on an `IO.Ref` per record,
which is below the third decimal of a run.  Each worker keeps
its results in its own array (record index, `RecordResult`), which
is what a record's check IS: the `GroupChecked` fact of that record
or its tagged error (`ConLeche.Cached.checkRecordResult`).  The pool
merges the arrays by index into one table and walks it in record
order (`ConLeche.Cached.collectChecks`): the walk stops at the first
failing record in FOLD order, so the verdict — and the declaration the
rejection names — is the sequential walk's, `checkPendingList`'s,
whatever the workers' timing.  **Determinism on a failure**: a worker
that fails record `f` lowers the shared `limit` to `f`, and no worker
starts a record at or above the limit — every record below `f` was
claimed before `f` was (the counter is monotone) and is finished by
the worker that claimed it, so the table is complete below the first
failure; records above it may be missing, and the walk never reaches
them.  A worker cannot be cancelled mid-check (a check is a pure
computation), so the pool drains.

Each worker thread reserves 1 GiB of address space — see
`jobsCount` (`Main.lean`); the default count is the hardware thread
count.

Nothing in the pool touches the driver's type: what a worker returns
carries its own evidence, and `collectChecks` assembles the
`∀ i, GroupChecked mode e i` the fully checked environment asks for
from the table alone.  The transfer theorem is untouched.

The runtime marks everything reachable from a task's closure — the
installed index and the records — for multi-threaded reference
counting once, on the first spawn (an object already marked is not
walked again); every reference-count operation on those objects is
atomic from then on, which is the pool's instruction overhead over
the sequential loop.  A plain run pays, on top of that, one atomic
claim per record; the heartbeat lane (`--progress`) pays one lock of a
mutex per completed record, for an exact completed-count.  The bump
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

/-- The check phase's heartbeat: on the `stride`-th completed check
(`n` completed so far, record `k` the one just completed), one line
naming it.  The counter is the number of COMPLETED checks, so in the
pool it is monotone whichever worker finished, and the line is printed
after the check rather than before it: a check that is running is not
on any line, the gap between two lines is where it sits. -/
def checkHeartbeat (err : IO.FS.Stream) (stride t0 : Nat) {mode : ConLeche.CheckMode}
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds)
    (n k : Nat) (hk : k < e.pend.size) : IO Unit := do
  if stride > 0 && n % stride == 0 then
    let now ← IO.monoMsNow
    err.putStr s!"con-leche: check {n}/{e.pend.size} \
      {e.pend[k].vg.kind.word} {e.pend[k].vg.cvA.name} \
      t={ConLeche.Cached.msSecs (now - t0)}s\n"
    err.flush

/-- **Phase B in one thread — the check pass at `--jobs=1`.**  Record
`k` is checked against the prefix view of the installed index from a
fresh memo state (`ConLeche.Cached.checkRecord`), and the accumulator —
`GroupChecked` of every record below `k`, a proposition — grows by
one; at the end every record is checked, which with the installed
environment IS a `FullyChecked mode natOpPinSets ds`, phase B of the fold
`checkDecls`.  Nothing is shared with any other thread and no counter
is claimed: this loop is the sequential baseline the pool below is
measured against.  It runs on ONE DEDICATED WORKER THREAD all the
same: the loop's cost is dominated by the per-record memo
state, that state comes out of the running thread's own mimalloc heap,
and the main thread's heap after the install phase is two gigabytes of
live environment with the parse's and the install's freed temporaries
scattered through it — allocating phase B out of that scatter costs a
factor of two in wall time at Mathlib scale for the same instructions.
With `--progress`, one line per `stride` completed checks. -/
def checkLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds) :
    (k : Nat) → (∀ j, j < k → ConLeche.Cached.GroupChecked mode e j) →
      IO (Except (ConLeche.CheckError × Nat) (PLift (∀ i, ConLeche.Cached.GroupChecked mode e i)))
  | k, acc =>
    if hk : k < e.pend.size then do
      match ConLeche.Cached.checkRecord mode e k hk with
      | .ok ⟨h⟩ =>
        checkHeartbeat err stride t0 e (k + 1) k hk
        checkLoop mode err stride t0 e (k + 1) (ConLeche.Cached.groupChecked_extend mode acc h)
      | .error e' => return .error e'
    else
      return .ok ⟨ConLeche.Cached.groupChecked_all mode
        (fun j hj => acc j (Nat.lt_of_lt_of_le hj (Nat.le_of_not_lt hk)))⟩
  termination_by k => e.pend.size - k

/-! ### The pool: phase B on `--jobs=<n>` threads -/

/-- One claimed record of one worker: below the shared `limit` it is
checked and its result appended; a failure lowers the limit to its
index; on the heartbeat lane the completed-count is bumped and its
line printed under one lock, so the lines count up.  A record
at or above the limit is skipped — it is above a known failure and the
walk will never ask for it. -/
def checkOne (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds)
    (limit : IO.Ref Nat) (done : Std.Mutex Nat) (k : Nat) (hk : k < e.pend.size)
    (acc : Array (Nat × ConLeche.Cached.RecordResult mode e)) :
    IO (Array (Nat × ConLeche.Cached.RecordResult mode e)) := do
  if k < (← limit.get) then
    let r := ConLeche.Cached.checkRecordResult mode e k hk
    if r matches .error _ then
      limit.modify (min · k)
    let acc := acc.push (k, r)
    if stride > 0 then
      done.atomically do
        let n ← modifyGet fun d => (d + 1, d + 1)
        checkHeartbeat err stride t0 e n k hk
    return acc
  else return acc

/-- One worker: claim ONE record off the shared counter, check it,
repeat until the counter is past the records.  The fuel is exact:
every claim advances the counter by exactly one, so `pend.size + 1`
claims see it past the end whatever the other workers do. -/
def checkWorker (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds)
    (next limit : IO.Ref Nat) (done : Std.Mutex Nat) :
    (fuel : Nat) → Array (Nat × ConLeche.Cached.RecordResult mode e) →
      IO (Array (Nat × ConLeche.Cached.RecordResult mode e))
  | 0, acc => pure acc
  | fuel + 1, acc => do
    let k ← next.modifyGet fun a => (a, a + 1)
    if hk : k < e.pend.size then
      let acc ← checkOne mode err stride t0 e limit done k hk acc
      checkWorker mode err stride t0 e next limit done fuel acc
    else pure acc

/-- The workers' arrays merged by record index into one table. -/
def mergeResults {mode : ConLeche.CheckMode} {ds : List ConLeche.Declaration}
    {e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds}
    (tab : Array (Option (ConLeche.Cached.RecordResult mode e))) :
    List (Array (Nat × ConLeche.Cached.RecordResult mode e)) →
      Array (Option (ConLeche.Cached.RecordResult mode e))
  | [] => tab
  | rs :: rest => mergeResults (rs.foldl (fun tab (k, r) => tab.set! k (some r)) tab) rest

/-- **Phase B on a pool of `jobs` worker threads.**  Spawns
`min jobs pend.size` workers, waits for all of them, merges their
results and walks the table in record order.  A worker that failed as
an `IO` action (not a check failing — the pool's own machinery) is an
internal error, exit 3, never a verdict on the input. -/
def checkPool (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 jobs : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds) :
    IO (Except (ConLeche.CheckError × Nat) (PLift (∀ i, ConLeche.Cached.GroupChecked mode e i))) := do
  let m := e.pend.size
  let workers := max 1 (min jobs m)
  let next ← IO.mkRef 0
  let limit ← IO.mkRef m
  let done ← Std.Mutex.new 0
  let mut tasks : Array (Task (Except IO.Error (Array (Nat × ConLeche.Cached.RecordResult mode e)))) := #[]
  for _ in [0:workers] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated)
      (checkWorker mode err stride t0 e next limit done (m + 1) #[]))
  let mut results : List (Array (Nat × ConLeche.Cached.RecordResult mode e)) := []
  let mut failure : Option IO.Error := none
  for t in tasks do
    match ← IO.wait t with
    | .ok rs => results := rs :: results
    | .error ioe => failure := some ioe
  if let some ioe := failure then
    return .error (.internal s!"check phase: a worker failed: {ioe}", 0)
  let tab := mergeResults (Array.replicate m none) results
  return ConLeche.Cached.collectChecks mode e tab 0 (fun j hj => absurd hj (Nat.not_lt_zero j))

end ConLeche.Driver
