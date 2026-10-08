module

public import ConLeche.Cached.Installed
public import Std.Sync.Mutex
public import ConLeche.Driver.Stats

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
claim per record and two clock reads (the statistics, `WStats`, kept
in the worker's own loop and merged at the end); the heartbeat lane (`--progress`) pays one lock of a
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

/-- Recorded check `k`'s label for the statistics: kind, name and fold
position. -/
def checkLabel {mode : ConLeche.CheckMode} {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds) (k : Nat) : String :=
  match e.pend[k]? with
  | some p => s!"{p.vg.kind.word} {p.vg.cvA.name} (#{p.pos})"
  | none => s!"check {k}"

/-- The check phase's heartbeat: on the `stride`-th completed check
(`n` completed so far, record `k` the one just completed), one line
naming it.  The counter is the number of COMPLETED checks, so in the
pool it is monotone whichever worker finished, and the line is printed
after the check rather than before it: a check that is running is not
on any line, the gap between two lines is where it sits.  In the pool
(`live`), the line ends with the number of busy workers and the oldest
check in flight with its age (`Live.report`). -/
def checkHeartbeat (err : IO.FS.Stream) (stride t0 : Nat) {mode : ConLeche.CheckMode}
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds)
    (live : Option Live) (n k : Nat) (hk : k < e.pend.size) : IO Unit := do
  if stride > 0 && n % stride == 0 then
    let now ← IO.monoMsNow
    let extra ← match live with
      | some lv => lv.report (checkLabel e)
      | none => pure ""
    err.putStr s!"con-leche: check {n}/{e.pend.size} \
      {e.pend[k].vg.kind.word} {e.pend[k].vg.cvA.name} \
      t={ConLeche.Cached.msSecs (now - t0)}s{extra}\n"
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
With `--progress`, one line per `stride` completed checks.  `st` is
the timing (`WStats`, performance-only), returned beside the result. -/
def checkLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds) :
    (k : Nat) → (∀ j, j < k → ConLeche.Cached.GroupChecked mode e j) → WStats →
      IO (WStats × Except (ConLeche.CheckError × Nat)
        (PLift (∀ i, ConLeche.Cached.GroupChecked mode e i)))
  | k, acc, st =>
    if hk : k < e.pend.size then do
      let ts ← IO.monoNanosNow
      match ConLeche.Cached.checkRecord mode e k hk with
      | .ok ⟨h⟩ =>
        let te ← IO.monoNanosNow
        checkHeartbeat err stride t0 e none (k + 1) k hk
        checkLoop mode err stride t0 e (k + 1) (ConLeche.Cached.groupChecked_extend mode acc h)
          (st.add k ts te)
      | .error e' =>
        let te ← IO.monoNanosNow
        return (st.add k ts te, .error e')
    else
      return (st, .ok ⟨ConLeche.Cached.groupChecked_all mode
        (fun j hj => acc j (Nat.lt_of_lt_of_le hj (Nat.le_of_not_lt hk)))⟩)
  termination_by k => e.pend.size - k

/-! ### The pool: phase B on `--jobs=<n>` threads -/

/-- A worker's result for one record: the record with its evidence
`Q`, or the error tagged with its fold position. -/
abbrev RecResultQ (Q : Nat → Prop) : Type :=
  Except (ConLeche.CheckError × Nat) { k : Nat // Q k }

/-- One claimed record of one worker: below the shared `limit` it is
checked and its result appended; a failure lowers the limit to its
index; on the heartbeat lane the completed-count is bumped and its
line printed under one lock, so the lines count up.  A record
at or above the limit is skipped — it is above a known failure and the
walk will never ask for it.  The check is timed into the worker's own
`st`; on the heartbeat lane worker `w` also publishes the record it is
on (`live`). -/
def checkOne (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds)
    {Q : Nat → Prop} (chk : (k : Nat) → k < e.pend.size → RecResultQ Q)
    (limit : IO.Ref Nat) (done : Std.Mutex Nat) (live : Live) (w : Nat)
    (k : Nat) (hk : k < e.pend.size)
    (acc : Array (Nat × RecResultQ Q)) (st : WStats) :
    IO (Array (Nat × RecResultQ Q) × WStats) := do
  if k < (← limit.get) then
    let ts ← IO.monoNanosNow
    if stride > 0 then live.begin w k ts
    let r := chk k hk
    let bad := r matches .error _
    -- (read in a branch on `bad`, so the check is forced before the clock)
    let te ← if bad then IO.monoNanosNow else IO.monoNanosNow
    if bad then
      limit.modify (min · k)
    let acc := acc.push (k, r)
    if stride > 0 then
      live.idle w
      done.atomically do
        let n ← modifyGet fun d => (d + 1, d + 1)
        checkHeartbeat err stride t0 e (some live) n k hk
    return (acc, st.add k ts te)
  else return (acc, st)

/-- One worker: claim ONE record off the shared counter, check it,
repeat until the counter is past the records.  The fuel is exact:
every claim advances the counter by exactly one, so `pend.size + 1`
claims see it past the end whatever the other workers do. -/
def checkWorker (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds)
    {Q : Nat → Prop} (chk : (k : Nat) → k < e.pend.size → RecResultQ Q)
    (next limit : IO.Ref Nat) (done : Std.Mutex Nat) (live : Live) (w : Nat) :
    (fuel : Nat) → Array (Nat × RecResultQ Q) → WStats →
      IO (Array (Nat × RecResultQ Q) × WStats)
  | 0, acc, st => pure (acc, st)
  | fuel + 1, acc, st => do
    let k ← next.modifyGet fun a => (a, a + 1)
    if hk : k < e.pend.size then
      let (acc, st) ← checkOne mode err stride t0 e chk limit done live w k hk acc st
      checkWorker mode err stride t0 e chk next limit done live w fuel acc st
    else pure (acc, st)

/-- The workers' arrays merged by record index into one table. -/
def mergeResults {Q : Nat → Prop}
    (tab : Array (Option (RecResultQ Q))) :
    List (Array (Nat × RecResultQ Q)) → Array (Option (RecResultQ Q))
  | [] => tab
  | rs :: rest => mergeResults (rs.foldl (fun tab (k, r) => tab.set! k (some r)) tab) rest

/-- **The results, assembled in record order** (any property `Q` of the
records, each record's own evidence): the walk stops at the first
failure in record order, so the verdict is the sequential walk's
whatever order the results were produced in.  A slot that is empty or
holds another record's result is an internal error. -/
def collectQ {Q : Nat → Prop} (n : Nat) (pos : Nat → Nat) (tab : Array (Option (RecResultQ Q))) :
    (j : Nat) → (∀ i, i < j → Q i) → Except (ConLeche.CheckError × Nat) (PLift (∀ i, i < n → Q i))
  | j, acc =>
    if hj : j < n then
      match tab[j]? with
      | some (some (.ok ⟨k, hk⟩)) =>
        if h : k = j then
          collectQ n pos tab (j + 1) (fun i hi => by
            by_cases hij : i < j
            · exact acc i hij
            · have : i = j := by omega
              subst this; exact h ▸ hk)
        else .error (.internal s!"check phase: slot {j} holds record {k}", pos j)
      | some (some (.error err)) => .error err
      | _ => .error (.internal s!"check phase: record {j} was never checked", pos j)
    else .ok ⟨fun i hi => acc i (Nat.lt_of_lt_of_le hi (Nat.le_of_not_lt hj))⟩
  termination_by j => n - j

/-- **Phase B on a pool of `jobs` worker threads**, for any per-record
check `chk` with its evidence `Q`.  Spawns `min jobs pend.size`
workers, waits for all of them, merges their results and walks the
table in record order.  A worker that failed as an `IO` action (not a
check failing — the pool's own machinery) is an internal error, exit
3, never a verdict on the input.  Beside the result, the pool's timing
report (`PoolRep`, performance-only). -/
def checkPoolQ (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 jobs : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds)
    {Q : Nat → Prop} (chk : (k : Nat) → k < e.pend.size → RecResultQ Q) :
    IO (PoolRep × Except (ConLeche.CheckError × Nat) (PLift (∀ i, i < e.pend.size → Q i))) := do
  let m := e.pend.size
  let workers := max 1 (min jobs m)
  let next ← IO.mkRef 0
  let limit ← IO.mkRef m
  let done ← Std.Mutex.new 0
  let live ← Live.new (if stride > 0 then workers else 0)
  let tStart ← IO.monoNanosNow
  let mut tasks : Array (Task (Except IO.Error (Array (Nat × RecResultQ Q) × WStats))) := #[]
  for w in [0:workers] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated)
      (checkWorker mode err stride t0 e chk next limit done live w (m + 1) #[] {}))
  let mut results : List (Array (Nat × RecResultQ Q)) := []
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
  return (rep, collectQ m (fun j => if h : j < m then e.pend[j].pos else 0) tab 0
    (fun j hj => absurd hj (Nat.not_lt_zero j)))

/-- **Phase B on a pool**: every record's check (`checkRecord`), its
`GroupChecked` facts assembled. -/
def checkPool (mode : ConLeche.CheckMode) (err : IO.FS.Stream) (stride t0 jobs : Nat)
    {ds : List ConLeche.Declaration}
    (e : ConLeche.Cached.InstalledEnv mode ConLeche.natOpPinSets ds) :
    IO (PoolRep × Except (ConLeche.CheckError × Nat)
      (PLift (∀ i, ConLeche.Cached.GroupChecked mode e i))) := do
  let (rep, r) ← checkPoolQ mode err stride t0 jobs e (Q := ConLeche.Cached.GroupChecked mode e)
    fun k hk => match ConLeche.Cached.checkRecord mode e k hk with
      | .ok ⟨h⟩ => .ok ⟨k, h⟩
      | .error err => .error err
  match r with
  | .ok ⟨h⟩ => return (rep, .ok ⟨ConLeche.Cached.groupChecked_all mode h⟩)
  | .error err => return (rep, .error err)

end ConLeche.Driver
