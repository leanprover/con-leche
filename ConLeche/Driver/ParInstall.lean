module

public import ConLeche.Verify.Cached.ViewCongr
public import ConLeche.Cached.InstallSkel
public import Std.Sync.Mutex
public import ConLeche.Driver.Stats
import Std.Data.TreeSet.Basic
import Std.Data.HashSet.Basic

/-!
# Phase A: the serial loop and the parallel install (task #329)

## The serial loop

Each record is installed by `ConLeche.Cached.annotDeclStep`: a
separable value declaration is annotated and pushed with its check
recorded, everything else is checked in full.  The loop carries the
chain of accepting steps (`ConLeche.Cached.InstallRun`) of the records
it has consumed, and returns it with the result.

## The parallel install: phase A on `--jobs=<n>` worker threads

Phase A installs every record from a fresh memo state, so a record's
install is a function of the index it sees and the record alone
(`ConLeche.Cached.annotDeclStep`). The parallel install runs that
function on `n` dedicated worker threads, each record at a **worker
view** (`ConLeche.Cached.workerView`) instead of the serial index, and
keeps THIS thread as the **commit thread**: it walks the records in
order, pushes each record's constants into the serial index and extends
the serial fold's accepting run by one step per record, exactly as
`installLoop` does.  What it returns is therefore `installLoop`'s type —
phase A of the fold — whatever the schedule.

* **The prediction.**  Before any record is installed, the names every
  record will install are read off the records (`predictSlots`, the
  install skeleton), and with them every constant's counter.  The
  frozen base index maps each predicted name to its counter, its record
  and its position (`buildBase`, sharded by name hash).  Record `k`'s
  constants are its SLOT: a thunk over a promise that whoever installs
  the record resolves — the one task-manager object per record, there
  because a lookup is pure code and can wait on nothing else.  A worker
  view sees the base below its record's predicted counter, so a lookup
  waits only on an earlier record.  The prediction, the base, the
  slots, the dependencies and the dependents are each computed on
  per-chunk (per-shard) tasks.
* **The install** of record `k` is `installStep` at the view of its
  predicted counter (`ConLeche/Verify/Cached/ViewCongr.lean`): the
  constants it pushes and, for a definition, theorem or opaque, its
  pending check.  After publishing its slot the installer makes the
  commit's checks (`goodB`: the `And` pin, and every slot the constants
  fill holds that very constant — `slotsOk`, base probes and pointer
  comparisons), and the result travels to the commit thread with its
  evidence (`WRes`) in the record's state (`RState`, an `IO.Ref`).
* **The commit.**  The commit thread takes record `k`'s install result
  (sleeping on its own condition variable if the installer is not done:
  never spinning, never waiting on the task manager), checks that the
  predicted counter is the serial one and the installer's verdict,
  pushes the installer's constants and adds the step by
  `installStep_commit` — the view answers every lookup as the serial
  index does (`ViewAgrees`), and an install at two such indices pushes
  the same constants (`checkDeclStepC_twin`), so the install at the view
  IS the serial step.  The index is marked linear (task #331) as on the
  serial path: the commit thread is its only holder, and a copy panics.
* **Progress.**  A record the commit thread reaches unclaimed it claims
  and installs itself, at its view, which waits on nothing (every earlier
  record is committed).  A worker waits only on earlier records, so no
  cycle exists.
* **Rejections and mispredictions.**  A failing install is reported at
  the first failing record in fold order, with the serial step's error
  (`installStep_commit_error`); a failed `And` pin with the serial
  step's error too (`annotDeclStep` rejects it before installing
  anything).  A misprediction — a counter or a slot that does not match
  — is an internal error (exit 3).  No input reaches it: every accepting
  step installs exactly the predicted skeleton (`annotStepC_skels`).
  Either way, and on an IO exception of the commit thread (a failing
  heartbeat write, rethrown), the workers are stopped, and every
  unresolved slot is resolved empty so that nobody stays waiting.

**Reference counts across threads.**  The records are marked
persistent before the first worker starts, and every install result by
its installer before it is published (it ends up in the installed
environment), so nothing a worker reads of them is counted atomically.
The install's own bookkeeping — the base shards, the dependency edges,
the dependents, the per-record counts and states — dies with the install
but is marked persistent too, on purpose: a base hit takes a reference
on a shard entry, which multi-threaded is an atomic increment on a line
every worker touches, and freeing the rest cost the check phase more
than it saved (task #329's `ifix` lane, DESIGN.md).  The counts and
states are written as well as read; a persistent ref is written through
the runtime's atomic path, and what it stores is a scalar or a fresh
wrapper around a persistent result.  The serial index is the commit
thread's alone: nothing else holds it, so every push updates it in
place.

**The schedule** (performance only): workers walk the records in
stream order off a shared cursor, a block of records per claim
(`cursorBlockSize`), and install
each record that is READY — whose dependencies, the records installing
the names its expressions mention, have all been installed; a record
that is not is installed when its last dependency is, by the worker that
installed that one.  The records up to the basis gate (inside the
built-in prelude) are installed in their dependency order like any
other; past the gate, a record carries no dependency edges to them
(`recDeps`).  The common case takes no lock (`Sched`).
-/

@[expose] public section

namespace ConLeche.Driver

open ConLeche

/-- **Phase A's loop — the driver's install pass, carrying its own
accepting run.**  Each record is installed by
`ConLeche.Cached.annotDeclStep`: a separable value declaration is
annotated and pushed with its check recorded, everything else is checked
in full.  The loop carries the chain of accepting steps
(`ConLeche.Cached.InstallRun`) of the records it has consumed — a
proposition, so nothing at run time — and returns it with the result:
what this loop returns IS an `InstalledEnv mode natOpPinSets ds.toList`
(`ConLeche/Cached/Installed.lean`), phase A of the fold `checkDecls`.
The records are the ARRAY the prepare step produced and the driver
holds to the end anyway (a rejection names its declaration by indexing
it), so the loop walks it BY INDEX — nothing converts a million
records into a list — while the run it carries is over
`ds.toList.take i`, the shape every lemma above it is stated in.
Whatever it prints between steps is irrelevant to that type, which is
why ONE loop serves the plain run and the `--progress` heartbeat
alike.

**Written tail-recursively, threading `p` LINEARLY**: a
`for … in ds` loop with `let mut` accumulators desugars to code that
`lean_inc`s the `FEnv` before each step, so
`lean_is_exclusive` is false at the index inserts and every hashmap
copies its bucket array per declaration — quadratic at Mathlib
scale.  Here the previous `p` is dead at the
recursive call, so the C carries no `lean_inc` of it before the
step, and the cost per declaration is flat.  The run is carried in the
SNOC direction (`InstallRun.snoc`) precisely so that the call stays a
tail call: a cons-direction proof would wrap the result on the way
back, one frame per declaration.  (The index measure makes this a
well-founded recursion; the compiler's recursive function is the same
tail call, and the measure is erased.)

**Stride 1 is the localisation lane.**  With `--progress` (bare, or
`--progress=1`) every declaration is announced before it is installed,
so a run that dies — an OOM, a timeout, a `SIGKILL` — names on its last
line the declaration it died in.  The index is the FOLD position, not
the stream's record index: the prepare step prepends the built-in
prelude and drops the stream's identical copies of its records, so the
two drift apart by a stream-dependent amount.  Calibrate by NAME.

Each step is timed into `st` (`WStats`, performance-only: a ref only
this thread touches). -/
def installLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream)
    (stride total t0 : Nat) (st : IO.Ref WStats)
    (ds : Array ConLeche.Declaration)
    (p₀ : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck) :
    (i : Nat) →
    (p : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck) →
    ConLeche.Cached.InstallRun mode ConLeche.natOpPinSets (ds.toList.take i) p₀ p →
      IO (Except (ConLeche.CheckError × Nat)
        (Σ' (p' : Nat × ConLeche.FEnv × Array ConLeche.Cached.PendingCheck),
          PLift (ConLeche.Cached.InstallRun mode ConLeche.natOpPinSets
            ds.toList p₀ p')))
  | i, p, hrun => do
    if hi : i < ds.size then
      let pd := ds[i]
      if stride > 0 && p.1 % stride == 0 then
        let now ← IO.monoMsNow
        err.putStr s!"con-leche: install {p.1}/{total} \
          {ConLeche.Cached.declCLabel pd} \
          t={ConLeche.Cached.msSecs (now - t0)}s\n"
        err.flush
      let ts ← IO.monoNanosNow
      match h : ConLeche.Cached.annotDeclStep mode ConLeche.natOpPinSets p pd with
      | .ok p₁ =>
        let te ← IO.monoNanosNow
        st.modify (·.add i ts te)
        installLoop mode err stride total t0 st ds p₀ (i + 1) p₁ (by
          have hlist : ds.toList.take (i + 1) = ds.toList.take i ++ [pd] := by
            rw [List.take_add_one]
            simp [pd, Array.getElem?_eq_getElem hi]
          rw [hlist]
          exact ConLeche.Cached.InstallRun.snoc mode hrun h)
      | .error e =>
        let te ← IO.monoNanosNow
        st.modify (·.add i ts te)
        return .error e
    else
      return .ok ⟨p, ⟨by
        rw [List.take_of_length_le (by simp; omega)] at hrun
        exact hrun⟩⟩
  termination_by i => ds.size - i

namespace ParInstall

open ConLeche ConLeche.Cached

/-- What the install of record `k` computes: `installStep` at the view of
the record's predicted counter. -/
def workerRes (mode : CheckMode) (ds : Array Declaration) (B : BaseIdx) (S : Slots)
    (vis : Array Nat) (k : Nat) : Except CheckError (List ConstantInfo × Option ValueGroup) :=
  match ds[k]?, vis[k]? with
  | some pd, some v => installStep mode natOpPinSets (workerView B S v) pd
  | _, _ => .error (.internal "parallel install: no such record")

/-- The constants an install result publishes. -/
def slotOfRes : Except CheckError (List ConstantInfo × Option ValueGroup) → Array ConstantInfo
  | .ok (L, _) => L.toArray
  | .error _ => #[]

/-- **The checks the commit needs, made by the installer**: record `k`
passes the `And` pin and, if it was installed, every constant it pushes
fills the slot the base predicted for it, at the record's predicted
counter.  The installer evaluates it right after publishing the slot
(so the slot check reads its own, just resolved slot), and the commit
thread reads the verdict instead of probing the base itself. -/
def goodB (ds : Array Declaration) (B : BaseIdx) (S : Slots) (vis : Array Nat) (k : Nat)
    (r : Except CheckError (List ConstantInfo × Option ValueGroup)) : Bool :=
  match ds[k]?, vis[k]? with
  | some pd, some v =>
    andPinOk pd && (match r with
      | .ok (L, _) => slotsOk B S v L
      | .error _ => true)
  | _, _ => false

/-- What `goodB` establishes. -/
def GoodAt (ds : Array Declaration) (B : BaseIdx) (S : Slots) (vis : Array Nat) (k : Nat)
    (r : Except CheckError (List ConstantInfo × Option ValueGroup)) : Prop :=
  ∀ pd v, ds[k]? = some pd → vis[k]? = some v →
    andPinOk pd = true ∧
      ∀ L vg?, r = .ok (L, vg?) → slotsOk B S v L = true

theorem goodB_spec {ds : Array Declaration} {B : BaseIdx} {S : Slots} {vis : Array Nat} {k : Nat}
    {r : Except CheckError (List ConstantInfo × Option ValueGroup)}
    (h : goodB ds B S vis k r = true) : GoodAt ds B S vis k r := by
  intro pd v hpd hv
  simp only [goodB, hpd, hv, Bool.and_eq_true] at h
  refine ⟨h.1, fun L vg? hr => ?_⟩
  have h2 := h.2
  rw [hr] at h2
  exact h2

/-- An install result for a record, with its evidence: it is `workerRes`
of that record, and when `good` the commit's checks hold (`GoodAt`) —
erased proofs at run time. -/
def WRes (mode : CheckMode) (ds : Array Declaration) (B : BaseIdx) (S : Slots)
    (vis : Array Nat) : Type :=
  { q : Nat × Except CheckError (List ConstantInfo × Option ValueGroup) × Bool //
      q.2.1 = workerRes mode ds B S vis q.1 ∧
        (q.2.2 = true → GoodAt ds B S vis q.1 q.2.1) }

/-- A record's state, for the workers and the commit thread: not yet
taken, taken by an installer, or installed with its result. -/
inductive RState (α : Type) where
  | free
  | taken
  | done (q : α)

/-! #### The schedule

Performance only — nothing below enters a type.  A record's dependencies
are the records installing the names its expressions mention, plus the
literal and basis names the core may look up on its own.  A dependency
the walk misses costs only a wait, never a verdict. -/

/-- The names an expression mentions: every constant, every projection's
structure and table, the literal support of every literal.  A walk over
the DAG, each shared node once. -/
partial def depNames (e : Expr) (acc : Std.HashSet Expr × Array Name) :
    Std.HashSet Expr × Array Name :=
  match e with
  | .const n _ => (acc.1, acc.2.push n)
  | .bvar _ | .sort _ => acc
  | .lit (.natVal _) => (acc.1, acc.2.push natName)
  | .lit (.strVal _) => (acc.1, acc.2.push stringName |>.push charName |>.push listName)
  | _ =>
    if acc.1.contains e then acc else
      let acc := (acc.1.insert e, acc.2)
      match e with
      | .app f a => depNames a (depNames f acc)
      | .lam ty b _ | .forallE ty b _ => depNames b (depNames ty acc)
      | .letE ty v b => depNames b (depNames v (depNames ty acc))
      | .fvar _ ty => depNames ty acc
      | .proj sn _ x => depNames x (acc.1, acc.2.push sn |>.push (projTableName sn))
      | _ => acc

/-- The basis the core may consult on its own. -/
def basisDepNames : Array Name :=
  #[natName, natZeroName, natSuccName, stringName, stringOfListName, listName,
    listNilName, listConsName, charName, charOfNatName, eqName, andName, boolName]

/-- The expressions of a record its install reads (a theorem's value is
not read at install) and the names it declares. -/
def declExprs : Declaration → List Expr × List Name
  | .defnDecl cv v _ => ([cv.type, v], [cv.name])
  | .thmDecl cv _ => ([cv.type], [cv.name])
  | .opaqueDecl cv v => ([cv.type, v], [cv.name])
  | .axiomDecl cv => ([cv.type], [cv.name])
  | .quotDecl _ cv => ([cv.type], [cv.name])
  | .basisDecl _ => ([], [])
  | .indDecl block _ => (block.map (·.toConstantVal.type), block.map (·.name))

/-- Record `k`'s dependencies: the earlier records installing the names
it looks up, ascending, without repeats — leaving out, for a record past
the GATE (the last record installing a basis name, `basisGate`), every
record at or below it: the cursor reaches those first, and a worker that
needs one of their slots before it is published waits on its promise.
Without that rule every record would be a dependent of the dozen basis
records, a hub whose dependents' lists the assembly would build
serially.  A record at or below the gate keeps its edges, so the
prelude is installed in its dependency order, on the workers.  (The
workers' cursor once started past the gate, leaving the prelude to the
commit thread alone: a serial ~0.5 s at the start of the install,
task #329's `ifix2` lane, DESIGN.md.) -/
def recDeps (B : BaseIdx) (gate k : Nat) (pd : Declaration) : Array Nat :=
  let (es, own) := declExprs pd
  let names := (es.foldl (fun acc e => depNames e acc)
    ({}, basisDepNames ++ own.toArray)).2
  let ks := names.filterMap fun n => match baseGet? B n with
    | some (_, k', _) => if k' < k && (k ≤ gate || gate < k') then some k' else none
    | none => none
  let ks := ks.qsort (· < ·)
  ks.foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

/-- The gate: the last record installing a basis name. -/
def basisGate (B : BaseIdx) : Nat :=
  basisDepNames.foldl (fun g n => match baseGet? B n with
    | some (_, k, _) => max g k
    | none => g) 0

/-- The chunks a parallel prelude step splits the records into:
`(lo, hi)` for each of `parts` contiguous ranges. -/
def chunkBounds (n parts : Nat) : Array (Nat × Nat) :=
  let chunk := (n + parts - 1) / parts
  (Array.range parts).map fun t => (min n (t * chunk), min n (t * chunk + chunk))

/-- The chunk containing record `d`, for `chunkBounds n parts`. -/
@[inline] def chunkOf (n parts d : Nat) : Nat := d / ((n + parts - 1) / parts)

/-- Records `lo .. hi - 1`'s part of the schedule, on a task of its own:
each record's dependency count (one IO reference each, starting at its
number of dependencies plus the cursor's token), its state (`RState`), and
its dependency edges grouped by dependency — `(d, the records of this
chunk depending on d, ascending)` — and bucketed by the chunk `d` lies
in (`chunkOf`), marked persistent.  Grouping here is what keeps the dependents' assembly
balanced: a hub every record depends on (the basis) arrives as one
group per chunk, appended in one copy, not as one push per record. -/
def depsChunk {α : Type} (B : BaseIdx) (ds : Array Declaration) (noMark : Bool)
    (gate n parts lo hi : Nat) :
    IO (Array (IO.Ref Nat) × Array (IO.Ref (RState α)) × Array (Array (Nat × Array Nat))) := do
  let mut counts := Array.mkEmpty (hi - lo)
  let mut state := Array.mkEmpty (hi - lo)
  let mut pos : Std.HashMap Nat Nat := {}
  let mut grps : Array (Nat × Array Nat) := #[]
  for k in [lo:hi] do
    let dk := match ds[k]? with
      | some pd => recDeps B gate k pd
      | none => #[]
    counts := counts.push (← IO.mkRef (dk.size + 1))
    state := state.push (← IO.mkRef RState.free)
    for d in dk do
      match pos[d]? with
      | some i => grps := grps.modify i fun (d', ks) => (d', ks.push k)
      | none =>
        pos := pos.insert d grps.size
        grps := grps.push (d, #[k])
  let mut edges : Array (Array (Nat × Array Nat)) := Array.replicate parts #[]
  for g in grps do
    edges := edges.modify (chunkOf n parts g.1) (·.push g)
  -- persistent (unless `noMark`), although all three die with the
  -- install (`counts` and `state` with the workers, `edges` once the
  -- dependents are assembled): freeing them instead — on background
  -- tasks, multi-threaded until then — cost the check phase on
  -- mathlib-full ~3 % of its wall time at `--jobs=8` (more busy time at
  -- the same instructions: the freed memory, interleaved with what
  -- survives, is what the check workers then allocate from), for
  -- ~350 MB of peak resident set (task #329's `ifix` lane, DESIGN.md).
  -- `counts` and `state` are WRITTEN by every worker; a persistent ref
  -- is written through the runtime's atomic path like a multi-threaded
  -- one, and what is stored is a scalar or (`RState.done`) a fresh
  -- wrapper around an already persistent install result.  `noMark`
  -- keeps the multi-threaded mark (the A/B).
  if noMark then
    Runtime.markMultiThreaded (counts, state, edges)
  else
    unsafe Runtime.markPersistent (counts, state, edges)

/-- One thread of the dependency step: claim fine chunks off `next` and
run `depsChunk` on each, returning the results with their chunk
numbers. -/
partial def depsWorker {α : Type} (B : BaseIdx) (ds : Array Declaration) (noMark : Bool)
    (gate n parts : Nat) (fine : Array (Nat × Nat)) (next : IO.Ref Nat)
    (acc : Array (Nat × (Array (IO.Ref Nat) × Array (IO.Ref (RState α)) ×
      Array (Array (Nat × Array Nat))))) :
    IO (Array (Nat × (Array (IO.Ref Nat) × Array (IO.Ref (RState α)) ×
      Array (Array (Nat × Array Nat))))) := do
  let c ← next.modifyGet fun c => (c, c + 1)
  match fine[c]? with
  | some (lo, hi) =>
    let r ← depsChunk B ds noMark gate n parts lo hi
    depsWorker B ds noMark gate n parts fine next (acc.push (c, r))
  | none => return acc

/-- The dependents of records `lo .. hi - 1` (chunk `r`), on a task of
its own: the groups into the chunk from every source chunk, in chunk
order, so each record's dependents are ascending.  Marked multi-threaded
here, on its own task: `chunks.size` of these tasks resolve together,
each one a non-scalar array, so marking it off the lock keeps the
runtime's automatic mark at resolution (`resolve_core`, under its one
global mutex) a no-op instead of a contended walk; the combined
`dependents` is marked persistent once, in `parInstall`. -/
def dependentsChunk (edges : Array (Array (Array (Nat × Array Nat))))
    (r lo hi : Nat) : IO (Array (Array Nat)) := do
  let mut acc : Array (Array Nat) := Array.replicate (hi - lo) #[]
  for t in [0:edges.size] do
    if let some es := edges[t]? then
      if let some e := es[r]? then
        for (d, ks) in e do
          acc := acc.modify (d - lo) (· ++ ks)
  Runtime.markMultiThreaded acc

/-- The slots of records `lo .. hi - 1`, on a task of its own: one
promise each, and the thunk over it a view reads.  (Not marked
persistent: marking waits for every task it reaches, and a promise's
task is unresolved here.) -/
def slotChunk (lo hi : Nat) :
    IO (Array (IO.Promise (Array ConstantInfo)) × Slots) := do
  let mut ps := Array.mkEmpty (hi - lo)
  let mut ss : Slots := Array.mkEmpty (hi - lo)
  for _ in [lo:hi] do
    let p ← IO.Promise.new
    ps := ps.push p
    ss := ss.push (Thunk.mk fun _ => (p.result?.get).getD #[])
  Runtime.markMultiThreaded (ps, ss)

/-- The prediction of records `lo .. hi - 1`, on a task of its own: each
record's slot count, the chunk's slots `(name, record, position)` in
counter order, and the chunk-relative counters of its slots bucketed by
base shard (`baseShard`). -/
def predictChunk (ds : Array Declaration) (nShards lo hi : Nat) :
    Array Nat × Array (Name × Nat × Nat) × Array (Array Nat) := Id.run do
  let mut sizes := Array.mkEmpty (hi - lo)
  let mut slots := #[]
  let mut buckets : Array (Array Nat) := Array.replicate nShards #[]
  for k in [lo:hi] do
    let names := match ds[k]? with
      | some pd => predictSlots pd
      | none => #[]
    sizes := sizes.push names.size
    for h : j in [0:names.size] do
      let nm := names[j]
      buckets := buckets.modify (baseShard nm nShards) (·.push slots.size)
      slots := slots.push (nm, k, j)
  return (sizes, slots, buckets)

/-- The scheduler.  Workers walk the records in order off a shared
`cursor`, one atomic claim per block of `cursorBlockSize` records (no
lock), each worker working through its block in stream order.  Record
`k`'s count starts at its number of dependencies PLUS ONE, the extra
token being the cursor's pass.  Whoever brings a count to zero — the cursor's pass if
every dependency is already installed, else the release of the last one
— has the record ready.  A record that becomes ready by a release (it
was passed while blocked) and that its releaser does not install next
goes to the `deferred` set (a tree under `lock`, lowest first;
`deferredN` is its size, read without the lock), which a worker drains
before advancing in its block, so stream order is preferred. `taken` is
a per-record test-and-set: the commit thread may install a record
itself, and whoever loses the race skips it.  The lock and the condition
variable are touched only for deferred records and by workers idle at
the end of the stream.  (A first scheduler kept EVERY ready record in
the tree under the lock: at 32 workers the workers spent ~60 % of the
install blocked in `mutex::lock`.) -/
structure Sched where
  counts : Array (IO.Ref Nat)
  dependents : Array (Array Nat)
  cursor : IO.Ref Nat
  deferred : IO.Ref (Std.TreeSet Nat compare)
  deferredN : IO.Ref Nat
  stop : IO.Ref Bool
  lock : Std.BaseMutex
  cv : Std.Condvar

/-- Drop record `d`'s count by one; `true` if it reached zero. -/
@[inline] def decCount (sc : Sched) (d : Nat) : IO Bool := do
  match sc.counts[d]? with
  | some r =>
    let c ← r.modifyGet fun c => (c - 1, c - 1)
    return c == 0
  | none => return false


/-- Record `k` installed: its dependents' counts drop.  Those that reach
zero were passed by the cursor while blocked: the lowest is returned
for the caller to install next, the others are deferred. -/
def release (sc : Sched) (k : Nat) : IO (Option Nat) := do
  match sc.dependents[k]? with
  | none => return none
  | some deps =>
    let mut newly : Array Nat := #[]
    for d in deps do
      if ← decCount sc d then newly := newly.push d
    match newly[0]? with
    | none => return none
    | some first =>
      if newly.size > 1 then
        let rest := newly.extract 1 newly.size
        sc.lock.lock
        sc.deferred.modify fun t => rest.foldl (fun t d => t.insert d) t
        sc.deferredN.modify (· + rest.size)
        sc.lock.unlock
        for _ in rest do
          sc.cv.notifyOne
      return some first

/-- The lowest deferred record, if any (takes the lock only when the
set looks non-empty). -/
def popDeferred (sc : Sched) : IO (Option Nat) := do
  if (← sc.deferredN.get) == 0 then return none
  sc.lock.lock
  let k? ← sc.deferred.modifyGet fun t => match t.min? with
    | some k => (some k, t.erase k)
    | none => (none, t)
  if k?.isSome then sc.deferredN.modify (· - 1)
  sc.lock.unlock
  return k?

/-- Records per cursor claim: a performance parameter (a grain size),
not an assumption about the input; no verdict depends on it.  Its
measurement: claiming one record at a time made the install at
`--jobs=4` and `8` slower than claiming 64 at the same instructions
(task #329's `ifix` lane, DESIGN.md: NS and cslib at 4 jobs +0.2–0.6 s
of a 5–8 s install, mathlib-full at 8 jobs 10.85 against 9.9 s), and
no sharper knee was found (task #329's `mtclean` lane).  Why is a
HYPOTHESIS, not measured: neighbouring records' per-record objects
(counters, states, slots) share cache lines, which with one record per
claim alternate between workers. -/
def cursorBlockSize : Nat := 64

/-- The next ready record for a worker, or `none` once stopped: a
deferred one, else the next record of the worker's own block, claiming
a fresh block of `cursorBlockSize` records off the cursor when it is
used up, if it is ready (a record that is not stays with its
dependencies' releases); at the end of the stream, wait for a deferred
record or the stop.  `lo hi` is the worker's claimed-but-not-yet-tried
block (`lo = hi` when empty): worker-local, threaded back to the
caller. -/
partial def nextReady (sc : Sched) (n : Nat) (lo hi : Nat) :
    IO (Option Nat × Nat × Nat) := do
  if ← sc.stop.get then return (none, lo, hi)
  if let some d ← popDeferred sc then return (some d, lo, hi)
  let (k, lo, hi) ← if lo < hi then pure (lo, lo + 1, hi) else
    let lo' ← sc.cursor.modifyGet fun c => (c, min n (c + cursorBlockSize))
    pure (lo', lo' + 1, min n (lo' + cursorBlockSize))
  if k < n then
    if ← decCount sc k then return (some k, lo, hi)
    else nextReady sc n lo hi
  else
    sc.lock.lock
    if !(← sc.stop.get) && (← sc.deferredN.get) == 0 then
      sc.cv.wait sc.lock
    sc.lock.unlock
    nextReady sc n lo hi

variable {mode : CheckMode} {ds : Array Declaration} {B : BaseIdx} {S : Slots}
  {vis : Array Nat}

/-- The state the commit thread and the workers share. -/
structure Shared (mode : CheckMode) (ds : Array Declaration) (B : BaseIdx) (S : Slots)
    (vis : Array Nat) where
  /-- record `k`'s published constants (`S` reads them): the one
  promise per record, so that a lookup (pure code) can wait on it -/
  slotP : Array (IO.Promise (Array ConstantInfo))
  /-- record `k`'s state, with its install result once done -/
  state : Array (IO.Ref (RState (WRes mode ds B S vis)))
  sched : Sched
  noMark : Bool
  /-- `k + 1` while the commit thread sleeps waiting for record `k`,
  else `0` -/
  commitWait : IO.Ref Nat
  commitLock : Std.BaseMutex
  commitCv : Std.Condvar
  /-- the commit thread's own installs, timed (performance-only) -/
  selfStats : IO.Ref WStats
  /-- on the heartbeat lane, the record each worker is on (worker `w`
  at `w`, the commit thread last); empty otherwise -/
  live : Live

/-- Claim record `k` for installing: `true` for exactly one caller. -/
@[inline] def tryTake (sh : Shared mode ds B S vis) (k : Nat) : IO Bool := do
  match sh.state[k]? with
  | some r => r.modifyGet fun
    | .free => (true, .taken)
    | s => (false, s)
  | none => return false

/-- Install record `k` at its view and publish the result: marked
persistent first (unless `--no-mark-persistent`), then the slot (workers
may wait on it), the commit's checks (`goodB`), the result in the
record's state (waking the commit thread if it waits for it), and the dependents
released (the lowest newly ready dependent is returned, for the
caller to install next). -/
def installAndPublish (sh : Shared mode ds B S vis) (k : Nat) :
    IO (WRes mode ds B S vis × Option Nat) := do
  let r := workerRes mode ds B S vis k
  let cs := slotOfRes r
  if !sh.noMark then
    -- The result is marked persistent although other threads may read it
    -- concurrently later (the slot's readers, the commit thread).  That is
    -- safe only while an install result reaches no object that is
    -- ALREADY multi-threaded and that another thread is still counting:
    -- the mark would turn such an object persistent (`lean_mark_persistent`
    -- does not skip a multi-threaded object) while other threads still
    -- decrement its count — a data race.  Today a result reaches only
    -- objects that are persistent already (the records, earlier results)
    -- or fresh ones of its own.  If a slot, a slot thunk, a promise or an
    -- `FEnv` (whose base layer holds the slots) ever ends up inside a
    -- `ConstantInfo` or a `ValueGroup`, this mark must go.
    let _ ← unsafe Runtime.markPersistent r
    let _ ← unsafe Runtime.markPersistent cs
  match sh.slotP[k]? with
  | some p => p.resolve cs
  | none => pure ()
  -- the commit's checks, here: the slot is resolved, its thunk reads it
  let good := goodB ds B S vis k r
  let q : WRes mode ds B S vis := ⟨(k, r, good), rfl, goodB_spec⟩
  match sh.state[k]? with
  | some st => st.set (.done q)
  | none => pure ()
  -- The handshake with `waitDone`: each side STORES (here the state,
  -- there `commitWait`) and then LOADS the other's.  `IO.Ref`'s get and
  -- set are sequentially consistent atomic exchanges (the runtime's
  -- `lean_st_ref_get`/`_set` on a shared ref), so the two stores are
  -- ordered and at least one side sees the other's: either the commit
  -- thread sees `.done` and does not sleep, or this thread sees
  -- `commitWait = k + 1` and signals.  The empty lock/unlock orders the
  -- signal after the commit thread's own check under the lock, so the
  -- signal cannot fall between that check and its `wait`.
  if (← sh.commitWait.get) == k + 1 then
    sh.commitLock.lock
    sh.commitLock.unlock
    sh.commitCv.notifyOne
  let next ← release sh.sched k
  pure (q, next)

/-- Hand a ready record to the workers (the commit thread does not
install the records its own installs make ready). -/
def deferRecord (sc : Sched) (k : Nat) : IO Unit := do
  sc.lock.lock
  sc.deferred.modify (·.insert k)
  sc.deferredN.modify (· + 1)
  sc.lock.unlock
  sc.cv.notifyOne

/-- Install and publish record `k` as worker `w`, timed into `st`
(performance-only; on the heartbeat lane the worker also publishes the
record it is on). -/
@[inline] def installTimed (sh : Shared mode ds B S vis) (w k : Nat) (st : WStats) :
    IO (WRes mode ds B S vis × Option Nat × WStats) := do
  let ts ← IO.monoNanosNow
  let lv := sh.live.cur.size > 0
  if lv then sh.live.begin w k ts
  let (q, next) ← installAndPublish sh k
  let te ← IO.monoNanosNow
  if lv then sh.live.idle w
  return (q, next, st.add k ts te)

/-- One worker (number `w`): install the record its last install made
ready, else the next ready one, repeat until stopped; returns its
timing.  `lo hi` is its claimed block (`nextReady`). -/
partial def workerLoop (sh : Shared mode ds B S vis) (w : Nat) (st : WStats)
    (cont : Option Nat) (lo hi : Nat) : IO WStats := do
  let (k?, lo, hi) ← match cont with
    | some k => pure (some k, lo, hi)
    | none => nextReady sh.sched ds.size lo hi
  match k? with
  | none => return st
  | some k =>
    if ← tryTake sh k then
      let (_, next, st) ← installTimed sh w k st
      workerLoop sh w st next lo hi
    else
      workerLoop sh w st none lo hi

/-- Stop the workers: no new records, and — when the run was abandoned
(`resolveAll`) — every slot not resolved yet resolved empty, so that
nobody stays waiting on it.  After a complete commit every slot is
resolved already, and the walk over a million cold promises is skipped. -/
def stopWorkers (sh : Shared mode ds B S vis) (resolveAll : Bool) : IO Unit := do
  sh.sched.stop.set true
  sh.sched.lock.lock
  sh.sched.lock.unlock
  sh.sched.cv.notifyAll
  if resolveAll then
    for p in sh.slotP do
      p.resolve #[]

/-- Record `k`'s install result, if it is done (one read of its state). -/
@[inline] def peekDone (sh : Shared mode ds B S vis) (k : Nat) :
    IO (Option (WRes mode ds B S vis)) := do
  match sh.state[k]? with
  | some st =>
    if let .done q ← st.get then return some q
    return none
  | none => return none

/-- The commit thread's wait for record `k`, taken by an installer: the
result once the record is done.  If it is not done yet, the thread
SLEEPS on its own condition variable (`Shared.commitWait` tells the
installer to signal it) — never spins, and never waits on the runtime's
task manager.  `cst[0]`/`cst[1]` count the sleeps and their time. -/
partial def waitDone (sh : Shared mode ds B S vis) (cst : IO.Ref (Array Nat)) (k : Nat) :
    IO (Option (WRes mode ds B S vis)) := do
  match sh.state[k]? with
  | none => return none
  | some st =>
    if let .done q ← st.get then return some q
    let t0 ← IO.monoNanosNow
    sh.commitWait.set (k + 1)
    sh.commitLock.lock
    let rec sleep : IO (WRes mode ds B S vis) := do
      if let .done q ← st.get then return q
      sh.commitCv.wait sh.commitLock
      sleep
    let q ← sleep
    sh.commitLock.unlock
    sh.commitWait.set 0
    let t1 ← IO.monoNanosNow
    cst.modify fun a => (a.modify 0 (· + 1)).modify 1 (· + (t1 - t0))
    return some q

/-- The internal error of a misprediction (exit 3): no input reaches it
(every accepting step installs the predicted skeleton,
`annotStepC_skels`), so it is reported, not recovered from. -/
def mispredicted (k i : Nat) (what : String) : Except (CheckError × Nat) α :=
  .error (.internal s!"parallel install: {what} at record {k}", i)

/-- **The commit loop.**  `installLoop`'s run, one record per step, each
record's step added from its install at its view: the commit thread
pushes the installer's constants into the serial index `fe` (whose
counter is `c`) itself.  `cst` counts the commit thread's sleeps
waiting for an installer and its own installs, with their times.

Written tail-recursively with `fe` and `pend` as plain arguments, as
`installLoop` is: nothing else holds the index, so every push is in
place (the index is marked linear, and a copy would panic). -/
def commitLoop (err : IO.FS.Stream) (stride total t0 : Nat)
    (hB : BaseInj B) (sh : Shared mode ds B S vis) (cst : IO.Ref (Array Nat))
    (p₀ : Nat × FEnv × Array PendingCheck) :
    (k i c : Nat) → (fe : FEnv) → (pend : Array PendingCheck) →
    fe.visibleBelow = c →
    InstallRun mode natOpPinSets (ds.toList.take k) p₀ (i, fe, pend) →
    IdxBelow fe → ViewAgrees B S fe →
      IO (Except (CheckError × Nat)
        (Σ' (p' : Nat × FEnv × Array PendingCheck),
          PLift (InstallRun mode natOpPinSets ds.toList p₀ p')))
  | k, i, c, fe, pend, hc, hrun, hidx, hag => do
    if hk : k < ds.size then
      let pd := ds[k]
      have hlist : ds.toList.take (k + 1) = ds.toList.take k ++ [pd] := by
        rw [List.take_add_one]
        simp [pd, Array.getElem?_eq_getElem hk]
      if stride > 0 && i % stride == 0 then
        let now ← IO.monoMsNow
        let extra ← sh.live.report fun j =>
          match ds[j]? with
          | some d => s!"{ConLeche.Cached.declCLabel d} (#{j})"
          | none => s!"record {j}"
        err.putStr s!"con-leche: install {i}/{total} \
          {ConLeche.Cached.declCLabel pd} \
          t={ConLeche.Cached.msSecs (now - t0)}s{extra}\n"
        err.flush
      if hv : vis[k]? = some c then
        -- the record's install: the installer's if it is done (read
        -- first: the common case, and no claim attempt then), here if
        -- nobody took it, else the installer's, slept for (never spun)
        let q? : Option (WRes mode ds B S vis) ← do
          if let some q ← peekDone sh k then pure (some q)
          else if ← tryTake sh k then
            let tf0 ← IO.monoNanosNow
            let (q, next, st) ← installTimed sh (sh.live.cur.size - 1) k (← sh.selfStats.get)
            sh.selfStats.set st
            if let some d := next then deferRecord sh.sched d
            let tf1 ← IO.monoNanosNow
            cst.modify fun a => (a.modify 2 (· + 1)).modify 3 (· + (tf1 - tf0))
            pure (some q)
          else waitDone sh cst k
        match q? with
        | none => return mispredicted k i "no install result"
        | some ⟨(k', r, good), hr, hg⟩ =>
          if hk' : k' = k then
            if hgood : good = true then
              have hG : GoodAt ds B S vis k r := hk' ▸ hg hgood
              have hG' := hG pd c (Array.getElem?_eq_getElem hk) hv
              have hval : r = installStep mode natOpPinSets (workerView B S fe.visibleBelow) pd := by
                have hr' : r = workerRes mode ds B S vis k := hk' ▸ hr
                rw [hr', hc]
                simp only [workerRes, Array.getElem?_eq_getElem hk, hv, pd]
              match hres : r with
              | .ok (L, vg?) =>
                have hstep0 := installStep_commit (pins := natOpPinSets) (i := i) (pend := pend)
                  hag hidx hG'.1 (hval.symm.trans hres)
                have hstep : annotDeclStep mode natOpPinSets (i, fe, pend) pd =
                    .ok (i + 1, FEnv.pushAll L fe, pushPending pend i c vg?) := by
                  rw [← hc]; exact hstep0
                commitLoop err stride total t0 hB sh cst p₀ (k + 1)
                  (i + 1) (c + L.length) (FEnv.pushAll L fe) (pushPending pend i c vg?)
                  (by rw [pushAll_visibleBelow, hc])
                  (by rw [hlist]; exact InstallRun.snoc mode hrun hstep)
                  (hidx.pushAll L)
                  (ViewAgrees.pushAll hB L hidx hag (hc ▸ hG'.2 L vg? hres))
              | .error e =>
                -- the serial step's error at this record, checked here
                -- (the return type carries no proof for a rejection)
                have _ : annotDeclStep mode natOpPinSets (i, fe, pend) pd = .error (e, i) := by
                  exact installStep_commit_error hag hidx hG'.1 (hval.symm.trans hres)
                return .error (e, i)
            else if andPinOk pd then
              return mispredicted k i "a predicted slot did not match"
            else
              -- a failed `And` pin: the serial step rejects the record
              -- before installing anything; its error is the verdict
              match annotDeclStep mode natOpPinSets (i, fe, pend) pd with
              | .error e => return .error e
              | .ok _ => return mispredicted k i "the `And` pin"
          else return mispredicted k i "a mismatched install result"
      else return mispredicted k i "a predicted counter did not match"
    else
      return .ok ⟨(i, fe, pend), ⟨by
        rw [List.take_of_length_le (by simp; omega)] at hrun
        exact hrun⟩⟩
  termination_by k => ds.size - k

end ParInstall

/-- **Phase A on `jobs` worker threads** (the section above): the
prediction, the base index, the slots, the dependencies and the
workers, the commit loop; at the end the workers are stopped, also when
the commit loop throws.  Its result is `installLoop`'s.  Its timing
report (performance-only) is left in `rep`: an action that collects the
statistics of the workers that have returned when it runs, waiting for
none.  The join of the stopped workers is left in `drain`, which the
CLI runs after the verdict line is out and before the process exits
(`Main.lean`'s `main`). -/
def parInstall (mode : CheckMode) (err : IO.FS.Stream) (stride total t0 jobs : Nat)
    (noMark : Bool) (rep : IO.Ref (IO (Option PoolRep))) (drain : IO.Ref (IO Unit))
    (ds : Array Declaration) :
    IO (Except (CheckError × Nat)
      (Σ' (p' : Nat × FEnv × Array Cached.PendingCheck),
        PLift (Cached.InstallRun mode natOpPinSets ds.toList
          (0, mkFEnv Env.empty, #[]) p'))) := do
  let tA ← IO.monoMsNow
  let n := ds.size
  let parts := max 1 jobs
  let chunks := ParInstall.chunkBounds n parts
  -- the records are read by every task below and live to the end of the
  -- run: persistent first, so that no task spawn walks them for
  -- multi-threaded marking
  if !noMark then
    let _ ← unsafe Runtime.markPersistent ds
  let tA0 ← IO.monoMsNow
  -- the prediction, chunk per task; then the counters (prefix sums).
  -- Marked multi-threaded (task #329's `mtclean` audit: kept, not
  -- persistent) because its `cs` component (`buckets`, and the `slots`
  -- it is concatenated with below) is handed to EVERY shard-building
  -- task afterwards — real concurrent reads, not a single join — and is
  -- then dropped once the shards are built; persistent would leak the
  -- names and the arrays for the rest of the run instead of freeing
  -- them.  (Every task below marks its own result itself before it
  -- returns: the runtime marks a task's result anyway while it holds its
  -- one global lock when the task resolves, and a result already marked
  -- costs that walk nothing.)
  let mut predTasks := #[]
  for (lo, hi) in chunks do
    -- (`IO.lazyPure`: a pure argument would be evaluated where the
    -- action is built, on this thread)
    predTasks := predTasks.push (← IO.asTask (prio := .dedicated) do
      let r ← IO.lazyPure fun _ => ParInstall.predictChunk ds parts lo hi
      Runtime.markMultiThreaded r)
  let mut preds := Array.mkEmpty parts
  for t in predTasks do
    preds := preds.push (← IO.ofExcept (← IO.wait t))
  let mut vis : Array Nat := Array.mkEmpty n
  let mut offs : Array Nat := Array.mkEmpty parts
  let mut slots : Array (Name × Nat × Nat) := #[]
  for (sizes, cs, _) in preds do
    offs := offs.push slots.size
    let mut c := slots.size
    for sz in sizes do
      vis := vis.push c
      c := c + sz
    slots := slots ++ cs
  let buckets := preds.map (·.2.2)
  -- the base, shard per task
  let mut shardTasks := #[]
  for s in [0:parts] do
    shardTasks := shardTasks.push (← IO.asTask (prio := .dedicated) do
      let r ← IO.lazyPure fun _ =>
        (⟨Cached.buildShard slots offs buckets s, s, rfl⟩ : Cached.BuiltShard slots offs buckets)
      -- persistent here, on the shard's own thread, although the base
      -- dies with the install.  Every base hit returns an entry of a
      -- shard (`baseGet?`) with a reference count taken on it, from every
      -- worker at once on the hot names; multi-threaded, those are atomic
      -- increments on shared cache lines, and that made the dependency
      -- walk and the pool measurably slower (task #329's `ifix` lane,
      -- DESIGN.md).  Multi-threaded under `noMark`.  The mark reaches
      -- multi-threaded objects of the prediction (the projection tables'
      -- names `predictChunk` built, also held by `slots`); safe, because
      -- no other running thread counts them: their tasks have finished,
      -- the main thread is waiting here, and the other shard tasks touch
      -- only the names of their own shards.
      if noMark then Runtime.markMultiThreaded r
      else unsafe Runtime.markPersistent r)
  let mut shards : Array (Cached.BuiltShard slots offs buckets) := Array.mkEmpty parts
  for t in shardTasks do
    shards := shards.push (← IO.ofExcept (← IO.wait t))
  let B : Cached.BaseIdx := shards.map (·.1)
  -- (`B.size` forces the prediction and the base before the clock is read)
  let tA' ← if B.size + vis.size == 0 then IO.monoMsNow else IO.monoMsNow
  let tB ← IO.monoMsNow
  let gate := ParInstall.basisGate B
  -- the slots, chunk per task: record `k`'s constants, as whoever
  -- installs it resolves them.  A slot is a thunk over its promise: the
  -- first lookup waits for the publisher, every later one reads the
  -- thunk's (persistent) value with no reference count on any shared
  -- object.
  let mut slotTasks := #[]
  for (lo, hi) in chunks do
    slotTasks := slotTasks.push (← IO.asTask (prio := .dedicated) (ParInstall.slotChunk lo hi))
  let mut slotP : Array (IO.Promise (Array ConstantInfo)) := Array.mkEmpty n
  let mut S : Cached.Slots := Array.mkEmpty n
  for t in slotTasks do
    let (ps, ss) ← IO.ofExcept (← IO.wait t)
    slotP := slotP ++ ps
    S := S ++ ss
  let tC0 ← IO.monoMsNow
  -- the dependencies, counts and states, chunk per task; then the
  -- dependents, chunk per task
  -- (the dependency walk's cost is uneven along the stream, so the
  -- records are cut finer than the threads, and `parts` threads claim
  -- the fine chunks off a counter)
  let fine := ParInstall.chunkBounds n (8 * parts)
  let nextFine ← IO.mkRef 0
  let mut depTasks := #[]
  for _ in [0:parts] do
    depTasks := depTasks.push (← IO.asTask (prio := .dedicated)
      (ParInstall.depsWorker (α := ParInstall.WRes mode ds B S vis) B ds noMark gate n parts
        fine nextFine #[]))
  let mut fineRes : Array (Option (Array (IO.Ref Nat) ×
      Array (IO.Ref (ParInstall.RState (ParInstall.WRes mode ds B S vis))) ×
      Array (Array (Nat × Array Nat)))) := Array.replicate fine.size none
  for t in depTasks do
    for (c, r) in ← IO.ofExcept (← IO.wait t) do
      fineRes := fineRes.set! c (some r)
  let mut counts : Array (IO.Ref Nat) := Array.mkEmpty n
  let mut state : Array (IO.Ref (ParInstall.RState (ParInstall.WRes mode ds B S vis))) :=
    Array.mkEmpty n
  let mut edges : Array (Array (Array (Nat × Array Nat))) := Array.mkEmpty fine.size
  for r? in fineRes do
    if let some (c, st, e) := r? then
      counts := counts ++ c
      state := state ++ st
      edges := edges.push e
  let tC ← IO.monoMsNow
  let mut depdTasks := #[]
  for h : r in [0:chunks.size] do
    let (lo, hi) := chunks[r]
    depdTasks := depdTasks.push
      (← IO.asTask (prio := .dedicated) (ParInstall.dependentsChunk edges r lo hi))
  let mut dependents : Array (Array Nat) := Array.mkEmpty n
  for t in depdTasks do
    dependents := dependents ++ (← IO.ofExcept (← IO.wait t))
  -- persistent, like the schedule's counts and states (`depsChunk`): it
  -- dies with the install, but freeing it costs the check phase more
  -- than it saves.  The mark reaches the inner arrays `dependentsChunk`
  -- marked multi-threaded; safe, because their tasks have finished and
  -- only this thread holds them now.
  if !noMark then
    let _ ← unsafe Runtime.markPersistent dependents
  let sched : ParInstall.Sched :=
    { counts, dependents, cursor := ← IO.mkRef 0,
      deferred := ← IO.mkRef ∅, deferredN := ← IO.mkRef 0,
      stop := ← IO.mkRef false, lock := ← Std.BaseMutex.new, cv := ← Std.Condvar.new }
  let selfStats ← IO.mkRef ({} : WStats)
  let sh : ParInstall.Shared mode ds B S vis :=
    { slotP, state, sched, noMark, commitWait := ← IO.mkRef 0,
      commitLock := ← Std.BaseMutex.new, commitCv := ← Std.Condvar.new,
      selfStats, live := ← Live.new (if stride > 0 then jobs + 1 else 0) }
  let tD ← IO.monoMsNow
  let tStart ← IO.monoNanosNow
  let mut tasks := #[]
  for w in [0:jobs] do
    tasks := tasks.push
      (← IO.asTask (prio := .dedicated) (ParInstall.workerLoop sh w {} none 0 0))
  -- the join of the workers, for the process's exit (see the end)
  drain.set do
    for t in tasks do
      let _ ← IO.wait t
  let cst ← IO.mkRef (Array.replicate 4 0)
  -- the serial index, marked linear (task #331) as on the serial path
  -- (`Driver/Run.lean`): the commit thread is its only holder, so a copy
  -- of it panics instead of silently copying the bucket array.  Marked
  -- here, on the value the loop threads, not on the closed term
  -- `mkFEnv Env.empty`, which is persistent and copied by its first
  -- insert anyway.
  -- An IO exception on this thread (a failing heartbeat write) must not
  -- leave the workers running: one past the end of the stream would sleep
  -- on the scheduler's condition variable forever, one inside an install
  -- on an unresolved slot, and the exit waits for them (`drain`).  So
  -- they are stopped, every slot resolved, and the exception rethrown.
  let res ← try
      ParInstall.commitLoop err stride total t0
        (Cached.buildBase_inj shards) sh cst (0, mkFEnv Env.empty, #[])
        0 0 0 (mkFEnv Env.empty).markLinear #[] rfl
        (FEnv.markLinear_eq _ ▸ .nil _)
        (FEnv.markLinear_eq _ ▸ Cached.IdxBelow.mkFEnv_empty)
        (FEnv.markLinear_eq _ ▸ Cached.ViewAgrees.empty B S)
    catch ex =>
      ParInstall.stopWorkers sh true
      throw ex
  let tEnd ← IO.monoNanosNow
  let tE ← IO.monoMsNow
  -- the timing report, collected when the summary is printed, from the
  -- workers that have finished by then.  It waits for none: after a
  -- rejection the summary is printed before the verdict, right after the
  -- commit, while a worker may still be inside an install past the
  -- rejected record (one the serial run never starts, and as long as the
  -- input makes it); a worker still running is left out of the report and
  -- counted in its title, and the exit waits for it (`drain`).  (After an
  -- accept the summary follows the check phase, and every worker has long
  -- returned.)
  rep.set do
    let mut stats := #[]
    let mut running := 0
    for t in tasks do
      if ← IO.hasFinished t then
        if let .ok st ← IO.wait t then stats := stats.push st
      else running := running + 1
    stats := stats.push (← selfStats.get)
    let name := if running == 0 then "install pool"
      else s!"install pool ({running} still running, not counted)"
    let r : PoolRep := { name, workers := jobs,
                         helper := some "the commit thread", tStart, tEnd, stats }
    return some r
  -- (after a rejection the records past it may never be installed, and
  -- a worker may be waiting on one of their slots)
  ParInstall.stopWorkers sh (res matches .error _)
  -- the workers are not joined here: once stopped they only exit, and
  -- a thread's exit (its allocator's teardown) took ~0.25 s on cslib —
  -- nothing after the commit needs them, and the statistics (`rep`,
  -- above) count only the finished ones.  After a rejection a worker may
  -- still be inside an install of a record past it; the verdict is
  -- printed without it, and then, before the process ends with
  -- `IO.Process.exit`, `main` waits for every worker (`drain`, set
  -- above; maintainer's ruling, 2026-10-10): `exit()` runs the C
  -- runtime's teardown, which must not meet a thread still inside an
  -- install.  The rejection path need not be fast; after an accept every
  -- worker has long returned and the wait is immediate.  That a stopped
  -- worker does end rests on two facts no type enforces: an installer
  -- never throws between `tryTake` and resolving its slot (it runs only
  -- reference, clock, promise, mutex and condition-variable operations,
  -- none of which throws), and a lookup waits only on a lower record
  -- (every unresolved slot is resolved empty above).
  let tF ← IO.monoMsNow
  if stride > 0 then
    let c ← cst.get
    err.putStr s!"con-leche: parallel install: records marked persistent {tA0 - tA} ms, prediction+base {tA' - tA0} ms, \
      gate {gate}, slots {tC0 - tB} ms, dependencies {tC - tC0} ms, dependents {tD - tC} ms, commit {tE - tD} ms, stop {tF - tE} ms (t={tF - t0} ms); \
      commit thread: {c[0]!} sleeps on a worker \
      ({c[1]! / 1000000} ms), {c[2]!} records installed itself ({c[3]! / 1000000} ms)\n"
    err.flush
  return res

end ConLeche.Driver
