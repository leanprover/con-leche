module

public import ConLeche.Verify.Cached.ViewCongr
public import ConLeche.Cached.InstallSkel
public import Std.Sync.Mutex
import Std.Data.TreeSet.Basic
import Std.Data.HashSet.Basic

/-!
# Phase A: the serial loop and the parallel install (task #329)

Phase A's loops, pulled out of `Main.lean` when the driver split into
`ConLeche/Driver/*` (the CLI stays in `Main.lean`; the proof-carrying
driver moved here, to `Driver/CheckPool.lean`, `Driver/ParInstall.lean`
and `Driver/Run.lean`).  A pure move: no logic changed, only the
module boundary.

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
order, pushes each record's constants into the serial index, and
extends the serial fold's accepting run by one step per record, exactly
as `installLoop` does.  What it returns is therefore `installLoop`'s
type — phase A of the fold — whatever the schedule.

* **The prediction.**  Before any record is installed, the names every
  record will install are read off the records (`predictSlots`, the
  install skeleton), and with them every constant's counter.  The
  frozen base index maps each predicted name to its counter, its record
  and its position (`buildBase`).  Record `k`'s constants are its SLOT:
  a thunk over a promise that whoever installs the record resolves.  A
  worker view sees the base below its record's predicted counter, so a
  lookup waits only on an earlier record.
* **The install** of record `k` is `installStep` at the view of its
  predicted counter (`ConLeche/Verify/Cached/ViewCongr.lean`): the constants it
  pushes and, for a definition, theorem or opaque, its pending check.
  Its result travels to the commit thread with its evidence (`WRes`).
* **The commit.**  The commit thread takes record `k`'s install result,
  checks that the predicted counter is the serial one and that every
  slot the constants fill holds that very constant (`slotsOk`: pointer
  comparisons), and adds the step by `installStep_commit` — the view
  answers every lookup as the serial index does (`ViewAgrees`), and an
  install at two such indices pushes the same constants
  (`checkDeclStepC_twin`), so the install at the view IS the serial step.
* **Progress.**  A record the commit thread reaches unclaimed it claims
  and installs itself, at its view, which waits on nothing (every earlier
  record is committed).  A worker waits only on earlier records, so no
  cycle exists.
* **Fallback.**  A misprediction — a counter or a slot that does not
  match — loses only the parallelism: the commit thread stops the
  workers (every unresolved slot is resolved empty, so nobody stays
  waiting) and continues with `installLoop` from the run it holds.  A
  rejection is reported at the first failing record in fold order, with
  the serial step's error (`installStep_commit_error`).

**Reference counts across threads.**  The records and the base index
are marked persistent before the first worker starts, and every install
result is marked persistent by its installer before it is published, so
nothing a worker reads is counted atomically but the promises.  The
serial index is the commit thread's alone: nothing else holds it, so
every push updates it in place.

**The schedule** (performance only): workers walk the records in
stream order off a shared cursor and install each one that is READY —
whose dependencies, the records installing the names its expressions
mention, have all been installed; a record that is not is installed
when its last dependency is, by the worker that installed that one.
The common case takes no lock (`Sched`).
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
two drift apart by a stream-dependent amount.  Calibrate by NAME. -/
def installLoop (mode : ConLeche.CheckMode) (err : IO.FS.Stream)
    (stride total t0 : Nat)
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
      match h : ConLeche.Cached.annotDeclStep mode ConLeche.natOpPinSets p pd with
      | .ok p₁ =>
        installLoop mode err stride total t0 ds p₀ (i + 1) p₁ (by
          have hlist : ds.toList.take (i + 1) = ds.toList.take i ++ [pd] := by
            rw [List.take_add_one]
            simp [pd, Array.getElem?_eq_getElem hi]
          rw [hlist]
          exact ConLeche.Cached.InstallRun.snoc mode hrun h)
      | .error e => return .error e
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
    andPinOk pd = true ∧ ∀ L vg?, r = .ok (L, vg?) → slotsOk B S v L = true

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
record at or below it: the scheduler hands out no record past the gate
before those are installed (`Sched.earlyLeft`), and without that rule
every record would be a dependent of the dozen basis records, a hub
whose dependents' lists the assembly would build serially. -/
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
  -- persistent (unless `noMark`): the edges are read by every chunk's
  -- dependents task, and freeing them is otherwise one serial walk by
  -- whichever task drops them last
  if !noMark then
    let _ ← unsafe Runtime.markPersistent edges
  return (counts, state, edges)

/-- The dependents of records `lo .. hi - 1` (chunk `r`), on a task of
its own: the groups into the chunk from every chunk at or after it, in
chunk order, so each record's dependents are ascending. -/
def dependentsChunk (edges : Array (Array (Array (Nat × Array Nat))))
    (r lo hi : Nat) : IO (Array (Array Nat)) := do
  let mut acc : Array (Array Nat) := Array.replicate (hi - lo) #[]
  for t in [r:edges.size] do
    if let some es := edges[t]? then
      if let some e := es[r]? then
        for (d, ks) in e do
          acc := acc.modify (d - lo) (· ++ ks)
  return acc

/-- The slots of records `lo .. hi - 1`, on a task of its own: one
promise each, and the thunk over it a view reads. -/
def slotChunk (lo hi : Nat) : IO (Array (IO.Promise (Array ConstantInfo)) × Slots) := do
  let mut ps := Array.mkEmpty (hi - lo)
  let mut ss : Slots := Array.mkEmpty (hi - lo)
  for _ in [lo:hi] do
    let p ← IO.Promise.new
    ps := ps.push p
    ss := ss.push (Thunk.mk fun _ => (p.result?.get).getD #[])
  return (ps, ss)

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
`cursor` (one atomic claim per record, no lock); record `k`'s count
starts at its number of dependencies PLUS ONE, the extra token being
the cursor's pass.  Whoever brings a count to zero — the cursor's pass
if every dependency is already installed, else the release of the last
one — has the record ready.  A record that becomes ready by a release
(it was passed while blocked) goes to the `deferred` set (a persistent
tree under `lock`, lowest first; `deferredN` is its size, read without
the lock), which a worker drains before advancing the cursor.  `taken`
is a per-record test-and-set: the commit thread may install a record
itself, and whoever loses the race skips it.  The lock and the
condition variable are touched only for deferred records and by
workers idle at the end of the stream.  (A first scheduler kept EVERY
ready record in the tree under the lock: at 32 workers the workers
spent ~60 % of the install blocked in `mutex::lock`.) -/
structure Sched where
  counts : Array (IO.Ref Nat)
  dependents : Array (Array Nat)
  cursor : IO.Ref Nat
  deferred : IO.Ref (Std.TreeSet Nat compare)
  deferredN : IO.Ref Nat
  stop : IO.Ref Bool
  lock : Std.BaseMutex
  cv : Std.Condvar
  /-- the gate (`recDeps`): no record past it is handed out while
  `earlyLeft`, the number of records at or below it not yet
  installed, is positive -/
  gate : Nat
  earlyLeft : IO.Ref Nat

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

/-- The next ready record for a worker, or `none` once stopped: a
deferred one, else the cursor's next record if it is ready (a record
that is not stays with its dependencies' releases); at the end of the
stream, wait for a deferred record or the stop. -/
partial def nextReady (sc : Sched) (n : Nat) (held : Option Nat) :
    IO (Option Nat × Option Nat) := do
  if ← sc.stop.get then return (none, none)
  if let some d ← popDeferred sc then return (some d, held)
  -- the worker's held record (a cursor record past the closed gate), else
  -- the cursor's next one
  let k ← match held with
    | some k => pure k
    | none => sc.cursor.modifyGet fun k => (k, k + 1)
  if k < n then
    if k > sc.gate && (← sc.earlyLeft.get) > 0 then
      -- past the closed gate: hold the record and sleep until the gate
      -- opens or a deferred record turns up
      sc.lock.lock
      if !(← sc.stop.get) && (← sc.earlyLeft.get) > 0 && (← sc.deferredN.get) == 0 then
        sc.cv.wait sc.lock
      sc.lock.unlock
      nextReady sc n (some k)
    else if ← decCount sc k then return (some k, none)
    else nextReady sc n none
  else
    sc.lock.lock
    if !(← sc.stop.get) && (← sc.deferredN.get) == 0 then
      sc.cv.wait sc.lock
    sc.lock.unlock
    nextReady sc n none


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
  if (← sh.commitWait.get) == k + 1 then
    sh.commitLock.lock
    sh.commitLock.unlock
    sh.commitCv.notifyOne
  if k ≤ sh.sched.gate then
    if (← sh.sched.earlyLeft.modifyGet fun c => (c - 1, c - 1)) == 0 then
      sh.sched.lock.lock
      sh.sched.lock.unlock
      sh.sched.cv.notifyAll
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

/-- One worker: install the record its last install made ready, else the
next ready one, repeat until stopped; returns how many it installed. -/
partial def workerLoop (sh : Shared mode ds B S vis) (cnt : Nat) (cont held : Option Nat) :
    IO Nat := do
  let (k?, held) ← match cont with
    | some k => pure (some k, held)
    | none => nextReady sh.sched ds.size held
  match k? with
  | none => return cnt
  | some k =>
    if ← tryTake sh k then
      let (_, next) ← installAndPublish sh k
      workerLoop sh (cnt + 1) next held
    else
      workerLoop sh cnt none held

/-- Stop the workers: no new records, and every slot not resolved yet
resolved empty, so that nobody stays waiting on it. -/
def stopWorkers (sh : Shared mode ds B S vis) : IO Unit := do
  sh.sched.stop.set true
  sh.sched.lock.lock
  sh.sched.lock.unlock
  sh.sched.cv.notifyAll
  for p in sh.slotP do
    p.resolve #[]

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

/-- **The fallback**: stop the workers and continue serially from the
run the commit thread holds. -/
def fallbackFrom (err : IO.FS.Stream) (stride total t0 : Nat)
    (sh : Shared mode ds B S vis) (p₀ : Nat × FEnv × Array PendingCheck) (k : Nat)
    (p : Nat × FEnv × Array PendingCheck)
    (hrun : InstallRun mode natOpPinSets (ds.toList.take k) p₀ p) :
    IO (Except (CheckError × Nat)
      (Σ' (p' : Nat × FEnv × Array PendingCheck),
        PLift (InstallRun mode natOpPinSets ds.toList p₀ p'))) := do
  stopWorkers sh
  if stride > 0 then
    err.putStr s!"con-leche: parallel install abandoned at fold position {k} \
      (a predicted slot did not match, or --install-fallback-at), continuing serially\n"
    err.flush
  installLoop mode err stride total t0 ds p₀ k p hrun

/-- **The commit loop.**  `installLoop`'s run, one record per step, each
record's step added from its install at its view.  `cst` counts the
commit thread's waits on a worker and its own installs, with their
times. -/
def commitLoop (err : IO.FS.Stream) (stride total t0 : Nat) (fallbackAt : Option Nat)
    (hB : BaseInj B) (sh : Shared mode ds B S vis) (cst : IO.Ref (Array Nat))
    (p₀ : Nat × FEnv × Array PendingCheck) :
    (k : Nat) →
    (p : Nat × FEnv × Array PendingCheck) →
    InstallRun mode natOpPinSets (ds.toList.take k) p₀ p →
    IdxBelow p.2.1 → ViewAgrees B S p.2.1 →
      IO (Except (CheckError × Nat)
        (Σ' (p' : Nat × FEnv × Array PendingCheck),
          PLift (InstallRun mode natOpPinSets ds.toList p₀ p')))
  | k, (i, fe, pend), hrun, hidx, hag => do
    if hk : k < ds.size then
      let pd := ds[k]
      have hlist : ds.toList.take (k + 1) = ds.toList.take k ++ [pd] := by
        rw [List.take_add_one]
        simp [pd, Array.getElem?_eq_getElem hk]
      if stride > 0 && i % stride == 0 then
        let now ← IO.monoMsNow
        err.putStr s!"con-leche: install {i}/{total} \
          {ConLeche.Cached.declCLabel pd} \
          t={ConLeche.Cached.msSecs (now - t0)}s\n"
        err.flush
      if fallbackAt == some k then
        fallbackFrom err stride total t0 sh p₀ k (i, fe, pend) hrun
      else if hv : vis[k]? = some fe.visibleBelow then
        -- the record's install: here if nobody took it, else the
        -- installer's, slept for (never spun) if it is still running
        let mine ← tryTake sh k
        let q? : Option (WRes mode ds B S vis) ← do
          if mine then
            let tf0 ← IO.monoNanosNow
            let (q, next) ← installAndPublish sh k
            if let some d := next then deferRecord sh.sched d
            let tf1 ← IO.monoNanosNow
            cst.modify fun a => (a.modify 2 (· + 1)).modify 3 (· + (tf1 - tf0))
            pure (some q)
          else waitDone sh cst k
        match q? with
        | none => fallbackFrom err stride total t0 sh p₀ k (i, fe, pend) hrun
        | some ⟨(k', r, good), hr, hg⟩ =>
          if hk' : k' = k then
            if hgood : good = true then
              have hG : GoodAt ds B S vis k r := hk' ▸ hg hgood
              have hG' := hG pd fe.visibleBelow (Array.getElem?_eq_getElem hk) hv
              have hval : r = installStep mode natOpPinSets (workerView B S fe.visibleBelow) pd := by
                have hr' : r = workerRes mode ds B S vis k := hk' ▸ hr
                rw [hr']
                simp only [workerRes, Array.getElem?_eq_getElem hk, hv, pd]
              match hres : r with
              | .ok (L, vg?) =>
                let v := fe.visibleBelow
                have hok := hG'.2 L vg? hres
                have hstep := installStep_commit (pins := natOpPinSets) (i := i) (pend := pend)
                  hag hidx hG'.1 (hval.symm.trans hres)
                commitLoop err stride total t0 fallbackAt hB sh cst p₀ (k + 1)
                  (i + 1, FEnv.pushAll L fe, pushPending pend i v vg?)
                  (by rw [hlist]; exact InstallRun.snoc mode hrun hstep)
                  (hidx.pushAll L)
                  (ViewAgrees.pushAll hB L hidx hag hok)
              | .error e => return .error (e, i)
            else fallbackFrom err stride total t0 sh p₀ k (i, fe, pend) hrun
          else fallbackFrom err stride total t0 sh p₀ k (i, fe, pend) hrun
      else fallbackFrom err stride total t0 sh p₀ k (i, fe, pend) hrun
    else
      return .ok ⟨(i, fe, pend), ⟨by
        rw [List.take_of_length_le (by simp; omega)] at hrun
        exact hrun⟩⟩
  termination_by k => ds.size - k

end ParInstall

/-- **Phase A on `jobs` worker threads** (the section above): the
prediction, the base index, the slots, the dependencies and the
workers, the commit loop; at the end the workers are stopped and
joined.  Its result is `installLoop`'s. -/
def parInstall (mode : CheckMode) (err : IO.FS.Stream) (stride total t0 jobs : Nat)
    (noMark : Bool) (fallbackAt : Option Nat) (ds : Array Declaration) :
    IO (Except (CheckError × Nat)
      (Σ' (p' : Nat × FEnv × Array Cached.PendingCheck),
        PLift (Cached.InstallRun mode natOpPinSets ds.toList
          (0, mkFEnv Env.empty, #[]) p'))) := do
  let tA ← IO.monoMsNow
  let n := ds.size
  let parts := max 1 jobs
  let chunks := ParInstall.chunkBounds n parts
  -- the records are read by every task below: persistent first, so that
  -- no task spawn walks them for multi-threaded marking
  if !noMark then
    let _ ← unsafe Runtime.markPersistent ds
  let tA0 ← IO.monoMsNow
  -- the prediction, chunk per task; then the counters (prefix sums)
  let predTasks := chunks.map fun (lo, hi) =>
    Task.spawn (prio := .dedicated) fun _ => ParInstall.predictChunk ds parts lo hi
  let preds := predTasks.map Task.get
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
  let B := Cached.buildBase slots offs buckets parts
  -- (`B.size` forces the prediction and the base before the clock is read)
  let tA' ← if B.size + vis.size == 0 then IO.monoMsNow else IO.monoMsNow
  if !noMark then
    -- one mark for both (the pair's components are what it reaches)
    let _ ← unsafe Runtime.markPersistent (B, vis)
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
  let mut depTasks := #[]
  for (lo, hi) in chunks do
    depTasks := depTasks.push (← IO.asTask (prio := .dedicated)
      (ParInstall.depsChunk (α := ParInstall.WRes mode ds B S vis) B ds noMark gate n parts lo hi))
  let mut counts : Array (IO.Ref Nat) := Array.mkEmpty n
  let mut state : Array (IO.Ref (ParInstall.RState (ParInstall.WRes mode ds B S vis))) :=
    Array.mkEmpty n
  let mut edges : Array (Array (Array (Nat × Array Nat))) := Array.mkEmpty parts
  for t in depTasks do
    let (c, st, e) ← IO.ofExcept (← IO.wait t)
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
  if !noMark then
    let _ ← unsafe Runtime.markPersistent dependents
  let sched : ParInstall.Sched :=
    { counts, dependents, cursor := ← IO.mkRef 0,
      deferred := ← IO.mkRef ∅, deferredN := ← IO.mkRef 0,
      stop := ← IO.mkRef false, lock := ← Std.BaseMutex.new, cv := ← Std.Condvar.new,
      gate, earlyLeft := ← IO.mkRef (min n (gate + 1)) }
  let sh : ParInstall.Shared mode ds B S vis :=
    { slotP, state, sched, noMark, commitWait := ← IO.mkRef 0,
      commitLock := ← Std.BaseMutex.new, commitCv := ← Std.Condvar.new }
  let tD ← IO.monoMsNow
  let mut tasks := #[]
  for _ in [0:jobs] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) (ParInstall.workerLoop sh 0 none none))
  let cst ← IO.mkRef (Array.replicate 4 0)
  let res ← ParInstall.commitLoop err stride total t0 fallbackAt (Cached.buildBase_inj slots offs buckets parts)
    sh cst (0, mkFEnv Env.empty, #[]) 0 (0, mkFEnv Env.empty, #[]) (.nil _)
    Cached.IdxBelow.mkFEnv_empty (Cached.ViewAgrees.empty B S)
  let tE ← IO.monoMsNow
  ParInstall.stopWorkers sh
  let mut installs := 0
  for t in tasks do
    match ← IO.wait t with
    | .ok c => installs := installs + c
    | .error _ => pure ()
  if stride > 0 then
    let c ← cst.get
    err.putStr s!"con-leche: parallel install: records marked persistent {tA0 - tA} ms, prediction+base {tA' - tA0} ms, \
      base marked persistent {tB - tA'} ms, \
      slots {tC0 - tB} ms, dependencies {tC - tC0} ms, dependents {tD - tC} ms, commit {tE - tD} ms; \
      {installs} records installed by workers; commit thread: {c[0]!} sleeps on a worker \
      ({c[1]! / 1000000} ms), {c[2]!} records installed itself ({c[3]! / 1000000} ms)\n"
    err.flush
  return res

end ConLeche.Driver
