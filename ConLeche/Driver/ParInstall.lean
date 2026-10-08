module

public import ConLeche.Cached.ViewCongr
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
  predicted counter (`ConLeche/Cached/ViewCongr.lean`): the constants it
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

**The schedule** (performance only): workers take the lowest READY
record — one whose dependencies, the records installing the names its
expressions mention, have all been installed.
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

/-- An install result for a record, with its evidence: it is `workerRes`
of that record (an erased proof at run time). -/
def WRes (mode : CheckMode) (ds : Array Declaration) (B : BaseIdx) (S : Slots)
    (vis : Array Nat) : Type :=
  { q : Nat × Except CheckError (List ConstantInfo × Option ValueGroup) //
      q.2 = workerRes mode ds B S vis q.1 }

/-- The constants an install result publishes. -/
def slotOfRes : Except CheckError (List ConstantInfo × Option ValueGroup) → Array ConstantInfo
  | .ok (L, _) => L.toArray
  | .error _ => #[]

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
it looks up, ascending, without repeats. -/
def recDeps (B : BaseIdx) (k : Nat) (pd : Declaration) : Array Nat :=
  let (es, own) := declExprs pd
  let names := (es.foldl (fun acc e => depNames e acc)
    ({}, basisDepNames ++ own.toArray)).2
  let ks := names.filterMap fun n => match B[n]? with
    | some (_, k', _) => if k' < k then some k' else none
    | none => none
  let ks := ks.qsort (· < ·)
  ks.foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

/-- The dependencies of records `lo .. hi - 1`. -/
def depsChunk (B : BaseIdx) (ds : Array Declaration) (lo hi : Nat) : Array (Array Nat) :=
  (Array.range (hi - lo)).map fun i =>
    match ds[lo + i]? with
    | some pd => recDeps B (lo + i) pd
    | none => #[]

/-- The dependents of every record, from the dependencies. -/
def dependentsGo (deps : Array (Array Nat)) :
    (k : Nat) → Array (Array Nat) → Array (Array Nat)
  | k, acc =>
    if h : k < deps.size then
      let acc := deps[k].foldl (fun acc d => acc.modify d (·.push k)) acc
      dependentsGo deps (k + 1) acc
    else acc
  termination_by k => deps.size - k

/-- The scheduler: per-record counts of uninstalled dependencies, the
ready set (a persistent tree, so that an update under the lock copies a
path, not an array), the stop flag. -/
structure Sched where
  counts : Array (IO.Ref Nat)
  dependents : Array (Array Nat)
  ready : IO.Ref (Std.TreeSet Nat compare)
  stop : IO.Ref Bool
  lock : Std.BaseMutex
  cv : Std.Condvar

/-- Record `k` installed: its dependents' counts drop, and those that
reach zero become ready. -/
def release (sc : Sched) (k : Nat) : IO Unit := do
  match sc.dependents[k]? with
  | none => pure ()
  | some deps =>
    let mut newly : Array Nat := #[]
    for d in deps do
      match sc.counts[d]? with
      | some r =>
        let c ← r.modifyGet fun c => (c - 1, c - 1)
        if c == 0 then newly := newly.push d
      | none => pure ()
    if !newly.isEmpty then
      sc.lock.lock
      sc.ready.modify fun t => newly.foldl (fun t d => t.insert d) t
      sc.lock.unlock
      for _ in newly do
        sc.cv.notifyOne

/-- The next ready record for a worker (under the lock), or `none` once
stopped. -/
partial def nextReady (sc : Sched) : IO (Option Nat) := do
  if ← sc.stop.get then return none
  let k? ← sc.ready.modifyGet fun t => match t.min? with
    | some k => (some k, t.erase k)
    | none => (none, t)
  match k? with
  | some k => return some k
  | none =>
    sc.cv.wait sc.lock
    nextReady sc

/-- The commit thread claims record `k`: `true` if it was still ready
(nobody took it), and then it is no longer. -/
def claim (sc : Sched) (k : Nat) : IO Bool := do
  sc.lock.lock
  let r ← sc.ready.modifyGet fun t => if t.contains k then (true, t.erase k) else (false, t)
  sc.lock.unlock
  return r

variable {mode : CheckMode} {ds : Array Declaration} {B : BaseIdx} {S : Slots}
  {vis : Array Nat}

/-- The state the commit thread and the workers share. -/
structure Shared (mode : CheckMode) (ds : Array Declaration) (B : BaseIdx) (S : Slots)
    (vis : Array Nat) where
  /-- record `k`'s published constants (`S` reads them) -/
  slotP : Array (IO.Promise (Array ConstantInfo))
  /-- record `k`'s install result -/
  resP : Array (IO.Promise (WRes mode ds B S vis))
  sched : Sched
  noMark : Bool

/-- Install record `k` at its view and publish the result: marked
persistent first (unless `--no-mark-persistent`), then the slot (workers
may wait on it), the result for the commit thread, and the dependents
released. -/
def installAndPublish (sh : Shared mode ds B S vis) (k : Nat) :
    IO (WRes mode ds B S vis) := do
  let r := workerRes mode ds B S vis k
  let cs := slotOfRes r
  if !sh.noMark then
    let _ ← unsafe Runtime.markPersistent r
    let _ ← unsafe Runtime.markPersistent cs
  match sh.slotP[k]? with
  | some p => p.resolve cs
  | none => pure ()
  let q : WRes mode ds B S vis := ⟨(k, r), rfl⟩
  match sh.resP[k]? with
  | some p => p.resolve q
  | none => pure ()
  release sh.sched k
  pure q

/-- One worker: install the lowest ready record, repeat until stopped;
returns how many it installed. -/
partial def workerLoop (sh : Shared mode ds B S vis) (cnt : Nat) : IO Nat := do
  sh.sched.lock.lock
  let k? ← nextReady sh.sched
  sh.sched.lock.unlock
  match k? with
  | none => return cnt
  | some k =>
    let _ ← installAndPublish sh k
    workerLoop sh (cnt + 1)

/-- Stop the workers: no new records, and every slot not resolved yet
resolved empty, so that nobody stays waiting on it. -/
def stopWorkers (sh : Shared mode ds B S vis) : IO Unit := do
  sh.sched.stop.set true
  sh.sched.lock.lock
  sh.sched.lock.unlock
  sh.sched.cv.notifyAll
  for p in sh.slotP do
    p.resolve #[]

/-- The prediction: record `k`'s slots `(name, k, j)` and its counter. -/
def predictGo (ds : Array Declaration) :
    (k c : Nat) → Array Nat → Array (Name × Nat × Nat) →
      Array Nat × Array (Name × Nat × Nat)
  | k, c, vis, slots =>
    if h : k < ds.size then
      let names := predictSlots ds[k]
      let slots := (names.zipIdx).foldl (fun acc (n, j) => acc.push (n, k, j)) slots
      predictGo ds (k + 1) (c + names.size) (vis.push c) slots
    else (vis, slots)
  termination_by k => ds.size - k

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
      else if hw : andPinOk pd = true ∧ vis[k]? = some fe.visibleBelow then
        -- the record's install: here if nobody took it, else the worker's
        let tf0 ← IO.monoNanosNow
        let done ← match sh.resP[k]? with
          | some p => IO.hasFinished p.result?
          | none => pure false
        let mine ← if done then pure false else claim sh.sched k
        let q? : Option (WRes mode ds B S vis) ← do
          if mine then
            pure (some (← installAndPublish sh k))
          else match sh.resP[k]? with
            | some p => IO.wait p.result?
            | none => pure none
        let tf1 ← IO.monoNanosNow
        -- [0] waits on a worker, [1] their ns, [2] installs here, [3] their ns
        cst.modify fun a =>
          if mine then (a.modify 2 (· + 1)).modify 3 (· + (tf1 - tf0))
          else (a.modify 0 (· + 1)).modify 1 (· + (tf1 - tf0))
        match q? with
        | none => fallbackFrom err stride total t0 sh p₀ k (i, fe, pend) hrun
        | some ⟨(k', r), hr⟩ =>
          if hk' : k' = k then
            have hval : r = installStep mode natOpPinSets (workerView B S fe.visibleBelow) pd := by
              have hr' : r = workerRes mode ds B S vis k := hk' ▸ hr
              rw [hr']
              simp only [workerRes, Array.getElem?_eq_getElem hk, hw.2, pd]
            match hres : r with
            | .ok (L, vg?) =>
              if hok : slotsOk B S fe.visibleBelow L = true then
                let v := fe.visibleBelow
                have hstep := installStep_commit (pins := natOpPinSets) (i := i) (pend := pend)
                  hag hidx hw.1 (hval.symm.trans hres)
                commitLoop err stride total t0 fallbackAt hB sh cst p₀ (k + 1)
                  (i + 1, FEnv.pushAll L fe, pushPending pend i v vg?)
                  (by rw [hlist]; exact InstallRun.snoc mode hrun hstep)
                  (hidx.pushAll L)
                  (ViewAgrees.pushAll hB L hidx hag hok)
              else fallbackFrom err stride total t0 sh p₀ k (i, fe, pend) hrun
            | .error e => return .error (e, i)
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
  let (vis, slots) := ParInstall.predictGo ds 0 0 (Array.mkEmpty n) #[]
  let B := Cached.buildBase slots
  if !noMark then
    let _ ← unsafe Runtime.markPersistent ds
    let _ ← unsafe Runtime.markPersistent B
    let _ ← unsafe Runtime.markPersistent vis
  let tB ← IO.monoMsNow
  -- the dependencies, computed in parallel: `jobs` contiguous chunks
  let chunk := (n + jobs - 1) / jobs
  let mut depTasks := #[]
  for t in [0:jobs] do
    let lo := min n (t * chunk)
    let hi := min n (lo + chunk)
    depTasks := depTasks.push
      (Task.spawn (prio := .dedicated) fun _ => ParInstall.depsChunk B ds lo hi)
  let mut deps : Array (Array Nat) := Array.mkEmpty n
  for t in depTasks do
    deps := deps ++ (← IO.wait t)
  let tC ← IO.monoMsNow
  let dependents := ParInstall.dependentsGo deps 0 (Array.replicate n #[])
  if !noMark then
    let _ ← unsafe Runtime.markPersistent dependents
  let counts ← deps.mapM fun d => IO.mkRef d.size
  let ready := (Array.range n).foldl (init := (∅ : Std.TreeSet Nat compare)) fun t k =>
    if deps[k]!.isEmpty then t.insert k else t
  let sched : ParInstall.Sched :=
    { counts, dependents, ready := ← IO.mkRef ready,
      stop := ← IO.mkRef false, lock := ← Std.BaseMutex.new, cv := ← Std.Condvar.new }
  -- the slots: record `k`'s constants, as whoever installs it resolves them
  let slotP ← (Array.range n).mapM fun _ => IO.Promise.new
  -- a slot is a thunk over its promise: the first lookup waits for the
  -- publisher, every later one reads the thunk's (persistent) value
  -- with no reference count on any shared object
  let S : Cached.Slots := slotP.map fun p => Thunk.mk fun _ => (p.result?.get).getD #[]
  have : Nonempty (ParInstall.WRes mode ds B S vis) :=
    ⟨⟨(0, ParInstall.workerRes mode ds B S vis 0), rfl⟩⟩
  let resP ← (Array.range n).mapM fun _ => IO.Promise.new
  let sh : ParInstall.Shared mode ds B S vis := { slotP, resP, sched, noMark }
  let tD ← IO.monoMsNow
  let mut tasks := #[]
  for _ in [0:jobs] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) (ParInstall.workerLoop sh 0))
  let cst ← IO.mkRef (Array.replicate 4 0)
  let res ← ParInstall.commitLoop err stride total t0 fallbackAt (Cached.buildBase_inj slots)
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
    err.putStr s!"con-leche: parallel install: prediction+base {tB - tA} ms, \
      dependencies {tC - tB} ms, slots {tD - tC} ms, commit {tE - tD} ms; \
      {installs} records installed by workers; commit thread: {c[0]!} waits on a worker \
      ({c[1]! / 1000000} ms), {c[2]!} records installed itself ({c[3]! / 1000000} ms)\n"
    err.flush
  return res

end ConLeche.Driver
