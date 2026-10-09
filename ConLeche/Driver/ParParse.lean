module

public import ConLeche.Frontend.RoundsWork
public import Std.Sync.Mutex

/-!
# The rounds: the pool and the window's tables (task #329)

The machinery the lazy parse (`ConLeche/Driver/LazyParse.lean`) builds
a window's tables with: a pool of `jobs` dedicated workers taking jobs
from three queues (`Pool`), the later rounds of a window
(`roundsIO`, over `ConLeche/Frontend/RoundsWork.lean`'s `roundR`), and
the pages the window's tables join the finished ones with (`pagesIO`).
Nothing the rounds compute is believed: the lazy parse checks every
chunk against the finished tables, line by line.

**Memory.**  An object every worker reads must not have its reference
count touched by them, or the count is an atomic word all of them
fight over: what is read through a borrowed reference (the tables, the
window, the chunks' scans) is never counted on the way, and the table
entries themselves — every name, level and expression the parse
builds, and every record — are marked persistent by the worker that
built them, before it hands them out (`markEach`, the install driver's
escape `Runtime.markPersistent`; they live to the end of the run).
Nothing else is marked: the arrays that hold the entries (a window's
round arrays, the pages of the finished tables) and the bookkeeping
(pending lines, positions, keys) are dropped and freed when the window,
or the parse, is done with them; what crosses threads among them is
either flat (a chunk's scan, its pending lines) or a container the
runtime marks itself, without walking into the persistent entries.
-/

@[expose] public section

namespace ConLeche.Driver.ParParse

open ConLeche ConLeche.Frontend

/-! ## The pool -/

/-- `n` dedicated workers and three job queues: the rounds and pages
of the current window first, then the checks of the window before,
then the scans of the chunks read ahead. -/
structure Pool where
  lock : Std.BaseMutex
  cv : Std.Condvar
  hi : IO.Ref (Std.Queue (IO Unit))
  mid : IO.Ref (Std.Queue (IO Unit))
  lo : IO.Ref (Std.Queue (IO Unit))
  stop : IO.Ref Bool

/-- Job priorities. -/
inductive Prio where
  | hi | mid | lo

/-- Queue a job. -/
def Pool.submit (pl : Pool) (prio : Prio) (act : IO Unit) : IO Unit := do
  pl.lock.lock
  match prio with
  | .hi => pl.hi.modify (·.enqueue act)
  | .mid => pl.mid.modify (·.enqueue act)
  | .lo => pl.lo.modify (·.enqueue act)
  pl.lock.unlock
  pl.cv.notifyOne

/-- The next job, waiting for one (the lock held); `none` once stopped. -/
partial def Pool.next (pl : Pool) : IO (Option (IO Unit)) := do
  if ← pl.stop.get then return none
  let deq (q : Std.Queue (IO Unit)) : Option (IO Unit) × Std.Queue (IO Unit) :=
    match q.dequeue? with
    | some (a, q') => (some a, q')
    | none => (none, q)
  match ← pl.hi.modifyGet deq with
  | some a => return some a
  | none =>
    match ← pl.mid.modifyGet deq with
    | some a => return some a
    | none =>
      match ← pl.lo.modifyGet deq with
      | some a => return some a
      | none =>
        pl.cv.wait pl.lock
        pl.next

/-- A worker: jobs until the pool stops. -/
partial def Pool.worker (pl : Pool) : IO Unit := do
  pl.lock.lock
  let a ← pl.next
  pl.lock.unlock
  match a with
  | none => return
  | some act =>
    try act catch _ => pure ()
    pl.worker

/-- A pool of `n` workers. -/
def Pool.start (n : Nat) : IO Pool := do
  let lock ← Std.BaseMutex.new
  let cv ← Std.Condvar.new
  let hi ← IO.mkRef (∅ : Std.Queue (IO Unit))
  let mid ← IO.mkRef (∅ : Std.Queue (IO Unit))
  let lo ← IO.mkRef (∅ : Std.Queue (IO Unit))
  let stop ← IO.mkRef false
  let pl : Pool := ⟨lock, cv, hi, mid, lo, stop⟩
  for _ in [0:max 1 n] do
    let _ ← IO.asTask (prio := .dedicated) pl.worker
  return pl

/-- Stop the workers (they finish their jobs and exit; nobody joins
them). -/
def Pool.shutdown (pl : Pool) : IO Unit := do
  pl.lock.lock
  pl.stop.set true
  pl.lock.unlock
  pl.cv.notifyAll

/-- A job whose result is waited for. -/
def Pool.run {α : Type} [Nonempty α] (pl : Pool) (prio : Prio) (f : IO α) :
    IO (IO.Promise α) := do
  let p ← IO.Promise.new
  pl.submit prio (do p.resolve (← f))
  return p

/-- A job's result. -/
def await {α : Type} [Nonempty α] (p : IO.Promise α) : IO α := do
  match ← IO.wait p.result? with
  | some a => pure a
  | none => throw (IO.userError "rounds parse: a job was dropped")

/-- Mark the ELEMENTS of an array persistent, not the array (which is
dropped later), unless `--no-mark-persistent`.  The escape is the
install driver's (`Runtime.markPersistent`, the identity on the value;
the object graph is marked in place and never freed).  An element's
walk stops at children already persistent: the entries it was built
from. -/
def markEach {α : Type} (noMark : Bool) (a : Array α) : IO Unit := do
  if !noMark then
    a.forM fun (x : α) => do let _ ← unsafe Runtime.markPersistent x

/-! ## A window -/

/-- The driver's settings. -/
structure Cfg where
  /-- chunks per window -/
  m : Nat
  /-- bytes per read -/
  csz : USize
  /-- chunks scanned ahead of the fallback's applying loop -/
  inflight : Nat
  noMark : Bool
  /-- chunks read and scanned beyond the current window -/
  ahead : Nat
  /-- counts the windows that fell back (for the tests) -/
  fallbacks : IO.Ref Nat

/-- The pages a window over `[lo, hi)` (re)writes, on the workers, in
groups of `grp`. -/
def pagesIO {α : Type} [Sent α] (pl : Pool) (P : Pages α) (s : Seg α)
    (lo hi : Nat) : IO (Array (Array α)) := do
  let p0 := pagesFrom lo
  let cnt := pagesCount lo hi
  let grp := 16
  let mut ps : Array (IO.Promise (Array (Array α))) := #[]
  let mut i := 0
  while i < cnt do
    let a := i
    let b := min cnt (i + grp)
    ps := ps.push (← pl.run .hi (do
      let pg ← IO.lazyPure fun _ =>
        (List.range (b - a)).foldl (fun acc k => acc.push (pageOf P s lo hi (p0 + a + k)))
          (Array.mkEmpty (b - a))
      return pg))
    i := b
  let mut out : Array (Array α) := Array.mkEmpty cnt
  for p in ps do
    out := out ++ (← await p)
  return out

/-- What a later round leaves of a chunk with nothing pending. -/
def idleRR (W : Win) (c : Nat) : RR := ⟨W.own c, .empty, 0, 0, false⟩

instance : Nonempty RR := ⟨⟨⟨.blank, .blank, .blank⟩, .empty, 0, 0, false⟩⟩
instance : Nonempty R0 := ⟨⟨#[], #[], #[], default, default, default, .empty, 0, 0, true⟩⟩

/-- The later rounds of a window, until nothing is pending: `none` on
an anomaly, a round without progress, or too many rounds. -/
partial def roundsIO (pl : Pool) (noMark : Bool) (P : Prior) (W : Win) (pends : Array ByteArray)
    (nps : Array Nat) (r : Nat) : IO (Option Win) := do
  if nps.all (· == 0) then return some W
  if r ≥ maxRounds then return none
  let mut ps : Array (Option (IO.Promise RR)) := #[]
  for c in [0:W.data.size] do
    let np := nps.getD c 0
    if np == 0 then ps := ps.push none
    else
      let pend := pends.getD c .empty
      ps := ps.push (some (← pl.run .hi (do
        let o ← IO.lazyPure fun _ => roundR P W c pend np
        -- the entries this round bound (in its late arrays)
        if let some d := o.own.n.late.back? then markEach noMark d
        if let some d := o.own.l.late.back? then markEach noMark d
        if let some d := o.own.e.late.back? then markEach noMark d
        return o)))
  let mut owns : Array Own := Array.mkEmpty W.data.size
  let mut pends' : Array ByteArray := Array.mkEmpty W.data.size
  let mut nps' : Array Nat := Array.mkEmpty W.data.size
  let mut prog := 0
  let mut bad := false
  let mut c := 0
  for p in ps do
    let o ← match p with
      | some p => await p
      | none => pure (idleRR W c)
    owns := owns.push o.own
    pends' := pends'.push o.pend
    nps' := nps'.push o.npend
    prog := prog + o.prog
    bad := bad || o.bad
    c := c + 1
  if bad || prog == 0 then return none
  roundsIO pl noMark P (W.setOwn owns) pends' nps' (r + 1)

end ConLeche.Driver.ParParse
