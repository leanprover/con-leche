module

public import ConLeche.Frontend.RoundsWork
public import ConLeche.Verify.Frontend.Rounds
public import Std.Sync.Mutex

/-!
# The rounds parse driver (task #329)

The parse at `--jobs` above one.  The stream is read forward in chunks
of whole lines (each read cut at its last newline, as the pipelined
parse cuts it, `ConLeche/Frontend/Pipeline.lean`); every chunk is
scanned flat on a worker; the chunks are taken a window at a time, and
a window's tables are computed in rounds on the workers
(`ConLeche/Frontend/RoundsWork.lean`): round 0 per chunk, then the
deferred lines until none is left, then the window's tables join the
finished tables page by page.

**What is trusted, and what is not.**  Nothing the rounds compute is
believed.  The finished tables after the window are tested to agree
with the tables before below the window's start (`Prior.keeps`), and
every chunk is CHECKED against them, line by line, at the counters the
serial parse has there (`checkFlat`).  A chunk that passes is one more
step of the serial parse (`GOK.chunk`, `ConLeche/Verify/Frontend/Rounds.lean`),
so the driver carries `GOK` from chunk to chunk and returns its result
with the evidence `ParseOutcome` asks for (`GOK.finish`).

**Fallback.**  A window whose chunks do not qualify (a tail carried, a
malformed line), whose rounds meet anything unusual (an index below its
table's counter — a stream that does not bind in increasing order — a
line the serial parse would fail at, a round without progress, more
rounds than a table holds), or a chunk that fails its check, is handed
to the serial parse from the state the chunks before it reached
(`GOK.reached`, the finished tables as a parse state): the window's
chunks and every chunk read so far by `chunkStepF`, the rest of the
stream by the pipelined parse (`loopP`).  That is the serial verdict,
at the serial line.

**Threads.**  `jobs` dedicated workers take jobs from two queues: the
rounds, pages and checks of the current window first, the scans of the
chunks read ahead when nothing else is waiting.  The main thread reads,
assembles, and folds the checks.

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

/-! ## Reading and scanning -/

/-- A chunk and its flat scan. -/
abbrev Scanned := { x : ByteArray × FlatChunk // x.2.Encodes (scanChunk x.1) }

instance : Inhabited Scanned := ⟨⟨(.empty, scanFlat 0 .empty), scanFlat_encodes _ _⟩⟩

/-- The scan job: the chunk `pending ++ buf0[0, k)`, put together and
scanned on the worker. -/
def scanJob (pending buf0 : ByteArray) (k : Nat) : IO Scanned :=
  IO.lazyPure fun _ =>
    let blk := if pending.isEmpty then buf0.extract 0 k else pending ++ buf0.extract 0 k
    ⟨(blk, scanFlat (blk.size / 2) blk), scanFlat_encodes _ _⟩

/-- Read until `want` chunks are queued or the stream has ended; each
chunk's scan is a job.  Returns the queue, its length, the leftover
bytes and whether the stream ended. -/
partial def readAhead (pl : Pool) (h : IO.FS.Handle) (csz : USize) (want : Nat)
    (q : Std.Queue (IO.Promise Scanned)) (n : Nat) (pending : ByteArray) (eof : Bool) :
    IO (Std.Queue (IO.Promise Scanned) × Nat × ByteArray × Bool) := do
  if eof || n ≥ want then return (q, n, pending, eof)
  let buf0 ← h.read csz
  if buf0.isEmpty then
    if pending.isEmpty then return (q, n, pending, true)
    else
      let p ← pl.run .lo (scanJob pending .empty 0)
      return (q.enqueue p, n + 1, .empty, true)
  else
    match lastNewlineBelow buf0 buf0.size with
    | none => readAhead pl h csz want q n (pending ++ buf0) false
    | some k =>
      let p ← pl.run .lo (scanJob pending buf0 (k + 1))
      readAhead pl h csz want (q.enqueue p) (n + 1) (buf0.extract (k + 1) buf0.size) false

/-- Up to `m` chunks off the queue. -/
def takeN (q : Std.Queue (IO.Promise Scanned)) (m : Nat) (acc : Array (IO.Promise Scanned)) :
    Array (IO.Promise Scanned) × Std.Queue (IO.Promise Scanned) :=
  match m with
  | 0 => (acc, q)
  | m + 1 =>
    match q.dequeue? with
    | some (p, q') => takeN q' m (acc.push p)
    | none => (acc, q)

/-! ## The fallback -/

/-- Scanned chunks applied by the serial parse, one after the other. -/
def serialScanned (st : StateD) (carry : ByteArray) (lineNo total : Nat)
    (hr : Reached st carry lineNo total) : List Scanned →
    Except ParseOutcome (Σ' (st : StateD) (carry : ByteArray) (lineNo total : Nat),
      Reached st carry lineNo total)
  | [] => .ok ⟨st, carry, lineNo, total, hr⟩
  | x :: xs =>
    match hs : chunkStepF st carry lineNo total x.val.1 x.val.2 with
    | .error e => .error ⟨.error e, hr.error (c := x.val.1) (by
        rw [← chunkStepF_of_encodes _ _ _ _ _ _ x.property]; exact hs)⟩
    | .ok (st', carry', lineNo', total') =>
      serialScanned st' carry' lineNo' total' (hr.step (c := x.val.1) (by
        rw [← chunkStepF_of_encodes _ _ _ _ _ _ x.property]; exact hs)) xs

/-- **The fallback**: from the state the chunks before reached, the
chunks given and every chunk read so far by the serial parse, then the
rest of the stream by the pipelined parse. -/
def fallback (pl : Pool) (h : IO.FS.Handle) (inflight : Nat) (csz : USize) (g : GSt)
    (hg : GOK g) (xs : List Scanned) (q : Std.Queue (IO.Promise Scanned)) (pending : ByteArray)
    (eof : Bool) : IO ParseOutcome := do
  -- the chunks read ahead, scanned (the pool runs their scans)
  let mut rest : Array Scanned := #[]
  let mut q := q
  repeat
    match q.dequeue? with
    | some (p, q') => rest := rest.push (← await p); q := q'
    | none => break
  pl.shutdown
  match serialScanned (g.P.toState g.c g.ds) .empty g.lineNo g.total hg.reached
      (xs ++ rest.toList) with
  | .error r => return r
  | .ok ⟨st, carry, lineNo, total, hr⟩ =>
    loopP h inflight csz st carry lineNo total hr ∅ 0 none pending eof

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

/-- The result of a window: on to the next, or the fallback from where
the checked chunks got. -/
inductive WinRes where
  | next (g : GSt) (hg : GOK g)
  | fall (g : GSt) (hg : GOK g) (xs : List Scanned)

/-- A chunk's check, with the evidence that it is `checkFlat` of the
chunk at the given counters. -/
structure CheckRes (P : Prior) where
  x : Scanned
  s : Ctr
  r : Option (Ctr × Array Declaration)
  h : r = checkFlat P x.val.2 s

/-- **The checked chunks, folded**: each chunk whose check ran at the
counters the chunks before reached and passed is one more serial step
(`GOK.chunk`); at the first that is not, the rest falls back. -/
def foldChecks (P : Prior) : List (CheckRes P) → (g : GSt) → GOK g → g.P = P → WinRes
  | [], g, hg, _ => .next g hg
  | r :: rest, g, hg, hP =>
    if hs : r.s.beq g.c then
      match hr : r.r with
      | some (c', ds') =>
        if hf : chunkFits r.x.val.1 r.x.val.2 g.total then
          foldChecks P rest _ (GOK.chunk hg r.x.property hf (c' := c') (ds' := ds') (by
            rw [hP, ← Ctr.beq_iff.mp hs, ← r.h, hr])) hP
        else .fall g hg (r.x :: rest.map (·.x))
      | none => .fall g hg (r.x :: rest.map (·.x))
    else .fall g hg (r.x :: rest.map (·.x))

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

/-- **A window's tables**, untrusted: round 0, the later rounds, the
pages after it, from the finished tables `P` at counters `c0` and the
byte count `total`; `none` on any anomaly. -/
def computeW (pl : Pool) (cfg : Cfg) (P : Prior) (c0 : Ctr) (total : Nat) (xs : Array Scanned) :
    IO (Option (Win × Array (Array Name) × Array (Array Level) × Array (Array Expr))) := do
  -- every chunk whole, and under the size guard
  let (fits, _) := xs.foldl (fun (ok, t) x => (ok && chunkFits x.val.1 x.val.2 t,
    t + x.val.1.size)) (true, total)
  if !fits then return none
  -- round 0
  let mut ps : Array (IO.Promise R0) := #[]
  for i in [0:xs.size] do
    let fc := (xs.getD i default).val.2
    ps := ps.push (← pl.run .hi (do
      let o ← IO.lazyPure fun _ => round0 P c0 i fc
      -- the entries round 0 bound (in its round-0 arrays)
      markEach cfg.noMark o.dn; markEach cfg.noMark o.dl; markEach cfg.noMark o.de
      return o))
  let os ← ps.mapM await
  let W := Win.ofRound0 c0 (xs.map (·.val.2.data)) os
  if !after0 W os then return none
  -- the later rounds
  let some W ← roundsIO pl cfg.noMark P W (os.map (·.pend)) (os.map (·.npend)) 0
    | return none
  -- the finished tables after the window
  let cE := W.cEnd
  let nn ← pagesIO pl P.n W.n c0.n cE.n
  let nl ← pagesIO pl P.l W.l c0.l cE.l
  let ne ← pagesIO pl P.e W.e c0.e cE.e
  return some (W, nn, nl, ne)

/-- A window whose tables have joined the finished ones and whose
checks are running: `g` is the state before it with those tables. -/
structure Pend where
  g : GSt
  hg : GOK g
  cps : Array (IO.Promise (CheckRes g.P))
  /-- the counters and byte count after the window, as its rounds say -/
  cEnd : Ctr
  tEnd : Nat

/-- The checks of a window, on the workers (each chunk at the counters
its rounds started it at). -/
def startChecks (pl : Pool) (cfg : Cfg) (P : Prior) (W : Win) (xs : Array Scanned) :
    IO (Array (IO.Promise (CheckRes P))) := do
  let mut cps : Array (IO.Promise (CheckRes P)) := #[]
  for i in [0:xs.size] do
    let x := xs.getD i default
    let s := W.start i
    have : Nonempty (CheckRes P) := ⟨⟨x, s, _, rfl⟩⟩
    cps := cps.push (← pl.run .mid (do
      let r ← IO.lazyPure fun _ =>
        (⟨checkFlat P x.val.2 s, rfl⟩ : { r // r = checkFlat P x.val.2 s })
      if let some (_, ds) := r.val then markEach cfg.noMark ds
      return ⟨x, s, r.val, r.property⟩))
  return cps

/-- A window's checks, waited for and folded. -/
def foldPend (p : Pend) : IO WinRes := do
  have : Nonempty (CheckRes p.g.P) := ⟨⟨default, default, _, rfl⟩⟩
  let cs ← p.cps.mapM await
  return foldChecks p.g.P cs.toList p.g p.hg rfl

/-- Where the stream is between windows: every window checked, or the
last one's checks running. -/
inductive Done where
  | ready (g : GSt) (hg : GOK g)
  | pend (p : Pend)

/-! ## The stream -/

/-- **The rounds parse of a stream**, window after window, carrying
`GOK`.  A window's tables are computed while the window before it is
being checked; the checks are folded before the window's own tables
join the finished ones.  A window that does not finish, or a chunk
that fails its check, falls back. -/
partial def streamLoop (pl : Pool) (h : IO.FS.Handle) (cfg : Cfg) (d : Done)
    (q : Std.Queue (IO.Promise Scanned)) (n : Nat) (pending : ByteArray) (eof : Bool) :
    IO ParseOutcome := do
  let (q, n, pending, eof) ← readAhead pl h cfg.csz (cfg.m + cfg.ahead) q n pending eof
  let (win, q) := takeN q cfg.m #[]
  let n := n - win.size
  let xs ← win.mapM await
  -- the next window's tables, from the tables the window before left
  let comp ← if xs.isEmpty then pure none else
    match d with
    | .ready g _ => computeW pl cfg g.P g.c g.total xs
    | .pend p => computeW pl cfg p.g.P p.cEnd p.tEnd xs
  -- the window before, checked
  let r ← match d with
    | .ready g hg => pure (WinRes.next g hg)
    | .pend p => foldPend p
  match r with
  | .fall g hg rest =>
    cfg.fallbacks.modify (· + 1)
    fallback pl h cfg.inflight cfg.csz g hg (rest ++ xs.toList) q pending eof
  | .next g hg =>
    if xs.isEmpty then
      pl.shutdown
      return ⟨.ok ⟨g.ds⟩, hg.finish⟩
    match comp with
    | none =>
      cfg.fallbacks.modify (· + 1)
      fallback pl h cfg.inflight cfg.csz g hg xs.toList q pending eof
    | some (W, nn, nl, ne) =>
      if hk : g.P.keeps g.c nn nl ne then
        let P' := g.P.setFrom g.c nn nl ne
        let g1 : GSt := { g with P := P' }
        let cps ← startChecks pl cfg P' W xs
        let tEnd := xs.foldl (fun t x => t + x.val.1.size) g.total
        streamLoop pl h cfg (.pend ⟨g1, GOK.keep hg hk, cps, W.cEnd, tEnd⟩) q n pending eof
      else
        cfg.fallbacks.modify (· + 1)
        fallback pl h cfg.inflight cfg.csz g hg xs.toList q pending eof

/-- **The rounds parse of a file** on `jobs` workers, windows of `m`
chunks of about `csz` bytes, `ahead` chunks read and scanned beyond the
window; with the number of windows that fell back. -/
def parseExportStreamRInfo (path : System.FilePath) (jobs m : Nat) (csz : USize)
    (ahead inflight : Nat) (noMark : Bool) : IO (ParseOutcome × Nat) := do
  let h ← IO.FS.Handle.mk path .read
  let fb ← IO.mkRef 0
  let pl ← Pool.start jobs
  let r ← streamLoop pl h ⟨max 1 m, csz, inflight, noMark, ahead, fb⟩ (.ready .init GOK.init)
    ∅ 0 .empty false
  return (r, ← fb.get)

/-- **The rounds parse of a file.** -/
def parseExportStreamR (path : System.FilePath) (jobs m : Nat) (csz : USize)
    (ahead inflight : Nat) (noMark : Bool) : IO ParseOutcome :=
  return (← parseExportStreamRInfo path jobs m csz ahead inflight noMark).1

end ConLeche.Driver.ParParse
