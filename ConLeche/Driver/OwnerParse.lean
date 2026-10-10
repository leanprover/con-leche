module

public import ConLeche.Verify.Frontend.Rounds
public import Std.Sync.Mutex
/- `withPtrEq` is `public` but not `@[expose]`; `sameB_eq` below needs
its body (it is *defined* as `k ()`).  `import all` makes it visible in
this module only. -/
import all Init.Util

/-!
# The rounds parse driver: owner threads (task #329)

The parse at `--jobs` above one.  `jobs` dedicated OWNER threads; the
stream is read forward in chunks of whole lines (each read cut at its
last newline), and the chunks are taken a window at a time, one chunk
per owner.  The owner of a chunk scans it ONCE into ordinary records
(`scanChunk`), kept in its own loop and never handed to another thread,
and computes the chunk's tables over them in rounds
(`ConLeche/Frontend/RoundsWork.lean`): round 0 on its own, then its
deferred lines, round after round, until no owner has any; after each
round it publishes the entries it built.  Then every owner builds a
slice of the window's pages and its chunk's records.

**Why the result is the serial parse's.**  Every entry the rounds
store is GOOD for the index its key names (`Good`,
`ConLeche/Verify/Frontend/Good.lean`): the builder of the line
binding that index, over lookups that answered good entries only.  That
is a property of the round functions, proved once; nothing is tested
again at run time.  The driver carries the window invariant (`WinInv`)
from round to round, from the evidence each owner hands back with its
result (the result is the round function's, on the owner's own chunk
and pending lines; an owner answers for a window only after comparing
the window's tables and counters with its round 0's, the pointer
first, `Cur.is`), and once the window is complete — every deferred
line done, every chunk scanned to its end, the pages built — the
window is one more stretch of the serial parse (`GOK.window`).

**Which bytes.**  The chunks the proof speaks of are the bytes the main
thread read (`bs`), never an owner's reply: an owner echoes the chunk
it holds, and the main thread accepts a result only for the very bytes
it sent that owner (`sameB`, the pointer first).  An owner without a
chunk says so (`ok := false`), and the window falls back.

**Fallback.**  A window whose chunks do not qualify (a malformed line,
an owner without the chunk), whose rounds meet anything unusual (an
index below its table's counter — a stream that does not bind in
increasing order — a line the serial parse would fail at, a round
without progress), or whose records a builder does not yield, is
handed to the serial parse from the state the windows before it reached
(`GOK.reached`, the finished tables as a parse state): the window's
chunks and every chunk read so far by `chunkStep`, the rest of the
stream by the serial loop (`serialLoop`).  That is the serial verdict,
at the serial line.  The bytes after the stream's last newline (a final
line without one) are never a window's: the serial parse applies them
from the state the last window reached (`serialRest`).

**Threads, and what crosses them.**  The main thread coordinates: it
sends every owner its messages (a chunk, round 0, a later round, the
window's finish) and waits for one promise per owner per step — the
barrier between rounds.  A reader thread reads the next window's chunks
while the current one is computed.  What crosses a thread is a chunk's
raw bytes, finished table entries and records, and shallow containers
of them (round arrays, pages, the window, the finished tables) with
bookkeeping words (keys, counters).  A scan record never crosses, nor
does a pending line.

**Memory.**  The table entries — every name, level and expression the
parse builds — and the records are marked persistent by the owner that
built them, before it hands them out (`markEach`, `markSlots`: the
install driver's escape `Runtime.markPersistent`; they live to the end
of the run, but for a window that falls back and names only binders
read, `tests/trust-surface.sh`).  Nothing else is marked: the arrays that hold the entries
and the bookkeeping are dropped and freed when the window, or the
parse, is done with them; the runtime marks such a container
multi-threaded as it crosses, without walking into the persistent
entries.  An object every owner reads (the finished tables, the window)
is read through borrowed references, never counted on the way.  The
marks rely on one invariant: every object reachable from a newly built
entry was built on this thread since its last publication, or is
already persistent (the entries of the finished tables and of earlier
rounds, which the builders read and share).  A chunk table's late slots
hold a filler instead (a constant every owner pushes), which is
skipped: marking an object other threads are counting is not safe.
-/

@[expose] public section

namespace ConLeche.Driver.OwnerParse

open ConLeche ConLeche.Frontend

/-- A promise's value (an owner that dropped its promise is an internal
error). -/
def await {α : Type} [Nonempty α] (p : IO.Promise α) : IO α := do
  match ← IO.wait p.result? with
  | some a => pure a
  | none => throw (IO.userError "rounds parse: an owner dropped a promise")

/-- Equality, the pointer first: `true` at once on the same object; else
the type's own lawful comparison (for the finished tables, entry by
entry with the kernel's pointer-first equalities, `Prior`'s
`LawfulBEq`; for bytes, `memcmp`). -/
@[inline] def sameB {α : Type} [BEq α] [LawfulBEq α] (a b : α) : Bool :=
  withPtrEq a b (fun _ => a == b) (fun h => by simp [h])

theorem sameB_eq {α : Type} [BEq α] [LawfulBEq α] (a b : α) : sameB a b = (a == b) := by rfl

theorem sameB_iff {α : Type} [BEq α] [LawfulBEq α] {a b : α} : sameB a b = true ↔ a = b := by
  rw [sameB_eq, beq_iff_eq]

/-- Mark one value persistent: the install driver's escape
`Runtime.markPersistent`, the identity on the value. -/
def markOne {α : Type} (x : α) : IO Unit := do
  let _ ← unsafe Runtime.markPersistent x

/-- Mark the ELEMENTS of an array persistent, not the array (which is
dropped later), unless `--no-mark-persistent`.  The escape is the
install driver's (`Runtime.markPersistent`, the identity on the value;
the object graph is marked in place and never freed).  An element's
walk stops at children already persistent: the entries it was built
from. -/
def markEach {α : Type} (noMark : Bool) (a : Array α) : IO Unit := do
  if !noMark then
    a.forM markOne

/-- Mark the entries of round 0's slot array persistent: the slots that
hold an entry, not the late slots' fillers (a constant every owner
pushes; marking an object other threads are counting is not safe). -/
def markSlots {α : Type} (noMark : Bool) (d : Array α) (late : ByteArray) : IO Unit := do
  if !noMark then
    for k in [0:d.size] do
      if byteN late k != 1 then
        match d[k]? with
        | some x => markOne x
        | none => pure ()

/-! ## Reading -/

/-- Read up to `m` chunks of about `csz` bytes, each cut at the last
newline of its read (a read without one is carried whole into the
next).  Returns the chunks, the bytes after the last newline read so
far and whether the stream ended.  A chunk is put together here, on the
reader: the bytes the owner scans and the proof speaks of are this
array. -/
partial def readWin (h : IO.FS.Handle) (csz : USize) (m : Nat) (acc : Array ByteArray)
    (pending : ByteArray) (eof : Bool) : IO (Array ByteArray × ByteArray × Bool) := do
  if eof || acc.size ≥ m then return (acc, pending, eof)
  let buf0 ← h.read csz
  if buf0.isEmpty then return (acc, pending, true)
  else
    match lastNewlineBelow buf0 buf0.size with
    | none => readWin h csz m acc (pending ++ buf0) false
    | some k =>
      let b := if pending.isEmpty then buf0.extract 0 (k + 1)
        else pending ++ buf0.extract 0 (k + 1)
      readWin h csz m (acc.push b) (buf0.extract (k + 1) buf0.size) false

/-- A window being read on the reader thread. -/
abbrev RdT := Task (Except IO.Error (Array ByteArray × ByteArray × Bool))

def spawnRead (h : IO.FS.Handle) (csz : USize) (m : Nat) (pending : ByteArray) (eof : Bool) :
    IO RdT :=
  IO.asTask (prio := .dedicated) (readWin h csz m #[] pending eof)

def awaitRd (t : RdT) : IO (Array ByteArray × ByteArray × Bool) := do
  match ← IO.wait t with
  | .ok r => pure r
  | .error e => throw e

/-! ## Messages and results

An owner's result for chunk `c` comes with the bytes `b` of the chunk it
holds (echoed for the main thread to compare with what it sent) and the
evidence `Q c b v` that its value `v` is the round function's on that
chunk's records (`scanChunk b`) and, for a later round, on pending lines
the owner holds (`PendOK`). -/

/-- An owner's result for chunk `c`: `ok` is its word that it held the
chunk (bytes `b`), computed `v` on it and met nothing unusual. -/
structure ORes (β : Type) (Q : Nat → ByteArray → β → Prop) where
  c : Nat
  b : ByteArray
  ok : Bool
  v : β
  h : ok = true → Q c b v

/-- No result: the window falls back. -/
def ORes.none [Inhabited β] {Q : Nat → ByteArray → β → Prop} (c : Nat) : ORes β Q :=
  ⟨c, .empty, false, default, by simp⟩

instance [Inhabited β] {Q : Nat → ByteArray → β → Prop} : Nonempty (ORes β Q) := ⟨.none 0⟩

instance : Inhabited R0 :=
  ⟨⟨⟨#[], .empty, #[], 0, 0, #[], 0⟩, ⟨#[], .empty, #[], 0, 0, #[], 0⟩,
    ⟨#[], .empty, #[], 0, 0, #[], 0⟩, #[], 0, true⟩⟩

instance : Inhabited RR :=
  ⟨⟨#[], .empty, #[], .empty, #[], .empty, #[], #[], #[], #[], 0, true⟩⟩

/-- Round 0's result for chunk `c`: its tables (the pending lines stay
on the owner) and its line count; beside them, its pending count. -/
def R0Q (P : Prior) (c0 : Ctr) (c : Nat) (b : ByteArray) (x : R0 × Nat × Nat) : Prop :=
  x.1 = { round0 P c0 c (recsOf b) with pend := #[] } ∧ x.2.2 = (recsOf b).size

/-- A later round's result for chunk `c`: its late entries; beside them,
its pending count. -/
def RRQ (P : Prior) (W : Win) (c : Nat) (b : ByteArray) (x : RR × Nat) : Prop :=
  RRok P W c b x.1

/-- A message to an owner. -/
inductive Msg where
  /-- the owner's chunk of the next window -/
  | chunk (b : ByteArray)
  /-- round 0 of chunk `c` of the window starting at `c0` -/
  | start (P : Prior) (c0 : Ctr) (c : Nat) (out : IO.Promise (ORes (R0 × Nat × Nat) (R0Q P c0)))
  /-- a later round of the owner's chunk -/
  | round (P : Prior) (W : Win) (out : IO.Promise (ORes (RR × Nat) (RRQ P W)))
  /-- slice `c` of `m` of the window's pages, and chunk `c`'s records -/
  | finish (P : Prior) (W : Win) (m c : Nat) (out : IO.Promise (ORes FinPart (FinOK P W m)))
  | stop

/-- An owner's mailbox. -/
structure Box where
  lock : Std.BaseMutex
  cv : Std.Condvar
  q : IO.Ref (Std.Queue Msg)

def Box.new : IO Box := do
  return ⟨← Std.BaseMutex.new, ← Std.Condvar.new, ← IO.mkRef ∅⟩

def Box.send (b : Box) (m : Msg) : IO Unit := do
  b.lock.lock
  b.q.modify (·.enqueue m)
  b.lock.unlock
  b.cv.notifyOne

partial def Box.recvLocked (b : Box) : IO Msg := do
  match ← b.q.modifyGet fun q => match q.dequeue? with
      | some (m, q') => (some m, q')
      | none => (none, q) with
  | some m => return m
  | none => b.cv.wait b.lock; b.recvLocked

def Box.recv (b : Box) : IO Msg := do
  b.lock.lock
  let m ← b.recvLocked
  b.lock.unlock
  return m

/-- Send to owner `i` (there is one per chunk of a window; a missing
one is the driver's error). -/
def sendTo (bxs : Array Box) (i : Nat) (m : Msg) : IO Unit :=
  match bxs[i]? with
  | some b => b.send m
  | none => throw (IO.userError s!"rounds parse: no owner {i}")

/-! ## The owner -/

/-- A chunk and its records, the owner's own. -/
structure Mine where
  b : ByteArray
  sc : ScannedChunk
  h : sc = scanChunk b

/-- The late entries a later round copied from (the window's), kept by
the owner until its next round (or the window's finish), so that the
main thread, which replaces the window, does not free them: freeing an
array visits every entry, and the main thread's time is everyone's
(task #329, lane GOOD: up to 0.3 s on NS at 32 jobs). -/
structure Keep where
  n : Array Name
  l : Array Level
  e : Array Expr

/-- Nothing kept. -/
def Keep.none : Keep := ⟨#[], #[], #[]⟩

/-- What an owner holds of its chunk's tables so that it, not the main
thread, frees them: round 0's slot arrays and the latest late entries.
The window holds them too; the owner keeps its share until its first
message after the next window's round 0, when the main thread has let
the window go, so that each owner frees its own chunk's arrays. -/
structure Hold where
  tn : TB Name
  tl : TB Level
  te : TB Expr
  out : Keep

/-- Nothing held. -/
def Hold.none : Hold := ⟨⟨#[], .empty, #[], 0, 0, #[], 0⟩, ⟨#[], .empty, #[], 0, 0, #[], 0⟩,
  ⟨#[], .empty, #[], 0, 0, #[], 0⟩, .none⟩

/-- The chunk of the current window: its records, the window it is
chunk `c` of (round 0's tables `P` and counters `c0`) and its pending
lines. -/
structure Cur where
  b : ByteArray
  sc : ScannedChunk
  hsc : sc = scanChunk b
  P : Prior
  c0 : Ctr
  c : Nat
  pend : Array Pend
  hp : PendOK P c0 c sc.recs pend
  /-- the late entries the last round copied from -/
  inp : Keep := .none
  /-- this window's tables, held (`Hold`) -/
  hold : Hold := .none
  /-- the window before's tables, held until the first message after
  this window's round 0 -/
  prevHold : Hold := .none

/-- Is the owner's chunk one of the window of `P` starting at `c0`?  The
driver sends the very tables round 0 was sent, so the pointer test
answers; behind it is one pass over the tables (`Prior`'s `LawfulBEq`). -/
@[inline] def Cur.is (x : Cur) (P : Prior) (c0 : Ctr) : Bool :=
  x.c0.beq c0 && sameB x.P P

theorem Cur.is_eq {x : Cur} {P c0} (h : x.is P c0 = true) : x.c0 = c0 ∧ x.P = P := by
  simp only [Cur.is, Bool.and_eq_true, sameB_iff] at h
  exact ⟨Ctr.beq_iff.mp h.1, h.2⟩

/-- **The owner's loop.**  Its state is plain arguments: the chunk of
the current window (`cur`, once its round 0 ran), of the next (`nxt`,
scanned), and the tables of the window it finished last (`fin`), held
until its next window's round 0 ran. -/
partial def ownerLoop (bx : Box) (noMark : Bool) (cur : Option Cur) (nxt : Option Mine)
    (fin : Hold) : IO Unit := do
  match ← bx.recv with
  | .stop => return
  | .chunk b =>
    ownerLoop bx noMark cur (some ⟨b, scanChunkCap (b.size / 32) b, scanChunkCap_eq _ _⟩) fin
  | .start P c0 c out =>
    match nxt with
    | some ⟨b, sc, hx⟩ =>
      let o := round0 P c0 c sc.recs
      markSlots noMark o.n.d o.n.late; markSlots noMark o.l.d o.l.late
      markSlots noMark o.e.d o.e.late
      out.resolve ⟨c, b, true, ({ o with pend := #[] }, o.pend.size, sc.recs.size),
        by intro _; subst hx; exact ⟨rfl, rfl⟩⟩
      -- the next window's chunk is now the current one
      ownerLoop bx noMark (some ⟨b, sc, hx, P, c0, c, o.pend, pendOK_round0 _ _ _ _,
        .none, ⟨o.n, o.l, o.e, .none⟩, fin⟩) none .none
    | none =>
      -- no chunk: the window falls back
      out.resolve (.none c)
      ownerLoop bx noMark none none fin
  | .round P W out =>
    match cur with
    | some x =>
      if hi : x.is P W.c0 then
        let o := roundR P W x.c x.sc.recs x.pend
        markEach noMark o.fn; markEach noMark o.fl; markEach noMark o.fe
        out.resolve ⟨x.c, x.b, !o.bad,
          ({ o with pend := #[], fn := #[], fl := #[], fe := #[] }, o.pend.size), by
            intro hb
            obtain ⟨h1, h2⟩ := Cur.is_eq hi
            have hr : recsOf x.b = x.sc.recs := by rw [recsOf, ← x.hsc]
            refine ⟨x.pend, ?_, ?_, ?_⟩
            · rw [hr, ← h1, ← h2]; exact x.hp
            · rw [hr]; rfl
            · rw [hr]; simpa using hb⟩
        let inp : Keep := ⟨(W.n.tabs.getD x.c .blank).lv, (W.l.tabs.getD x.c .blank).lv,
          (W.e.tabs.getD x.c .blank).lv⟩
        let hold : Hold := { x.hold with out := ⟨o.vn, o.vl, o.ve⟩ }
        let x' : Cur := { x with
          pend := o.pend
          hp := x.hp.afterRound P W
          inp := inp
          hold := hold
          prevHold := .none }
        ownerLoop bx noMark (some x') nxt fin
      else
        out.resolve (.none x.c)
        ownerLoop bx noMark cur nxt fin
    | none =>
      out.resolve (.none 0)
      ownerLoop bx noMark cur nxt fin
  | .finish P W m c out =>
    let pn := finSlice P.n W.n m c
    let pl := finSlice P.l W.l m c
    let pe := finSlice P.e W.e m c
    match cur with
    | some x =>
      if x.is P W.c0 && x.c == c then
        let ds := chunkDecls P W c x.sc.recs
        if let some d := ds then markEach noMark d
        out.resolve ⟨c, x.b, scanEnds x.b x.sc && W.fullAt c && ds.isSome,
          ⟨pn, pl, pe, ds.getD #[]⟩, by
            intro h
            simp only [Bool.and_eq_true] at h
            obtain ⟨⟨he, hf⟩, hd⟩ := h
            have hr : recsOf x.b = x.sc.recs := by rw [recsOf, ← x.hsc]
            refine ⟨rfl, rfl, rfl, by rw [← x.hsc]; exact he, hf, ?_⟩
            rw [hr]
            show ds = some (ds.getD #[])
            obtain ⟨d, hd⟩ := Option.isSome_iff_exists.mp hd
            rw [hd]; rfl⟩
      else out.resolve (.none c)
    | none => out.resolve (.none c)
    -- this window's tables, held into the next window
    ownerLoop bx noMark none nxt (match cur with | some x => x.hold | none => .none)

/-! ## The coordinator -/

/-- The driver's settings and counters. -/
structure Cfg where
  /-- bytes per read (about a chunk) -/
  csz : USize
  noMark : Bool
  /-- windows that fell back (for the tests) -/
  fallbacks : IO.Ref Nat
  /-- windows taken through the rounds, and their later rounds -/
  windows : IO.Ref Nat
  rounds : IO.Ref Nat

/-- Chunks applied by the serial parse, one after the other. -/
def serialChunks (st : StateD) (carry : ByteArray) (lineNo total : Nat)
    (hr : Reached st carry lineNo total) : List ByteArray →
    Except ParseOutcome (Σ' (st : StateD) (carry : ByteArray) (lineNo total : Nat),
      Reached st carry lineNo total)
  | [] => .ok ⟨st, carry, lineNo, total, hr⟩
  | x :: xs =>
    match hs : chunkStep st carry lineNo total x with
    | .error e => .error ⟨.error e, hr.error hs⟩
    | .ok (st', carry', lineNo', total') =>
      serialChunks st' carry' lineNo' total' (hr.step hs) xs

/-- Stop every owner. -/
def stopAll (bxs : Array Box) : IO Unit :=
  bxs.forM (·.send .stop)

/-- **The serial parse from where the windows left off**: from the
state the windows before reached (`GOK.reached`), the chunks given by
the serial parse, then the rest of the stream by the serial loop. -/
def serialRest (h : IO.FS.Handle) (g : GSt) (hg : GOK g) (xs : List ByteArray) :
    IO ParseOutcome := do
  let st := (g.P.toState g.c g.ds).markLinear
  have hr : Reached st .empty g.lineNo g.total := by
    simp only [st, StateD.markLinear_eq]; exact hg.reached
  match serialChunks st .empty g.lineNo g.total hr xs with
  | .error r => return r
  | .ok ⟨st, carry, lineNo, total, hr⟩ => serialLoop h chunkSize st carry lineNo total hr

/-- **The fallback**: the owners stopped, every chunk read so far and
the bytes after them to the serial parse (`serialRest`). -/
def fallback (h : IO.FS.Handle) (bxs : Array Box) (cfg : Cfg) (g : GSt) (hg : GOK g)
    (xs : List ByteArray) (pending : ByteArray) : IO ParseOutcome := do
  stopAll bxs
  cfg.fallbacks.modify (· + 1)
  serialRest h g hg (if pending.isEmpty then xs else xs ++ [pending])

/-- One more value on a checked prefix. -/
theorem gather_push {Q : Nat → ByteArray → β → Prop} {bs : Array ByteArray} {acc : Array β}
    {v : β} (hacc : ∀ i (h : i < acc.size) (hb : i < bs.size), Q i bs[i] acc[i])
    (hv : ∀ hb : acc.size < bs.size, Q acc.size bs[acc.size] v) :
    ∀ i (h : i < (acc.push v).size) (hb : i < bs.size), Q i bs[i] (acc.push v)[i] := by
  intro i hi hb
  rw [Array.getElem_push]
  split
  · exact hacc i ‹_› hb
  · have : i = acc.size := by simp at hi; omega
    subst this; exact hv hb

/-- **The owners' results, checked** chunk by chunk (from chunk
`acc.size`): each from an owner that answered for its chunk, on the
very bytes the main thread read (`sameB`, the pointer first); a chunk
no owner was asked about takes `dflt`'s value, if it has one.  One
value per chunk read, with its evidence. -/
def gather {β : Type} {Q : Nat → ByteArray → β → Prop} (bs : Array ByteArray)
    (rs : Array (Option (ORes β Q))) (dflt : (i : Nat) → Option {v : β // ∀ b, Q i b v})
    (acc : Array β) (hacc : ∀ i (h : i < acc.size) (hb : i < bs.size), Q i bs[i] acc[i]) :
    Option {vs : Array β // vs.size = bs.size ∧
      ∀ i (h : i < vs.size) (hb : i < bs.size), Q i bs[i] vs[i]} :=
  if hc : acc.size < rs.size then
    match rs[acc.size] with
    | none =>
      match dflt acc.size with
      | some ⟨v, hv⟩ => gather bs rs dflt (acc.push v) (gather_push hacc fun _ => hv _)
      | none => none
    | some x =>
      if hx : x.ok && x.c == acc.size &&
          (match bs[acc.size]? with | some b => sameB x.b b | none => false) then
        gather bs rs dflt (acc.push x.v) (gather_push hacc fun hb => by
          simp only [Bool.and_eq_true, beq_iff_eq, Array.getElem?_eq_getElem hb, sameB_iff] at hx
          obtain ⟨⟨hok, hcc⟩, hbb⟩ := hx
          have := x.h hok
          rw [hcc, hbb] at this; exact this)
      else none
  else if h : acc.size = bs.size then some ⟨acc, h, hacc⟩ else none
termination_by rs.size - acc.size

/-- What a later round leaves of a chunk with nothing pending. -/
def idleRR (W : Win) (c : Nat) : RR :=
  ⟨(W.n.tabs.getD c .blank).lv, (W.n.tabs.getD c .blank).ldone,
   (W.l.tabs.getD c .blank).lv, (W.l.tabs.getD c .blank).ldone,
   (W.e.tabs.getD c .blank).lv, (W.e.tabs.getD c .blank).ldone, #[], #[], #[], #[], 0, false⟩

theorem idleRR_ok (P : Prior) (W : Win) (c : Nat) (b : ByteArray) : RRok P W c b (idleRR W c) := by
  refine ⟨#[], PendOK.empty _ _ _ _, ?_, ?_⟩ <;> simp [roundR, idleRR, RR.lates]

/-- **The later rounds of a window**, on the owners of the chunks with
pending lines, until nothing is pending: `none` on an anomaly or a
round without progress (every round binds a pending line, so the
rounds end); else the window, its invariant and the number of rounds. -/
partial def roundsLoop (bxs : Array Box) (P : Prior) (bs : Array ByteArray) (W : Win)
    (hW : WinInv P bs.toList W) (nps : Array Nat) (r : Nat) :
    IO (Option ((W : Win) ×' WinInv P bs.toList W ×' Nat)) := do
  if nps.all (· == 0) then return some ⟨W, hW, r⟩
  let mut ps : Array (Option (IO.Promise (ORes (RR × Nat) (RRQ P W)))) := Array.mkEmpty W.nc
  for c in [0:W.nc] do
    if nps.getD c 0 == 0 then ps := ps.push none
    else
      let p ← IO.Promise.new
      sendTo bxs c (.round P W p)
      ps := ps.push (some p)
  let mut rs : Array (Option (ORes (RR × Nat) (RRQ P W))) := Array.mkEmpty W.nc
  for p in ps do
    match p with
    | some p => rs := rs.push (some (← await p))
    | none => rs := rs.push none
  match gather bs rs (fun c => some ⟨(idleRR W c, 0), fun b => idleRR_ok P W c b⟩) #[]
      (fun _ h => absurd h (Nat.not_lt_zero _)) with
  | none => return none
  | some ⟨vs, _, hq⟩ =>
    let rrs := vs.map (·.1)
    if rrs.foldl (fun a o => a + o.prog) 0 == 0 then return none
    if hn : rrs.size = W.nc then
      roundsLoop bxs P bs (W.setLate rrs) (hW.setLate rrs hn fun c h hb => by
        have := hq c (by simpa [rrs] using h) (by simpa using hb)
        simpa [rrs, RRQ] using this) (vs.map (·.2)) (r + 1)
    else return none

/-- **The rounds parse of a stream**, window after window, carrying
`GOK`.  `bs` is the window whose chunks the owners hold (scanned or
being scanned), `rd` the read of the window after it. -/
partial def streamLoop (bxs : Array Box) (h : IO.FS.Handle) (cfg : Cfg) (g : GSt) (hg : GOK g)
    (bs : Array ByteArray) (rd : RdT) : IO ParseOutcome := do
  let m := bs.size
  if m == 0 then
    -- the stream's end: the bytes after its last newline, if any, are
    -- its final line, for the serial parse.  The read after an empty
    -- window has no chunks (`readWin` returns fewer than asked only at
    -- the stream's end); if it ever had, they go to the serial parse
    -- too, never dropped.
    let (nbs, pending, _) ← awaitRd rd
    stopAll bxs
    if nbs.isEmpty && pending.isEmpty then return ⟨.ok ⟨g.ds⟩, hg.finish⟩
    else return ← serialRest h g hg (if pending.isEmpty then nbs.toList else nbs.toList ++ [pending])
  let fall := fun (_ : Unit) => do
    let (nbs, pending, _) ← awaitRd rd
    fallback h bxs cfg g hg (bs.toList ++ nbs.toList) pending
  -- round 0 of this window, on the owners, from the tables after the window before
  let P := g.P
  let c0 := g.c
  let mut r0s : Array (IO.Promise (ORes (R0 × Nat × Nat) (R0Q P c0))) := Array.mkEmpty m
  for i in [0:m] do
    let p ← IO.Promise.new
    sendTo bxs i (.start P c0 i p)
    r0s := r0s.push p
  let os ← r0s.mapM fun p => return some (← await p)
  let some ⟨vs, hsz, hq⟩ := gather bs os (fun _ => none) #[]
      (fun _ h => absurd h (Nat.not_lt_zero _)) | return ← fall ()
  let os' := vs.map (·.1)
  have hos : ∀ c (h : c < bs.toList.length), os'[c]'(by simp [os'] at h ⊢; omega) =
      { round0 P c0 c (recsOf bs.toList[c]) with pend := #[] } := by
    intro c hc
    have := (hq c (by simp at hc; omega) (by simpa using hc)).1
    simpa [os'] using this
  -- the window's lines
  let nl := (vs.toList.map (·.2.2)).sum
  have hnl : nl = (bs.toList.map fun b => (recsOf b).size).sum := by
    simp only [nl]
    congr 1
    apply List.ext_getElem (by simp [hsz])
    intro c h1 h2
    simp only [List.getElem_map, Array.getElem_toList]
    exact (hq c (by simpa using h1) (by simpa using h2)).2
  let W := Win.ofRound0 c0 os'
  if ha : after0 W os' then
    have hW : WinInv P bs.toList W := winInv_ofRound0 (by simp [os', hsz]) hos ha
    let some ⟨W, hW, nr⟩ ← roundsLoop bxs P bs W hW (vs.map (·.2.1)) 0 | return ← fall ()
    cfg.windows.modify (· + 1); cfg.rounds.modify (· + nr)
    -- the pages after the window, a slice per owner, and its records
    let mut fps : Array (IO.Promise (ORes FinPart (FinOK P W m))) := Array.mkEmpty m
    for j in [0:m] do
      let p ← IO.Promise.new
      sendTo bxs j (.finish P W m j p)
      fps := fps.push p
    -- meanwhile the next window's chunks go to their owners, and the
    -- window after it is read
    let (nbs, pending, eof) ← awaitRd rd
    let rd' ← spawnRead h cfg.csz bxs.size pending eof
    for j in [0:nbs.size] do
      sendTo bxs j (.chunk nbs[j]!)
    let fs ← fps.mapM fun p => return some (← await p)
    let fallN := fun (_ : Unit) => do
      let (nbs', pending', _) ← awaitRd rd'
      fallback h bxs cfg g hg (bs.toList ++ nbs.toList ++ nbs'.toList) pending'
    let some ⟨ps, hpsz, hpq⟩ := gather bs fs (fun _ => none) #[]
        (fun _ h => absurd h (Nat.not_lt_zero _)) | fallN ()
    let tot := (bs.toList.map ByteArray.size).sum
    if hm : 0 < m ∧ W.c0 = g.c ∧ g.total + tot < USize.size then
      have hm' : ps.size = bs.toList.length := by simpa using hpsz
      have hps : ∀ c (h : c < ps.size) (hb : c < bs.toList.length),
          FinOK g.P W ps.size c bs.toList[c] ps[c] := by
        intro c h hb; rw [hpsz]; simpa using hpq c h (by simpa using hb)
      have hg' := GOK.window hg hW hm.2.1 hm' (by simpa [m] using hm.1) hps hm.2.2
      let g' : GSt := ⟨g.P.setFrom W (joinN ps) (joinL ps) (joinE ps), W.cEnd,
        g.ds ++ joinD ps, g.lineNo + nl, g.total + tot⟩
      streamLoop bxs h cfg g' (by simp only [g', hnl, tot]; exact hg') nbs rd'
    else fallN ()
  else fall ()

/-- **The rounds parse of a file** on `jobs` owners, chunks of about
`csz` bytes; with the number of windows that fell back, the windows
taken through the rounds and their later rounds. -/
def parseExportStreamOInfo (path : System.FilePath) (jobs : Nat) (csz : USize)
    (noMark : Bool) : IO (ParseOutcome × Nat × Nat × Nat) := do
  let h ← IO.FS.Handle.mk path .read
  let cfg : Cfg := ⟨csz, noMark, ← IO.mkRef 0, ← IO.mkRef 0, ← IO.mkRef 0⟩
  let mut bxs : Array Box := #[]
  for _ in [0:max 1 jobs] do
    let b ← Box.new
    let _ ← IO.asTask (prio := .dedicated) (ownerLoop b noMark none none .none)
    bxs := bxs.push b
  -- the owners are stopped however the parse ends: an IO error (a read
  -- that fails, a dropped promise) propagates instead of leaving them
  -- blocked, which would keep the process from exiting
  let r ← tryFinally (do
      let (bs, pending, eof) ← readWin h csz bxs.size #[] .empty false
      for i in [0:bs.size] do
        sendTo bxs i (.chunk bs[i]!)
      let rd ← spawnRead h csz bxs.size pending eof
      streamLoop bxs h cfg .init GOK.init bs rd)
    (stopAll bxs)
  return (r, ← cfg.fallbacks.get, ← cfg.windows.get, ← cfg.rounds.get)

/-- **The rounds parse of a file.** -/
def parseExportStreamO (path : System.FilePath) (jobs : Nat) (csz : USize) (noMark : Bool) :
    IO ParseOutcome :=
  return (← parseExportStreamOInfo path jobs csz noMark).1

end ConLeche.Driver.OwnerParse
