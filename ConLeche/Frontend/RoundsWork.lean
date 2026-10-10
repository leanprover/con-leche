module

public import ConLeche.Frontend.Rounds

@[expose] public section

/-!
# The rounds parse: the rounds (task #329)

How the rounds parse computes a window's tables and records.  Nothing
here tests what it computed afterwards: why the result is the serial
parse's is proved about these functions
(`ConLeche/Verify/Frontend/Rounds.lean`), and a window whose rounds go
wrong in a way the proof does not cover — a line that does not fit the
counters, a line the serial parse would fail at, a window that does not
finish — is handed to the serial parse.

**Windows and rounds.**  The chunks are taken a window at a time.  In
round 0 every chunk of the window applies its lines in order, on the
thread that owns it (`ConLeche/Driver/OwnerParse.lean`), reading the
finished tables before the window and its own entries; a line that
reads an entry of another chunk of the window is deferred.  In each
later round every chunk applies its deferred lines, reading the other
chunks' entries as of the end of the round before.  Rounds repeat until
no line is deferred; then every owner builds a slice of the window's
pages (`pageOf`) and its chunk's declarations (`chunkDecls`), reading
the window's tables.  The DAG of the stream is shallow, so a window
takes a handful of rounds.

**Keys.**  The `k`-th line of a table in a chunk binds `first + k` when
the chunk is dense (lean4export's case), else `ids[k]`; `idx` finds
`k` back (arithmetic, or a binary search).
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## Keys: the indices a chunk binds -/

/-- The indices one chunk binds in one table, in order. -/
structure Keys where
  first : Nat
  cnt : Nat
  /-- empty when the chunk is dense: the indices are `first, first + 1, …` -/
  ids : Array Nat
  deriving Inhabited

/-- The `k`-th index. -/
@[inline] def Keys.keyOf (K : @& Keys) (k : Nat) : Nat :=
  if K.ids.isEmpty then K.first + k else K.ids.getD k 0

/-- The first position in `ids[lo, hi)` whose index is at least `j`. -/
def keysFind (ids : @& Array Nat) (j lo hi : Nat) : Nat :=
  if lo < hi then
    let mid := (lo + hi) / 2
    if ids.getD mid 0 < j then keysFind ids j (mid + 1) hi else keysFind ids j lo mid
  else lo
termination_by hi - lo

/-- The position of index `j`, if the chunk binds it. -/
@[inline] def Keys.idx (K : @& Keys) (j : Nat) : Option Nat :=
  if K.ids.isEmpty then
    if K.first ≤ j ∧ j < K.first + K.cnt then some (j - K.first) else none
  else
    let k := keysFind K.ids j 0 K.ids.size
    if k < K.cnt ∧ K.ids.getD k 0 == j then some k else none

/-! ## A chunk's table

Slot `k` of a chunk's table is the entry of the chunk's `k`-th line of
that table.  Round 0 builds `d0`, every slot at its position: the
entry, or — where the line was deferred — a filler, with the slot's
byte in `late` set and its late number `s` in `ls`; late entry `s`,
`lv[s]` (and `ldone[s]` set), is written by the later round that
computes it.  `d0`, `late` and `ls` are never written again (the other
chunks read them); `lv`/`ldone`, as small as the deferred lines, are
written by the chunk's owner (a copy per round: the other chunks read
the round before's).  Entries are kept unboxed (a box per entry is 16
bytes for every entry of the run), so a filler is needed where there is
none yet (`Inhabited`); the bytes say where.  `ls` is a word per slot,
freed with the window. -/

/-- One table of one chunk. -/
structure CTab (α : Type) where
  d0 : Array α
  /-- `1` at a late slot -/
  late : ByteArray
  /-- a late slot's late number -/
  ls : Array Nat
  lv : Array α
  /-- `1` once late entry `s` is done -/
  ldone : ByteArray

/-- Byte `i` of a byte array (`0` past its end). -/
@[inline] def byteN (a : @& ByteArray) (i : Nat) : UInt8 :=
  if h : i < a.size then a[i] else 0

/-- Late entry `s`, if done. -/
@[inline] def lateVal (lv : @& Array α) (ldone : @& ByteArray) (s : Nat) : Option α :=
  if byteN ldone s == 1 then
    if h : s < lv.size then some lv[s] else none
  else none

/-- Slot `k` given apart (round 0's part and the late entries), if done. -/
@[inline] def slotGet (d0 : @& Array α) (late : @& ByteArray) (ls : @& Array Nat)
    (lv : @& Array α) (ldone : @& ByteArray) (k : Nat) : Option α :=
  if h : k < d0.size then
    if byteN late k == 1 then lateVal lv ldone (ls.getD k 0) else some d0[k]
  else none

/-- Slot `k`, if done. -/
@[inline] def CTab.get (t : @& CTab α) (k : Nat) : Option α :=
  slotGet t.d0 t.late t.ls t.lv t.ldone k

/-- Is every deferred line's entry done? -/
def CTab.full (t : @& CTab α) : Bool :=
  t.ldone.size == t.lv.size && t.ldone.data.all (· == 1)

/-! ## Segments: the chunks of a table, side by side

Chunk `c` covers the indices `[starts[c], starts[c + 1])`. -/

/-- A table split into chunks. -/
structure Seg (α : Type) where
  tabs : Array (CTab α)
  keys : Array Keys
  starts : Array Nat

/-- The last chunk whose start is at most `j`, between `lo` and `hi`
(a guess: `Seg.get` checks it). -/
def Seg.findGo (st : @& Array Nat) (j lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    if st.getD mid 0 ≤ j then Seg.findGo st j mid hi else Seg.findGo st j lo mid
  else lo
termination_by hi - lo

/-- Slot `k` of chunk `e`'s table. -/
@[inline] def Seg.getAt (s : @& Seg α) (e k : Nat) : Option α :=
  if h : e < s.tabs.size then s.tabs[e].get k else none

/-- Chunk `e`'s entry for index `j`. -/
@[inline] def Seg.atC (s : @& Seg α) (e j : Nat) : Option α :=
  if h : e < s.keys.size then
    match s.keys[e].idx j with
    | some k => s.getAt e k
    | none => none
  else none

/-- Entry `j`, looked up chunk by chunk (the specification; what runs
when the guess is wrong, which it never is on monotone starts). -/
@[noinline] def Seg.getSlow (s : @& Seg α) (j : Nat) : Option α :=
  go 0
where
  go (c : Nat) : Option α :=
    if c < s.tabs.size then
      if s.starts.getD c 0 ≤ j ∧ j < s.starts.getD (c + 1) 0 then s.atC c j
      else go (c + 1)
    else none
  termination_by s.tabs.size - c

/-- Entry `j`: the chunk the binary search finds, if its range holds
`j`. -/
@[inline] def Seg.get (s : @& Seg α) (j : Nat) : Option α :=
  let c := Seg.findGo s.starts j 0 s.tabs.size
  if c < s.tabs.size ∧ s.starts.getD c 0 ≤ j ∧ j < s.starts.getD (c + 1) 0 then s.atC c j
  else Seg.getSlow s j

/-- The window: its chunks' tables, where its tables start, and how
many chunks it has. -/
structure Win where
  c0 : Ctr
  n : Seg Name
  l : Seg Level
  e : Seg Expr
  nc : Nat

/-! ## The lookups of a round

A lookup answers an entry, or "not yet" (`defer`: the entry is another
line's of the window, not done yet — with the slot it waits for, when
known), or "never" (`fail`: the serial parse would fail here, or the
window is not one the rounds handle). -/

/-- A table, named. -/
inductive WT where
  | none
  | name
  | level
  | expr
  deriving Inhabited

/-- A rounds lookup that does not answer. -/
inductive Miss where
  /-- not done yet: slot `k` of table `t` of chunk `c` (`t = .none`: not
  known which) -/
  | defer (c k : Nat) (t : WT)
  | fail

/-! ### Round 0

Round 0 of a chunk needs nothing of the window's other chunks; it runs
on the chunk's owner, over the records the owner scanned the chunk
into.  What it cannot know is where the chunk's ranges start (one past
the last index the chunk before it binds): before the chunk's first
line of a table it reads in that table only what lies below the
window. -/

/-- A table of a chunk being built in round 0: its slots, which are
late and their late numbers, how many are, its keys (`first`, `ids`)
and one past the last index it bound. -/
structure TB (α : Type) where
  d : Array α
  late : ByteArray
  ls : Array Nat
  np : Nat
  first : Nat
  ids : Array Nat
  b : Nat

/-- The keys after one more line binding `id`, at `n` lines so far. -/
@[inline] def keysPush (n first b : Nat) (ids : Array Nat) (id : Nat) : Array Nat :=
  if n == 0 then ids
  else if ids.isEmpty then
    if id == b then ids else ((Array.range n).map (first + ·)).push id
  else ids.push id

/-- The keys of a table builder. -/
@[inline] def TB.keys (t : TB α) : Keys := ⟨t.first, t.d.size, t.ids⟩

/-- Round 0's lookup in one table (slots `d`, late bytes `lt`, first
index `f`, keys `ids`, counter `b`): below the window the prior pages;
the chunk's own entries from its first index below its counter;
anything else in the window waits (another chunk, or the chunk's start
not known yet). -/
@[inline] def r0Look (pg : @& Pages α) (c0t c : Nat) (t : WT) (d : @& Array α)
    (lt : @& ByteArray) (f : Nat) (ids : @& Array Nat) (b j : Nat) : Except Miss α :=
  if j < c0t then
    match pg.get j with
    | some x => .ok x
    | none => .error .fail
  else if d.size == 0 then .error (.defer 0 0 .none)
  else if j < b then
    if f ≤ j then
      let k := if ids.isEmpty then j - f else keysFind ids j 0 ids.size
      if h : k < d.size then
        if ids.isEmpty || ids.getD k 0 == j then
          if byteN lt k == 1 then .error (.defer c k t) else .ok d[k]
        else .error .fail
      else .error .fail
    else .error (.defer 0 0 .none)
  else .error .fail

/-- A deferred line: its record's position in the chunk, the lines of
each table before it in the chunk (its counters, once the chunk's start
is known; for its own table, its slot), its late entry number, and what
it waits for. -/
structure Pend where
  pos : Nat
  kn : Nat
  kl : Nat
  ke : Nat
  s : Nat
  wc : Nat
  wk : Nat
  wt : WT

/-- Round 0's result for one chunk. -/
structure R0 where
  n : TB Name
  l : TB Level
  e : TB Expr
  pend : Array Pend
  prog : Nat
  bad : Bool

/-- Round 0 of chunk `c` of a window starting at `c0`: the records `d`
from position `p`, in order.  Each table's builder is passed as plain
arguments — its slots, late bytes, late numbers, late count, first
index, keys and counter — not as a record: a record rebuilt at every
line is a fresh allocation (the compiler does not reuse it here).  A
line's keys are updated in the recursive call's arguments, after its
builder has read them (an update before would keep two versions alive,
and the push would copy). -/
def round0Go (P : @& Prior) (c0 : Ctr) (c : Nat) (d : @& Array LineRec) (p : Nat)
    (dn : Array Name) (ltn : ByteArray) (lsn : Array Nat) (npn fn : Nat) (idn : Array Nat)
    (bn : Nat)
    (dl : Array Level) (ltl : ByteArray) (lsl : Array Nat) (npl fl : Nat) (idl : Array Nat)
    (bl : Nat)
    (de : Array Expr) (lte : ByteArray) (lse : Array Nat) (npe fe : Nat) (ide : Array Nat)
    (be : Nat)
    (pend : Array Pend) (prog : Nat) : R0 :=
  if h : p < d.size then
    match d[p] with
    | .name id x =>
      if dn.size != 0 && id < bn then
        ⟨⟨dn, ltn, lsn, npn, fn, idn, bn⟩, ⟨dl, ltl, lsl, npl, fl, idl, bl⟩,
         ⟨de, lte, lse, npe, fe, ide, be⟩, pend, prog, true⟩
      else
        let n := dn.size
        match nameOfF (r0Look P.n c0.n c .name dn ltn fn idn bn)
            (r0Look P.l c0.l c .level dl ltl fl idl bl) (r0Look P.e c0.e c .expr de lte fe ide be)
            x with
        | .ok v => round0Go P c0 c d (p + 1) (dn.push v) (ltn.push 0) (lsn.push 0) npn (if n == 0 then id else fn) (keysPush n fn bn idn id)
            (id + 1) dl ltl lsl npl fl idl bl de lte lse npe fe ide be pend (prog + 1)
        | .error (.defer wc wk wt) =>
          let pe : Pend := ⟨p, n, dl.size, de.size, npn, wc, wk, wt⟩
          round0Go P c0 c d (p + 1) (dn.push default) (ltn.push 1) (lsn.push npn) (npn + 1) (if n == 0 then id else fn)
            (keysPush n fn bn idn id) (id + 1) dl ltl lsl npl fl idl bl de lte lse npe fe ide be (pend.push pe) prog
        | .error .fail =>
          ⟨⟨dn, ltn, lsn, npn, fn, idn, bn⟩, ⟨dl, ltl, lsl, npl, fl, idl, bl⟩,
           ⟨de, lte, lse, npe, fe, ide, be⟩, pend, prog, true⟩
    | .level id x =>
      if dl.size != 0 && id < bl then
        ⟨⟨dn, ltn, lsn, npn, fn, idn, bn⟩, ⟨dl, ltl, lsl, npl, fl, idl, bl⟩,
         ⟨de, lte, lse, npe, fe, ide, be⟩, pend, prog, true⟩
      else
        let n := dl.size
        match levelOfF (r0Look P.n c0.n c .name dn ltn fn idn bn)
            (r0Look P.l c0.l c .level dl ltl fl idl bl) (r0Look P.e c0.e c .expr de lte fe ide be)
            x with
        | .ok v => round0Go P c0 c d (p + 1) dn ltn lsn npn fn idn bn (dl.push v) (ltl.push 0)
            (lsl.push 0) npl (if n == 0 then id else fl) (keysPush n fl bl idl id) (id + 1) de lte lse npe fe ide be pend (prog + 1)
        | .error (.defer wc wk wt) =>
          let pe : Pend := ⟨p, dn.size, n, de.size, npl, wc, wk, wt⟩
          round0Go P c0 c d (p + 1) dn ltn lsn npn fn idn bn (dl.push default) (ltl.push 1)
            (lsl.push npl) (npl + 1) (if n == 0 then id else fl) (keysPush n fl bl idl id) (id + 1) de lte lse npe fe ide be (pend.push pe)
            prog
        | .error .fail =>
          ⟨⟨dn, ltn, lsn, npn, fn, idn, bn⟩, ⟨dl, ltl, lsl, npl, fl, idl, bl⟩,
           ⟨de, lte, lse, npe, fe, ide, be⟩, pend, prog, true⟩
    | .expr id x =>
      if de.size != 0 && id < be then
        ⟨⟨dn, ltn, lsn, npn, fn, idn, bn⟩, ⟨dl, ltl, lsl, npl, fl, idl, bl⟩,
         ⟨de, lte, lse, npe, fe, ide, be⟩, pend, prog, true⟩
      else
        let n := de.size
        match exprOfF (r0Look P.n c0.n c .name dn ltn fn idn bn)
            (r0Look P.l c0.l c .level dl ltl fl idl bl) (r0Look P.e c0.e c .expr de lte fe ide be)
            x with
        | .ok v => round0Go P c0 c d (p + 1) dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl
            (de.push v) (lte.push 0) (lse.push 0) npe (if n == 0 then id else fe) (keysPush n fe be ide id) (id + 1) pend (prog + 1)
        | .error (.defer wc wk wt) =>
          let pe : Pend := ⟨p, dn.size, dl.size, n, npe, wc, wk, wt⟩
          round0Go P c0 c d (p + 1) dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl
            (de.push default) (lte.push 1) (lse.push npe) (npe + 1) (if n == 0 then id else fe) (keysPush n fe be ide id) (id + 1) (pend.push pe)
            prog
        | .error .fail =>
          ⟨⟨dn, ltn, lsn, npn, fn, idn, bn⟩, ⟨dl, ltl, lsl, npl, fl, idl, bl⟩,
           ⟨de, lte, lse, npe, fe, ide, be⟩, pend, prog, true⟩
    | _ => round0Go P c0 c d (p + 1) dn ltn lsn npn fn idn bn dl ltl lsl npl fl idl bl
        de lte lse npe fe ide be pend prog
  else
    ⟨⟨dn, ltn, lsn, npn, fn, idn, bn⟩, ⟨dl, ltl, lsl, npl, fl, idl, bl⟩,
     ⟨de, lte, lse, npe, fe, ide, be⟩, pend, prog, false⟩
termination_by d.size - p

/-- Round 0 of chunk `c` (its records `recs`) of a window starting at `c0`.
The arrays it pushes onto are created here, on the chunk's owner, and
marked linear (task #331, `Array.markLinear`, the identity): a push
while a second reference is alive aborts instead of copying. -/
def round0 (P : @& Prior) (c0 : Ctr) (c : Nat) (recs : @& Array LineRec) : R0 :=
  round0Go P c0 c recs 0 #[].markLinear ByteArray.empty.markLinear #[].markLinear 0 0 #[] 0
    #[].markLinear ByteArray.empty.markLinear #[].markLinear 0 0 #[] 0
    #[].markLinear ByteArray.empty.markLinear #[].markLinear 0 0 #[] 0 #[].markLinear 0

/-- `n` zero bytes. -/
def zeroBytes (n : Nat) : ByteArray := ⟨Array.replicate n 0⟩

/-- A chunk table from round 0: the slots, and the late entries, none
done yet. -/
def TB.tab [Inhabited α] (t : TB α) : CTab α :=
  ⟨t.d, t.late, t.ls, Array.replicate t.np default, zeroBytes t.np⟩

/-! ### The later rounds -/

/-- Chunk `c`'s own geometry: where its ranges start, its keys, its
round-0 parts. -/
structure Geo where
  c : Nat
  ln : Nat
  ll : Nat
  le : Nat
  kn : Keys
  kl : Keys
  ke : Keys
  dn : Array Name
  dl : Array Level
  de : Array Expr
  latn : ByteArray
  latl : ByteArray
  late : ByteArray
  lsn : Array Nat
  lsl : Array Nat
  lse : Array Nat

/-- The counter of a table at a line with `k` lines of the table before
it in a chunk whose range starts at `lo`. -/
@[inline] def ctrOf (lo : Nat) (K : @& Keys) (k : Nat) : Nat :=
  if k == 0 then lo else K.keyOf (k - 1) + 1

/-- A later round's lookup of index `j` from chunk `c` (own range from
`lo`, keys `K`, own table given apart) at counter `b`, off the inline
paths: in the chunk's own range its own entry; else the chunk before it
whose range holds `j`. -/
@[noinline] def rawLk (S : @& Seg α) (c lo : Nat) (K : @& Keys) (d0 : @& Array α)
    (late : @& ByteArray) (ls : @& Array Nat) (lv : @& Array α) (ldone : @& ByteArray)
    (t : WT) (j : Nat) : Except Miss α :=
  if lo ≤ j then
    match K.idx j with
    | some k => match slotGet d0 late ls lv ldone k with
      | some x => .ok x
      | none => .error (.defer c k t)
    | none => .error .fail
  else
    let e := Seg.findGo S.starts j 0 c
    if e < c ∧ S.starts.getD e 0 ≤ j ∧ j < S.starts.getD (e + 1) 0 then
      match S.keys[e]? with
      | some K' => match K'.idx j with
        | some k => match S.getAt e k with
          | some x => .ok x
          | none => .error (.defer e k t)
        | none => .error .fail
      | none => .error .fail
    else .error .fail

/-- **A later round's lookup.**  Below the window, the prior pages; the
own chunk's dense range — most lookups — read inline; everything else
is `rawLk`'s. -/
@[inline] def rLk (P : @& Pages α) (S : @& Seg α) (c0t c lo : Nat) (K : @& Keys)
    (d0 : @& Array α) (late : @& ByteArray) (ls : @& Array Nat) (lv : @& Array α)
    (ldone : @& ByteArray) (t : WT) (b j : Nat) : Except Miss α :=
  if j < b then
    if K.ids.isEmpty ∧ K.first ≤ j ∧ j - K.first < d0.size then
      match slotGet d0 late ls lv ldone (j - K.first) with
      | some x => .ok x
      | none => .error (.defer c (j - K.first) t)
    else if j < c0t then
      match P.get j with
      | some x => .ok x
      | none => .error .fail
    else rawLk S c lo K d0 late ls lv ldone t j
  else .error .fail

/-- Is the slot a deferred line waits for still not done?  (No slot
named: retry.) -/
@[inline] def stillBlocked (W : @& Win) (G : @& Geo) (lvn : @& Array Name)
    (ldn : @& ByteArray) (lvl : @& Array Level) (ldl : @& ByteArray) (lve : @& Array Expr)
    (lde : @& ByteArray) (e : @& Pend) : Bool :=
  -- the other chunk's table is read BORROWED (`getD` would hand out a
  -- reference, an atomic increment on an object every worker reads)
  match e.wt with
  | .none => false
  | .name => (if e.wc == G.c then slotGet G.dn G.latn G.lsn lvn ldn e.wk
      else W.n.getAt e.wc e.wk).isNone
  | .level => (if e.wc == G.c then slotGet G.dl G.latl G.lsl lvl ldl e.wk
      else W.l.getAt e.wc e.wk).isNone
  | .expr => (if e.wc == G.c then slotGet G.de G.late G.lse lve lde e.wk
      else W.e.getAt e.wc e.wk).isNone

/-- What a later round of a chunk returns: its late entries, the entries
it computed (to be marked), the lines still pending, how many it bound,
and whether it met an anomaly. -/
structure RR where
  vn : Array Name
  dn : ByteArray
  vl : Array Level
  dl : ByteArray
  ve : Array Expr
  de : ByteArray
  fn : Array Name
  fl : Array Level
  fe : Array Expr
  pend : Array Pend
  prog : Nat
  bad : Bool

/-- A later round of chunk `G`: the pending lines from `q`. -/
def roundRGo (P : @& Prior) (W : @& Win) (G : @& Geo) (d : @& Array LineRec)
    (pend : @& Array Pend) (q : Nat) (vn : Array Name) (dn : ByteArray) (vl : Array Level)
    (dl : ByteArray) (ve : Array Expr) (de : ByteArray) (fn : Array Name) (fl : Array Level)
    (fe : Array Expr) (pend' : Array Pend) (prog : Nat) : RR :=
  if h : q < pend.size then
    let e := pend[q]
    if stillBlocked W G vn dn vl dl ve de e then
      roundRGo P W G d pend (q + 1) vn dn vl dl ve de fn fl fe (pend'.push e) prog
    else
      let bn := ctrOf G.ln G.kn e.kn
      let bl := ctrOf G.ll G.kl e.kl
      let be := ctrOf G.le G.ke e.ke
      match d[e.pos]? with
      | some (.name _ x) =>
        match nameOfF (rLk P.n W.n W.c0.n G.c G.ln G.kn G.dn G.latn G.lsn vn dn .name bn)
            (rLk P.l W.l W.c0.l G.c G.ll G.kl G.dl G.latl G.lsl vl dl .level bl)
            (rLk P.e W.e W.c0.e G.c G.le G.ke G.de G.late G.lse ve de .expr be) x with
        | .ok v =>
          roundRGo P W G d pend (q + 1) (vn.setIfInBounds e.s v) (dn.set! e.s 1) vl dl ve de
            (fn.push v) fl fe pend' (prog + 1)
        | .error (.defer wc wk wt) =>
          roundRGo P W G d pend (q + 1) vn dn vl dl ve de fn fl fe
            (pend'.push { e with wc := wc, wk := wk, wt := wt }) prog
        | .error .fail => ⟨vn, dn, vl, dl, ve, de, fn, fl, fe, pend', prog, true⟩
      | some (.level _ x) =>
        match levelOfF (rLk P.n W.n W.c0.n G.c G.ln G.kn G.dn G.latn G.lsn vn dn .name bn)
            (rLk P.l W.l W.c0.l G.c G.ll G.kl G.dl G.latl G.lsl vl dl .level bl)
            (rLk P.e W.e W.c0.e G.c G.le G.ke G.de G.late G.lse ve de .expr be) x with
        | .ok v =>
          roundRGo P W G d pend (q + 1) vn dn (vl.setIfInBounds e.s v) (dl.set! e.s 1) ve de
            fn (fl.push v) fe pend' (prog + 1)
        | .error (.defer wc wk wt) =>
          roundRGo P W G d pend (q + 1) vn dn vl dl ve de fn fl fe
            (pend'.push { e with wc := wc, wk := wk, wt := wt }) prog
        | .error .fail => ⟨vn, dn, vl, dl, ve, de, fn, fl, fe, pend', prog, true⟩
      | some (.expr _ x) =>
        match exprOfF (rLk P.n W.n W.c0.n G.c G.ln G.kn G.dn G.latn G.lsn vn dn .name bn)
            (rLk P.l W.l W.c0.l G.c G.ll G.kl G.dl G.latl G.lsl vl dl .level bl)
            (rLk P.e W.e W.c0.e G.c G.le G.ke G.de G.late G.lse ve de .expr be) x with
        | .ok v =>
          roundRGo P W G d pend (q + 1) vn dn vl dl (ve.setIfInBounds e.s v) (de.set! e.s 1)
            fn fl (fe.push v) pend' (prog + 1)
        | .error (.defer wc wk wt) =>
          roundRGo P W G d pend (q + 1) vn dn vl dl ve de fn fl fe
            (pend'.push { e with wc := wc, wk := wk, wt := wt }) prog
        | .error .fail => ⟨vn, dn, vl, dl, ve, de, fn, fl, fe, pend', prog, true⟩
      | _ => ⟨vn, dn, vl, dl, ve, de, fn, fl, fe, pend', prog, true⟩
  else ⟨vn, dn, vl, dl, ve, de, fn, fl, fe, pend', prog, false⟩
termination_by pend.size - q

/-- Chunk `c`'s start counters. -/
def Win.start (W : @& Win) (c : Nat) : Ctr :=
  ⟨W.n.starts.getD c 0, W.l.starts.getD c 0, W.e.starts.getD c 0⟩

/-- The window's counters at its end. -/
def Win.cEnd (W : Win) : Ctr := W.start W.nc

/-- An empty chunk table. -/
def CTab.blank : CTab α := ⟨#[], .empty, #[], #[], .empty⟩

/-- Chunk `c`'s geometry. -/
def Win.geo (W : @& Win) (c : Nat) : Geo :=
  let tn := W.n.tabs.getD c .blank
  let tl := W.l.tabs.getD c .blank
  let te := W.e.tabs.getD c .blank
  ⟨c, W.n.starts.getD c 0, W.l.starts.getD c 0, W.e.starts.getD c 0,
   W.n.keys.getD c default, W.l.keys.getD c default, W.e.keys.getD c default,
   tn.d0, tl.d0, te.d0, tn.late, tl.late, te.late, tn.ls, tl.ls, te.ls⟩

/-- **A later round of chunk `c`**, whose pending lines are `pend`
(nothing to do without pending lines). -/
def roundR (P : @& Prior) (W : @& Win) (c : Nat) (recs : @& Array LineRec)
    (pend : @& Array Pend) : RR :=
  let tn := W.n.tabs.getD c .blank
  let tl := W.l.tabs.getD c .blank
  let te := W.e.tabs.getD c .blank
  if pend.isEmpty then ⟨tn.lv, tn.ldone, tl.lv, tl.ldone, te.lv, te.ldone, #[], #[], #[], #[], 0,
    false⟩
  else roundRGo P W (W.geo c) recs pend 0 tn.lv tn.ldone tl.lv tl.ldone te.lv te.ldone
    #[].markLinear #[].markLinear #[].markLinear #[].markLinear 0

/-! ## The finished tables after a window

A window's entries take the ranks after the finished tables' `n`, chunk
by chunk (`rstarts`: where each chunk's ranks start).  Seen by rank, the
window is a segment of dense chunks (`Seg.byRank`), and the pages are
built over it slot by slot; the runs of the window's indices are added
to the finished tables' (`winRunsGo`), merged where they continue a
run. -/

/-- Where each chunk's ranks start, from `a`: one more than the chunk
before's last. -/
def rstartsGo (ks : @& Array Keys) (i a : Nat) (acc : Array Nat) : Array Nat :=
  if h : i < ks.size then rstartsGo ks (i + 1) (a + ks[i].cnt) (acc.push (a + ks[i].cnt))
  else acc
termination_by ks.size - i

/-- Where each chunk's ranks start, the first at `r0`; the last entry
is the window's end. -/
def rstarts (ks : @& Array Keys) (r0 : Nat) : Array Nat := rstartsGo ks 0 r0 #[r0]

/-- The window's segment by rank: chunk `c` holds the ranks from
`rstarts[c]`, densely. -/
def Seg.byRank (s : Seg α) (r0 : Nat) : Seg α :=
  let st := rstarts s.keys r0
  ⟨s.tabs, s.keys.mapIdx fun c K => ⟨st.getD c 0, K.cnt, #[]⟩, st⟩

/-- One past the window's last rank. -/
def Seg.rEnd (s : @& Seg α) (r0 : Nat) : Nat := (rstarts s.keys r0).getD s.keys.size 0

/-- From chunk `c`, forward to the last chunk below `n` whose start is
at most `j`. -/
def Seg.adv (st : @& Array Nat) (n j c : Nat) : Nat :=
  if c + 1 < n ∧ st.getD (c + 1) 0 ≤ j then Seg.adv st n j (c + 1) else c
termination_by n - c

/-- Page `p` of a table whose ranks below `lo` are `P`'s and whose
ranks in `[lo, hi)` are the window segment `s`'s (by rank); slot by
slot, from `i`, up to rank `hi`, with a cursor `c` on the window's
chunks (a hint: a slot whose rank the cursor's range does not hold is
looked up). -/
def pageGo [Inhabited α] (P : @& Pages α) (s : @& Seg α) (lo hi p : Nat) (i c : Nat)
    (v : Array α) : Array α :=
  if i < 4096 then
    let j := p * 4096 + i
    if j < lo then
      pageGo P s lo hi p (i + 1) c (v.push ((P.atRank j).getD default))
    else if j < hi then
      let c := Seg.adv s.starts s.tabs.size j c
      let x := if c < s.tabs.size ∧ s.starts.getD c 0 ≤ j ∧ j < s.starts.getD (c + 1) 0 then
          s.atC c j
        else s.get j
      pageGo P s lo hi p (i + 1) c (v.push (x.getD default))
    else v
  else v
termination_by 4096 - i

/-- Page `p` after a window: the cursor starts at the chunk holding
the page's first rank in the window. -/
def pageOf [Inhabited α] (P : @& Pages α) (s : @& Seg α) (lo hi p : Nat) : Array α :=
  let j0 := max lo (p * 4096)
  pageGo P s lo hi p 0 (Seg.findGo s.starts j0 0 s.tabs.size) (Array.mkEmpty 4096)

/-- The pages that a window over the ranks `[lo, hi)` (re)writes: from
`lo / 4096`, how many. -/
@[inline] def pagesFrom (lo : Nat) : Nat := lo / 4096
@[inline] def pagesCount (lo hi : Nat) : Nat := (hi + 4095) / 4096 - lo / 4096

/-- Split `[p0, p0 + cnt)` into `m` slices; slice `j`. -/
@[inline] def slice (p0 cnt m j : Nat) : Nat × Nat :=
  (p0 + j * cnt / m, p0 + (j + 1) * cnt / m)

/-- The pages `[a, b)` of one table after a window. -/
def pagesSlice [Inhabited α] (P : @& Pages α) (s : @& Seg α) (lo hi a b : Nat) :
    Array (Array α) :=
  go a (Array.mkEmpty (b - a))
where
  go (p : Nat) (acc : Array (Array α)) : Array (Array α) :=
    if p < b then go (p + 1) (acc.push (pageOf P s lo hi p)) else acc
  termination_by b - p

/-- Slice `c` of `m` of a table's pages after a window (segment `s`). -/
def finSlice [Inhabited α] (P : @& Pages α) (s : @& Seg α) (m c : Nat) : Array (Array α) :=
  let hi := s.rEnd P.n
  let ab := slice (pagesFrom P.n) (pagesCount P.n hi) m c
  pagesSlice P (s.byRank P.n) P.n hi ab.1 ab.2

/-- A run added after `rs`: merged into the last run when it continues
it, in indices and in ranks. -/
@[inline] def pushRun (rs : Array Run) (x : Run) : Array Run :=
  match rs.back? with
  | some y => if y.e == x.i && y.r + (y.e - y.i) == x.r then rs.pop.push ⟨y.i, x.e, y.r⟩
    else rs.push x
  | none => rs.push x

/-- The runs of keys `K` from their `k`-th, ranks from `base`, one
index at a time. -/
def idsRuns (K : @& Keys) (base k : Nat) (acc : Array Run) : Array Run :=
  if k < K.cnt then idsRuns K base (k + 1) (pushRun acc ⟨K.keyOf k, K.keyOf k + 1, base + k⟩)
  else acc
termination_by K.cnt - k

/-- The runs of a chunk's keys, ranks from `base`, after `acc`: a dense
chunk is one run. -/
def keysRuns (K : @& Keys) (base : Nat) (acc : Array Run) : Array Run :=
  if K.cnt == 0 then acc
  else if K.ids.isEmpty then pushRun acc ⟨K.first, K.first + K.cnt, base⟩
  else idsRuns K base 0 acc

/-- The runs of a window's chunks from chunk `c` (rank starts `st`),
after `acc`. -/
def winRunsGo (ks : @& Array Keys) (st : @& Array Nat) (c : Nat) (acc : Array Run) :
    Array Run :=
  if h : c < ks.size then winRunsGo ks st (c + 1) (keysRuns ks[c] (st.getD c 0) acc) else acc
termination_by ks.size - c

/-- A finished table after a window (segment `s`), its pages from the
window's first on being `news`. -/
def Pages.after (P : Pages α) (s : Seg α) (news : Array (Array α)) : Pages α :=
  let st := rstarts s.keys P.n
  ⟨P.pages.extract 0 (P.n / 4096) ++ news, winRunsGo s.keys st 0 P.runs,
   st.getD s.keys.size 0⟩

/-- The finished tables after a window. -/
def Prior.setFrom (P : Prior) (W : Win) (nn : Array (Array Name))
    (nl : Array (Array Level)) (ne : Array (Array Expr)) : Prior :=
  ⟨P.n.after W.n nn, P.l.after W.l nl, P.e.after W.e ne⟩

/-! ## A chunk's declarations

Once no line of the window is pending, a declaration line's builder
reads the finished tables before the window and the window's tables,
cut at the line's counters: the tables the serial parse holds there. -/

/-- The window's view of a table at counter `b`: below the window the
prior pages, in it the window's entries, with the serial parse's
messages. -/
@[inline] def vN (P : @& Prior) (W : @& Win) (b j : Nat) : Except String Name :=
  match (if j < b then (if j < W.c0.n then P.n.get j else W.n.get j) else none) with
  | some n => pure n
  | none => throw s!"undefined name index {j}"

@[inline] def vL (P : @& Prior) (W : @& Win) (b j : Nat) : Except String Level :=
  match (if j < b then (if j < W.c0.l then P.l.get j else W.l.get j) else none) with
  | some l => pure l
  | none => throw s!"undefined level index {j}"

@[inline] def vE (P : @& Prior) (W : @& Win) (b j : Nat) : Except String Expr :=
  match (if j < b then (if j < W.c0.e then P.e.get j else W.e.get j) else none) with
  | some e => pure e
  | none => throw s!"undefined expr index {j}"

/-- The declarations of a chunk (records `d`) from line `i`, the
counters `ct` there: `none` if a declaration line's builder yields no
record. -/
def chunkDeclsGo (P : @& Prior) (W : @& Win) (d : @& Array LineRec) (i : Nat) (ct : Ctr)
    (acc : Array Declaration) : Option (Array Declaration) :=
  if h : i < d.size then
    match d[i] with
    | .decl r =>
      match declOfF (vN P W ct.n) (vL P W ct.l) (vE P W ct.e) r with
      | .ok (.inl x) => chunkDeclsGo P W d (i + 1) ct (acc.push x)
      | _ => none
    | r => chunkDeclsGo P W d (i + 1) (ct.step r) acc
  else some acc
termination_by d.size - i

/-- **The declarations of chunk `c`**: its records walked from the
chunk's start counters. -/
def chunkDecls (P : @& Prior) (W : @& Win) (c : Nat) (d : @& Array LineRec) :
    Option (Array Declaration) :=
  chunkDeclsGo P W d 0 (W.start c) #[]

/-! ## A window's assembly -/

/-- The chunk starts of one table, from `a`: the next chunk starts one
past the last index the chunk binds, or where the chunk started if it
binds none. -/
def startsGo (ks : @& Array Keys) (i a : Nat) (acc : Array Nat) : Array Nat :=
  if h : i < ks.size then
    let K := ks[i]
    let a' := if K.cnt == 0 then a else K.keyOf (K.cnt - 1) + 1
    startsGo ks (i + 1) a' (acc.push a')
  else acc
termination_by ks.size - i

/-- A segment of chunk tables and keys, from `a`. -/
def Seg.mk' (a : Nat) (ts : Array (CTab α)) (ks : Array Keys) : Seg α :=
  ⟨ts, ks, startsGo ks 0 a #[a]⟩

/-- The window after round 0. -/
def Win.ofRound0 (c0 : Ctr) (os : Array R0) : Win :=
  ⟨c0, Seg.mk' c0.n (os.map (·.n.tab)) (os.map (·.n.keys)),
   Seg.mk' c0.l (os.map (·.l.tab)) (os.map (·.l.keys)),
   Seg.mk' c0.e (os.map (·.e.tab)) (os.map (·.e.keys)), os.size⟩

/-- The late entries of a segment's chunks replaced. -/
def Seg.setLate (s : Seg α) (lvs : Array (Array α × ByteArray)) : Seg α :=
  { s with tabs := (s.tabs.zip lvs).map fun (t, lv, ld) => { t with lv := lv, ldone := ld } }

/-- The chunks' late entries replaced, after a round. -/
def Win.setLate (W : Win) (os : Array RR) : Win :=
  { W with n := W.n.setLate (os.map fun o => (o.vn, o.dn)),
           l := W.l.setLate (os.map fun o => (o.vl, o.dl)),
           e := W.e.setLate (os.map fun o => (o.ve, o.de)) }

/-- A chunk's first index of a table is at least the chunk's start. -/
@[inline] def Seg.firstOK (s : @& Seg α) (c : Nat) : Bool :=
  match s.keys[c]? with
  | some K => K.cnt == 0 || s.starts.getD c 0 ≤ K.first
  | none => false

/-- Round 0's results, checked: no anomaly, and every chunk's first
index of each table at least its start. -/
def after0 (W : Win) (os : Array R0) : Bool :=
  os.size == W.nc &&
    (List.range os.size).all (fun c => match os[c]? with
      | some o => !o.bad && W.n.firstOK c && W.l.firstOK c && W.e.firstOK c
      | none => false)

/-- Are chunk `c`'s late entries all done? -/
def Win.fullAt (W : @& Win) (c : Nat) : Bool :=
  (W.n.tabs.getD c .blank).full && (W.l.tabs.getD c .blank).full &&
    (W.e.tabs.getD c .blank).full

end ConLeche.Frontend
