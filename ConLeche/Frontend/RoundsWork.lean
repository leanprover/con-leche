module

public import ConLeche.Frontend.Rounds

@[expose] public section

/-!
# The rounds parse: the rounds (task #329)

How the parse at `--jobs` above one (`ConLeche/Driver/LazyParse.lean`)
computes a window's tables.  Nothing here is trusted: what the driver
keeps of a window is checked line by line against the finished tables
(`checkFlatL`, `ConLeche/Frontend/Lazy.lean`), and a window whose
rounds go wrong in any way — a line that does not fit the counters, a
line the serial parse would fail at, a window that does not finish —
is handed to the serial parse.  An expression line the sweep did not
mark (`round0`'s bitmap) is bound to `lazyExpr`, not built; a built line
that reads one fails.

**Windows and rounds.**  The chunks are taken a window at a time.  In
round 0 every chunk of the window applies its lines in order, on its
own task, reading the finished tables before the window and its own
entries; a line that reads an entry of another chunk of the window is
deferred.  In each later round every chunk applies its deferred lines,
reading the other chunks' entries as of the end of the round before.
Rounds repeat until no line is deferred; the window's tables then join
the finished tables, page by page (`pageOf`).  The DAG of the stream is
shallow, so a window takes a handful of rounds.

**Keys.**  The `k`-th line of a table in a chunk binds `first + k` when
the chunk is dense (lean4export's case), else `ids[k]`; `idx` finds
`k` back (arithmetic, or a binary search).
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## Keys: the indices a chunk binds

The `k`-th line of a table in a chunk binds `first + k` when the chunk
is dense (lean4export's case), else `ids[k]`; `idx` finds `k` back
(arithmetic, or a binary search). -/

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

/-- The least position in `ids[lo, hi)` whose index is at least `j`. -/
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

/-! ## A chunk's table, built over rounds

A chunk's entries of one table are computed over several rounds, and
the other chunks read the entries of earlier rounds while this one
computes more.  An array the other chunks read is shared and cannot be
written in place.  Round 0 builds `d0`, every entry at its position,
with a placeholder (`Sent.pend`) where the line was deferred; it is
written in place during round 0 and never again.  A later round writes
a fresh `late` array, and `lpos` says where a late entry is: `0` while
it is pending, else `i * 256 + r + 1` for position `i` of late round
`r`, as four bytes (little-endian) at `4 * k`.  `lpos` is a byte array:
the per-round copy of it is a copy of bytes, and publishing it to the
other workers does not visit its entries. -/

/-- Word `k` of a byte array (four bytes, little-endian; `0` past the end). -/
@[inline] def rd32 (a : @& ByteArray) (k : Nat) : Nat :=
  let i := 4 * k
  if h : i + 3 < a.size then
    a[i].toNat + 256 * (a[i + 1].toNat + 256 * (a[i + 2].toNat + 256 * a[i + 3].toNat))
  else 0

/-- Set word `k` to `v` (below `2^32`). -/
@[inline] def wr32 (a : ByteArray) (k v : Nat) : ByteArray :=
  let i := 4 * k
  (((a.set! i (v % 256).toUInt8).set! (i + 1) (v / 256 % 256).toUInt8).set! (i + 2)
    (v / 65536 % 256).toUInt8).set! (i + 3) (v / 16777216 % 256).toUInt8

/-- One table of one chunk. -/
structure Tab (α : Type) where
  d0 : Array α
  lpos : ByteArray
  late : Array (Array α)

/-- A chunk table with `n` pending entries (round 0). -/
def Tab.empty [Sent α] (n : Nat) : Tab α := ⟨Array.replicate n Sent.pend, .empty, #[]⟩

/-- No table yet (before round 0). -/
def Tab.blank : Tab α := ⟨#[], .empty, #[]⟩

/-- A late entry `k`, if it is done. -/
@[inline] def Tab.lateGet (t : @& Tab α) (k : Nat) : Option α :=
  let p := rd32 t.lpos k
  if p == 0 then none
  else
    let q := p - 1
    if h' : q % 256 < t.late.size then t.late[q % 256][q / 256]?
    else none

/-- Entry `k`, if it is done, with the round-0 array given apart (a
later round keeps it out of the table it writes). -/
@[inline] def Tab.getD0 [Sent α] (d0 : @& Array α) (t : @& Tab α) (k : Nat) : Option α :=
  if h : k < d0.size then
    let v := d0[k]
    if Sent.isPend v then t.lateGet k else some v
  else none

/-- Entry `k`, if it is done. -/
@[inline] def Tab.get [Sent α] (t : @& Tab α) (k : Nat) : Option α :=
  if h : k < t.d0.size then
    let v := t.d0[k]
    if Sent.isPend v then t.lateGet k else some v
  else none

/-- Bind entry `k` in round 0, if it is pending. -/
@[inline] def Tab.bind0 [Sent α] (t : Tab α) (k : Nat) (x : α) : Tab α :=
  match t with
  | ⟨d0, lp, late⟩ =>
    if h : k < d0.size then
      if Sent.isPend d0[k] then ⟨d0.set k x, lp, late⟩ else ⟨d0, lp, late⟩
    else ⟨d0, lp, late⟩

/-- `n` zero bytes (doubling copies of a zero block). -/
def zeros (n : Nat) : ByteArray :=
  go (((List.replicate 64 (0 : UInt8)).foldl ByteArray.push (ByteArray.emptyWithCapacity 64))) 16
where
  go (b : ByteArray) : Nat → ByteArray
    | 0 => b.extract 0 n
    | fuel + 1 => if b.size ≥ n then b.extract 0 n else go (b ++ b) fuel

/-- Open a later round with room for `cap` entries: its array, empty
(and the positions, at the first). -/
def Tab.openRound (t : Tab α) (cap : Nat) : Tab α :=
  match t with
  | ⟨d0, lp, late⟩ =>
    ⟨d0, if lp.size == 0 then zeros (4 * d0.size) else lp, late.push (Array.mkEmpty cap)⟩

/-- A later round's own table: the round-0 array left out (it stays in
the window, read from there), the late part opened. -/
def Tab.lateOpen (t : Tab α) (cap : Nat) : Tab α :=
  match t.openRound cap with
  | ⟨_, lp, late⟩ => ⟨#[], lp, late⟩

/-- Bind entry `k` in the open later round (the last array), if it is
pending (a done entry is never changed), a round is open (at most 256)
and the position fits the word. -/
@[inline] def Tab.bindL [Sent α] (d0 : @& Array α) (t : Tab α) (k : Nat) (x : α) : Tab α :=
  -- matched, not projected: the fields are taken over from a unique
  -- `t` without a second reference, so `set!`/`modify` work in place
  match t with
  | ⟨d0', pos, ds⟩ =>
    let r := ds.size - 1
    let i := if h : r < ds.size then ds[r].size else 0
    if (match d0[k]? with | some v => Sent.isPend v | none => false) && 4 * k + 3 < pos.size &&
        rd32 pos k == 0 && 0 < ds.size && ds.size ≤ 256 && i < 16777215 then
      ⟨d0', wr32 pos k (i * 256 + r + 1), ds.modify r (·.push x)⟩
    else ⟨d0', pos, ds⟩

/-- How many entries the table has. -/
@[inline] def Tab.size (t : @& Tab α) : Nat := t.d0.size

/-! ## Segments: the chunks of a table, side by side

Chunk `c` covers the indices `[starts[c], starts[c + 1])`. -/

/-- A table split into chunks.  `dir` is a hint: for each page of 1024
indices, a chunk at or before the one holding the page's first index. -/
structure Seg (α : Type) where
  tabs : Array (Tab α)
  keys : Array Keys
  starts : Array Nat
  dir : Array Nat := #[]

/-- The last chunk whose start is at most `j`, between `lo` and `hi`
(a guess: `Seg.get` checks it). -/
def Seg.findGo (st : @& Array Nat) (j lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    if st.getD mid 0 ≤ j then Seg.findGo st j mid hi else Seg.findGo st j lo mid
  else lo
termination_by hi - lo

/-- Chunk `c`'s entry for index `j`. -/
@[inline] def Seg.at [Sent α] (s : @& Seg α) (c j : Nat) : Option α :=
  if h : c < s.keys.size then
    match s.keys[c].idx j with
    | some k => if h' : c < s.tabs.size then s.tabs[c].get k else none
    | none => none
  else none

/-- Entry `j`, looked up chunk by chunk (the specification; what runs
when the guess is wrong, which it never is on monotone starts). -/
@[noinline] def Seg.getSlow [Sent α] (s : @& Seg α) (j : Nat) : Option α :=
  go 0
where
  go (c : Nat) : Option α :=
    if c < s.tabs.size then
      if s.starts.getD c 0 ≤ j ∧ j < s.starts.getD (c + 1) 0 then s.at c j
      else go (c + 1)
    else none
  termination_by s.tabs.size - c

/-- From chunk `c`, forward to the chunk whose range holds `j` (at most
`fuel` steps). -/
@[inline] def Seg.fwd (st : @& Array Nat) (j : Nat) : Nat → Nat → Nat
  | 0, c => c
  | fuel + 1, c => if st.getD (c + 1) 0 ≤ j then Seg.fwd st j fuel (c + 1) else c

/-- The chunk that holds index `j` (a guess, checked by the caller): by
the page directory, else by binary search. -/
@[inline] def Seg.find (s : @& Seg α) (j : Nat) : Nat :=
  let p := j / 1024
  let c := if h : p < s.dir.size then Seg.fwd s.starts j 4 s.dir[p] else s.tabs.size
  if c < s.tabs.size ∧ s.starts.getD c 0 ≤ j ∧ j < s.starts.getD (c + 1) 0 then c
  else Seg.findGo s.starts j 0 s.tabs.size

/-- Entry `j`: the guessed chunk if its range holds `j`. -/
@[inline] def Seg.get [Sent α] (s : @& Seg α) (j : Nat) : Option α :=
  let c := s.find j
  if s.starts.getD c 0 ≤ j ∧ j < s.starts.getD (c + 1) 0 ∧ c < s.tabs.size then s.at c j
  else Seg.getSlow s j

/-- The page directory, extended from page `p` to the pages below
`stop`: the last chunk, from `c`, whose start is at most the page's
first index. -/
def dirGo (st : @& Array Nat) (stop p c : Nat) (dir : Array Nat) : Array Nat :=
  if p * 1024 < stop then
    let c := Seg.fwd st (p * 1024) st.size c
    dirGo st stop (p + 1) c (dir.push c)
  else dir
termination_by stop - p * 1024
decreasing_by
  have : p * 1024 < (p + 1) * 1024 := by omega
  omega

/-- The window: its chunks' flat scans and tables, and where its tables
start. -/
structure Win where
  c0 : Ctr
  n : Seg Name
  l : Seg Level
  e : Seg Expr
  data : Array ByteArray

/-- A rounds lookup that does not answer: the entry is not done yet, or
the serial parse would fail here. -/
inductive Miss where
  /-- not done yet: the entry it waits for, as a wait word (`j * 4 + t`;
  `t`: 0 name, 1 level, 2 expr) -/
  | defer (blk : Nat)
  | fail

/-! ### The lookups of a round

A lookup answers an entry, or "not yet" (`defer`: the entry is another
chunk's, not done in an earlier round), or "never" (`fail`: the serial
parse would fail here).  The answers are carried WITHOUT an allocation:
the raw lookup returns the entry or one of two sentinel values, and the
`Except` the builders read is made around it by an inlined test.  A
real entry that happened to look like a sentinel would only be read as
a miss (the window would then fall back to the serial parse); no
parsed entry does — a parsed expression has no free variable. -/

/-- The sentinel numbers (below `2^32`: a literal above that is a decimal
parse at every use). -/
def sentD : Nat := 4000000000
def sentF : Nat := 4000000001

def missN (k : Nat) : Name := .num .anonymous k
def missL (k : Nat) : Level := .param (.num .anonymous k)
def missE (k : Nat) : Expr := .fvar k (.bvar 0)
@[noinline] def missND : Name := missN sentD
@[noinline] def missNF : Name := missN sentF
@[noinline] def missLD : Level := missL sentD
@[noinline] def missLF : Level := missL sentF
@[noinline] def missED : Expr := missE sentD
@[noinline] def missEF : Expr := missE sentF

/-- What a raw answer means. -/
@[inline] def nameMiss (j : Nat) : Name → Except Miss Name
  | .num .anonymous k => if k == sentD then .error (.defer (j * 4)) else if k == sentF then .error .fail
      else .ok (.num .anonymous k)
  | x => .ok x

@[inline] def levelMiss (j : Nat) : Level → Except Miss Level
  | .param (.num .anonymous k) => if k == sentD then .error (.defer (j * 4 + 1))
      else if k == sentF then .error .fail else .ok (.param (.num .anonymous k))
  | x => .ok x

@[inline] def exprMiss (j : Nat) : Expr → Except Miss Expr
  | .fvar k t => if k == sentD then .error (.defer (j * 4 + 2)) else if k == sentF then .error .fail
      else .ok (.fvar k t)
  | x => .ok x

/-- A lookup in chunk `e` of a segment (`d`/`f`: the sentinels). -/
@[inline] def Seg.atRaw [Sent α] (s : @& Seg α) (e j : Nat) (d f : α) : α :=
  if h : e < s.keys.size then
    match s.keys[e].idx j with
    | some k => if h' : e < s.tabs.size then
        match s.tabs[e].get k with
        | some x => x
        | none => d
      else f
    | none => f
  else f

/-- A window lookup from chunk `c`, whose own table is `own` and own
range starts at `lo`: `c`'s range reads `own` through `c`'s keys
`K`, another chunk's range that chunk's table; `d`/`f` are the
sentinels. -/
@[inline] def Seg.viewRaw [Sent α] (s : @& Seg α) (c lo : Nat) (K : @& Keys) (own : @& Tab α)
    (d0 : @& Array α) (j : Nat) (d f : α) : α :=
  if lo ≤ j then
    match K.idx j with
    | some k => match Tab.getD0 d0 own k with
      | some x => x
      | none => d
    | none => f
  else
    let e := Seg.findGo s.starts j 0 c
    if s.starts.getD e 0 ≤ j ∧ j < s.starts.getD (e + 1) 0 then s.atRaw e j d f else f

/-- The raw rounds lookups of chunk `c` (own range from `lo`, keys `K`,
table `own`) at counter `b`: below the window, the prior tables; in the
window, `Seg.viewRaw`.  At or above the counter, the serial parse
fails. -/
@[noinline] def rNameRaw (P : @& Prior) (W : @& Win) (c lo : Nat) (K : @& Keys)
    (own : @& Tab Name) (d0 : @& Array Name) (b j : Nat) : Name :=
  if j < b then
    if W.c0.n ≤ j then W.n.viewRaw c lo K own d0 j missND missNF
    else match P.n.get j with | some x => x | none => missNF
  else missNF

@[noinline] def rLevelRaw (P : @& Prior) (W : @& Win) (c lo : Nat) (K : @& Keys)
    (own : @& Tab Level) (d0 : @& Array Level) (b j : Nat) : Level :=
  if j < b then
    if W.c0.l ≤ j then W.l.viewRaw c lo K own d0 j missLD missLF
    else match P.l.get j with | some x => x | none => missLF
  else missLF

@[noinline] def rExprRaw (P : @& Prior) (W : @& Win) (c lo : Nat) (K : @& Keys)
    (own : @& Tab Expr) (d0 : @& Array Expr) (b j : Nat) : Expr :=
  if j < b then
    if W.c0.e ≤ j then W.e.viewRaw c lo K own d0 j missED missEF
    else match P.e.get j with | some x => x | none => missEF
  else missEF

/-- Chunk `c`'s own geometry: where its ranges start, its keys. -/
structure Geo where
  c : Nat
  ln : Nat
  ll : Nat
  le : Nat
  kn : Keys
  kl : Keys
  ke : Keys
  /-- the chunk's round-0 arrays, as the window holds them (later rounds) -/
  dn : Array Name
  dl : Array Level
  de : Array Expr

/-- A late own entry, raw. -/
@[noinline] def lateRaw [Sent α] (t : @& Tab α) (k : Nat) (d : α) : α :=
  match t.lateGet k with
  | some x => x
  | none => d

/-- A wait word: the entry `k` of chunk `c`'s table `t` (0 name,
1 level, 2 expr). -/
@[inline] def waitWord (c k t : Nat) : Nat := ((c * 65536 * 65536 + k) * 4) + t

/-- The wait word of a window index whose raw lookup said "not yet". -/
@[noinline] def winWait [Sent α] (s : @& Seg α) (n j t : Nat) : Nat :=
  let e := Seg.findGo s.starts j 0 n
  if h : e < s.keys.size then
    match s.keys[e].idx j with
    | some k => waitWord e k t
    | none => 0
  else 0

/-- The rounds lookups.  The own chunk's dense range — most lookups —
is read inline; everything else is the raw lookup's. -/
@[inline] def rName (P : @& Prior) (W : @& Win) (G : @& Geo) (own : @& Tab Name)
    (d0 : @& Array Name) (b j : Nat) :
    Except Miss Name :=
  if G.ln ≤ j ∧ j < b ∧ G.kn.ids.isEmpty ∧ G.kn.first ≤ j then
    let k := j - G.kn.first
    if h : k < d0.size then
      let v := d0[k]
      if Sent.isPend v then
        match own.lateGet k with
        | some x => .ok x
        | none => .error (.defer (waitWord G.c k 0))
      else .ok v
    else .error .fail
  else match rNameRaw P W G.c G.ln G.kn own d0 b j with
    | .num .anonymous k =>
      if k == sentD then .error (.defer (winWait W.n W.data.size j 0))
      else if k == sentF then .error .fail else .ok (.num .anonymous k)
    | x => .ok x
@[inline] def rLevel (P : @& Prior) (W : @& Win) (G : @& Geo) (own : @& Tab Level)
    (d0 : @& Array Level) (b j : Nat) :
    Except Miss Level :=
  if G.ll ≤ j ∧ j < b ∧ G.kl.ids.isEmpty ∧ G.kl.first ≤ j then
    let k := j - G.kl.first
    if h : k < d0.size then
      let v := d0[k]
      if Sent.isPend v then
        match own.lateGet k with
        | some x => .ok x
        | none => .error (.defer (waitWord G.c k 1))
      else .ok v
    else .error .fail
  else match rLevelRaw P W G.c G.ll G.kl own d0 b j with
    | .param (.num .anonymous k) =>
      if k == sentD then .error (.defer (winWait W.l W.data.size j 1))
      else if k == sentF then .error .fail else .ok (.param (.num .anonymous k))
    | x => .ok x
@[inline] def rExpr (P : @& Prior) (W : @& Win) (G : @& Geo) (own : @& Tab Expr)
    (d0 : @& Array Expr) (b j : Nat) :
    Except Miss Expr :=
  if G.le ≤ j ∧ j < b ∧ G.ke.ids.isEmpty ∧ G.ke.first ≤ j then
    let k := j - G.ke.first
    if h : k < d0.size then
      let v := d0[k]
      if Sent.isPend v then
        match own.lateGet k with
        | some x => .ok x
        | none => .error (.defer (waitWord G.c k 2))
      else if isLazyE v then .error .fail
      else .ok v
    else .error .fail
  else match rExprRaw P W G.c G.le G.ke own d0 b j with
    | .fvar k t =>
      if k == sentD then .error (.defer (winWait W.e W.data.size j 2))
      else if k == sentF || k == sentL then .error .fail else .ok (.fvar k t)
    | x => .ok x

/-- What one table line does in a round. -/
inductive LStep where
  | name (t : Tab Name)
  | level (t : Tab Level)
  | expr (t : Tab Expr)
  | defer (blk : Nat)
  | fail

/-- Bind in round 0 or in a later round. -/
@[inline] def Tab.bindR [Sent α] (r0 : Bool) (d0 : @& Array α) (t : Tab α) (k : Nat) (x : α) :
    Tab α :=
  if r0 then t.bind0 k x else Tab.bindL d0 t k x

/-- One table line at counters `bn`/`bl`/`be`, in the chunk `G` whose
tables are `tn`/`tl`/`te`: its entry bound at its position `k`, if
every entry it reads is done. -/
@[inline] def lineStep (r0 : Bool) (P : @& Prior) (W : @& Win) (G : @& Geo) (tn : Tab Name)
    (tl : Tab Level) (te : Tab Expr) (bn bl be k : Nat) (r : @& LineRec) : LStep :=
  -- round 0: the round-0 arrays are the tables' own; a later round's
  -- are the window's (`G`), kept out of the tables it writes
  let dn := if r0 then tn.d0 else G.dn
  let dl := if r0 then tl.d0 else G.dl
  let de := if r0 then te.d0 else G.de
  match r with
  | .name _ x =>
    match nameOfF (rName P W G tn dn bn) (rLevel P W G tl dl bl) (rExpr P W G te de be) x with
    | .ok v => .name (tn.bindR r0 dn k v)
    | .error (.defer blk) => .defer blk
    | .error .fail => .fail
  | .level _ x =>
    match levelOfF (rName P W G tn dn bn) (rLevel P W G tl dl bl) (rExpr P W G te de be) x with
    | .ok v => .level (tl.bindR r0 dl k v)
    | .error (.defer blk) => .defer blk
    | .error .fail => .fail
  | .expr _ x =>
    match exprOfF (rName P W G tn dn bn) (rLevel P W G tl dl bl) (rExpr P W G te de be) x with
    | .ok v => .expr (te.bindR r0 de k v)
    | .error (.defer blk) => .defer blk
    | .error .fail => .fail
  | _ => .fail

/-- Chunk `c`'s own tables. -/
structure Own where
  n : Tab Name
  l : Tab Level
  e : Tab Expr

/-- Push a line and its counters. -/
@[inline] def push4 (a : Array Nat) (i bn bl be : Nat) : Array Nat :=
  (((a.push i).push bn).push bl).push be

/-- Push a pending line, its counters and what it waits for. -/
@[inline] def push5 (a : Array Nat) (i bn bl be blk : Nat) : Array Nat :=
  (push4 a i bn bl be).push blk

/-! ### What a deferred line waits for

A deferred line is not retried in every later round: it is retried
when the entry it waited for is done.  The entry is a hint — a line
retried early just defers again, and a line never retried stays
pending, so the window falls back — and costs one lookup per round. -/

/-- Is the entry named by a wait word still pending?  (`0`: no wait
word, retry.) -/
@[inline] def stillBlocked (W : @& Win) (G : @& Geo) (tn : @& Tab Name)
    (tl : @& Tab Level) (te : @& Tab Expr) (blk : Nat) : Bool :=
  if blk == 0 then false
  else
    let q := blk >>> 2
    let k := q &&& 4294967295
    let c := q >>> 32
    -- the other chunk's table is read BORROWED (`getD` would hand out
    -- a reference, an atomic increment on an object every worker reads)
    match blk &&& 3 with
    | 0 => if c == G.c then (Tab.getD0 G.dn tn k).isNone
        else if h : c < W.n.tabs.size then (W.n.tabs[c].get k).isNone else false
    | 1 => if c == G.c then (Tab.getD0 G.dl tl k).isNone
        else if h : c < W.l.tabs.size then (W.l.tabs[c].get k).isNone else false
    | 2 => if c == G.c then (Tab.getD0 G.de te k).isNone
        else if h : c < W.e.tabs.size then (W.e.tabs[c].get k).isNone else false
    | _ => false

/-! ### Round 0

Round 0 of a chunk needs nothing of the window's other chunks, so it
runs right after the chunk's scan, on the same worker, while the
chunk's records are still in its cache.  What it cannot know is where
the chunk's ranges start (one past the last index the chunk before it
binds): a counter before the chunk's first line of a table is that
start, and round 0 writes it as the word `0` — every other counter
`b` as `b + 1` — and reads below it only what lies below the window.
Its keys (the indices each table's lines bind) and its round-0 arrays
are pushed line by line; the window's ranges come from the keys once
every chunk is through. -/

/-- A counter as a word: `0` the chunk's start (not known in round 0),
else the counter plus one. -/
@[inline] def ctrWord (seen : Bool) (b : Nat) : Nat := if seen then b + 1 else 0

/-- A counter word read back, at a chunk starting at `start`. -/
@[inline] def wordCtr (start w : Nat) : Nat := if w == 0 then start else w - 1

/-- Round 0's lookup in one table: below the window the prior pages;
the chunk's own entries from its first index `first` below its counter
`b`; anything else in the window waits (`defer 0`: another chunk, or the
chunk's start not known yet). -/
@[inline] def r0Look [Sent α] (pg : @& Pages α) (c0x c t first b : Nat) (ids : @& Array Nat)
    (d0 : @& Array α) (j : Nat) : Except Miss α :=
  if j < c0x then
    match pg.get j with
    | some x => .ok x
    | none => .error .fail
  else if d0.size == 0 then .error (.defer 0)
  else if j < b then
    if first ≤ j then
      let k := if ids.isEmpty then j - first else keysFind ids j 0 ids.size
      if h : k < d0.size then
        if ids.isEmpty || ids.getD k 0 == j then
          let v := d0[k]
          if Sent.isPend v then .error (.defer (waitWord c k t)) else .ok v
        else .error .fail
      else .error .fail
    else .error (.defer 0)
  else .error .fail

/-- Round 0's expression lookup: `r0Look`, a lazy entry (bound, not
built) failing — a built line never reads one. -/
@[inline] def r0LookE (pg : @& Pages Expr) (c0x c first b : Nat) (ids : @& Array Nat)
    (d0 : @& Array Expr) (j : Nat) : Except Miss Expr :=
  match r0Look pg c0x c 2 first b ids d0 j with
  | .ok v => if isLazyE v then .error .fail else .ok v
  | e => e

/-- Is expression index `j` marked (to be built)?  An empty bitmap marks
every index (the eager parse). -/
@[inline] def isMarked (mk : @& ByteArray) (j : Nat) : Bool :=
  mk.size == 0 ||
    (let b := j / 8
     if h : b < mk.size then (mk[b] >>> (j % 8).toUInt8) &&& 1 == 1 else false)

/-- One more index on a table's keys, as round 0 pushes it: `first` and
`ids` after a line binding `id` (the line count before it is `n`, the
last index `b - 1`). -/
@[inline] def keyPush (n first b : Nat) (ids : Array Nat) (id : Nat) : Nat × Array Nat :=
  if n == 0 then (id, ids)
  else if ids.isEmpty then
    if id == b then (first, ids)
    else (first, ((Array.range n).map (first + ·)).push id)
  else (first, ids.push id)

/-! ### Pending lines

A deferred line is kept as 24 bytes of a byte array: where its record
starts in the chunk's flat scan, its three counters (as `ctrWord`s),
four bytes each (a larger counter is cut, the line is then misread and
the window falls back), and what it waits for, eight bytes.  The array
grows by doubling; the count of lines is kept beside it.  A byte array
crosses to the next round's worker as one object. -/

/-- Write four bytes (little-endian) at byte `i` (inside the array). -/
@[inline] def put32 (a : ByteArray) (i : Nat) (x : Nat) : ByteArray :=
  let v := x.toUInt32
  (((a.set! i v.toUInt8).set! (i + 1) (v >>> 8).toUInt8).set! (i + 2)
    (v >>> 16).toUInt8).set! (i + 3) (v >>> 24).toUInt8

/-- Four bytes (little-endian) at byte `i` (`0` past the end). -/
@[inline] def get32 (a : @& ByteArray) (i : Nat) : Nat :=
  if h : i + 3 < a.size then
    ((a[i]'(by omega)).toUInt32 ||| ((a[i + 1]'(by omega)).toUInt32 <<< 8) |||
      ((a[i + 2]'(by omega)).toUInt32 <<< 16) ||| ((a[i + 3]'(by omega)).toUInt32 <<< 24)).toNat
  else 0

/-- Pending line `n` (the `n`-th 24-byte record) written. -/
@[inline] def pendPush (a : ByteArray) (n p wn wl we blk : Nat) : ByteArray :=
  let off := 24 * n
  let a := if off + 24 ≤ a.size then a else a ++ zeros (a.size + 24 * 64)
  put32 (put32 (put32 (put32 (put32 (put32 a off p) (off + 4) wn) (off + 8) wl) (off + 12) we)
    (off + 16) (blk &&& 4294967295)) (off + 20) (blk >>> 32)

/-- Round 0's result for one chunk. -/
structure R0 where
  dn : Array Name
  dl : Array Level
  de : Array Expr
  kn : Keys
  kl : Keys
  ke : Keys
  pend : ByteArray
  npend : Nat
  prog : Nat
  bad : Bool

/-- Round 0 of chunk `c` of a window starting at `c0`: the `k` lines of
the flat scan `d` from position `p`, in order.  For each table the
counter `b`, the first index `f`, the index list (empty while dense)
and the round-0 array. -/
def round0Go (P : @& Prior) (mk : @& ByteArray) (c0 : Ctr) (c : Nat) (d : @& ByteArray) (p : USize)
    (k : Nat)
    (bn fn : Nat) (idn : Array Nat) (dn : Array Name)
    (bl fl : Nat) (idl : Array Nat) (dl : Array Level)
    (be fe : Nat) (ide : Array Nat) (de : Array Expr)
    (pend : ByteArray) (np prog : Nat) : R0 :=
  match k with
  | 0 => ⟨dn, dl, de, ⟨fn, dn.size, idn⟩, ⟨fl, dl.size, idl⟩, ⟨fe, de.size, ide⟩, pend, np, prog,
      false⟩
  | k + 1 =>
    Flat.withLineU d p fun r q =>
    match r with
    | .name id x =>
      if dn.size != 0 && id < bn then ⟨dn, dl, de, ⟨fn, dn.size, idn⟩, ⟨fl, dl.size, idl⟩,
        ⟨fe, de.size, ide⟩, pend, np, prog, true⟩
      else
        let (fn', idn') := keyPush dn.size fn bn idn id
        match nameOfF (r0Look P.n c0.n c 0 fn bn idn dn) (r0Look P.l c0.l c 1 fl bl idl dl)
            (r0LookE P.e c0.e c fe be ide de) x with
        | .ok v => round0Go P mk c0 c d q k (id + 1) fn' idn' (dn.push v) bl fl idl dl
            be fe ide de pend np (prog + 1)
        | .error (.defer blk) => round0Go P mk c0 c d q k (id + 1) fn' idn' (dn.push Sent.pend)
            bl fl idl dl be fe ide de
            (pendPush pend np p.toNat (ctrWord (dn.size != 0) bn) (ctrWord (dl.size != 0) bl)
              (ctrWord (de.size != 0) be) blk) (np + 1) prog
        | .error .fail => ⟨dn, dl, de, ⟨fn, dn.size, idn⟩, ⟨fl, dl.size, idl⟩,
            ⟨fe, de.size, ide⟩, pend, np, prog, true⟩
    | .level id x =>
      if dl.size != 0 && id < bl then ⟨dn, dl, de, ⟨fn, dn.size, idn⟩, ⟨fl, dl.size, idl⟩,
        ⟨fe, de.size, ide⟩, pend, np, prog, true⟩
      else
        let (fl', idl') := keyPush dl.size fl bl idl id
        match levelOfF (r0Look P.n c0.n c 0 fn bn idn dn) (r0Look P.l c0.l c 1 fl bl idl dl)
            (r0LookE P.e c0.e c fe be ide de) x with
        | .ok v => round0Go P mk c0 c d q k bn fn idn dn (id + 1) fl' idl' (dl.push v)
            be fe ide de pend np (prog + 1)
        | .error (.defer blk) => round0Go P mk c0 c d q k bn fn idn dn (id + 1) fl' idl'
            (dl.push Sent.pend) be fe ide de
            (pendPush pend np p.toNat (ctrWord (dn.size != 0) bn) (ctrWord (dl.size != 0) bl)
              (ctrWord (de.size != 0) be) blk) (np + 1) prog
        | .error .fail => ⟨dn, dl, de, ⟨fn, dn.size, idn⟩, ⟨fl, dl.size, idl⟩,
            ⟨fe, de.size, ide⟩, pend, np, prog, true⟩
    | .expr id x =>
      if de.size != 0 && id < be then ⟨dn, dl, de, ⟨fn, dn.size, idn⟩, ⟨fl, dl.size, idl⟩,
        ⟨fe, de.size, ide⟩, pend, np, prog, true⟩
      else
        let (fe', ide') := keyPush de.size fe be ide id
        if !isMarked mk id then
          -- a line no install reads: bound, not built
          round0Go P mk c0 c d q k bn fn idn dn bl fl idl dl (id + 1) fe' ide'
            (de.push lazyExpr) pend np (prog + 1)
        else
        match exprOfF (r0Look P.n c0.n c 0 fn bn idn dn) (r0Look P.l c0.l c 1 fl bl idl dl)
            (r0LookE P.e c0.e c fe be ide de) x with
        | .ok v => round0Go P mk c0 c d q k bn fn idn dn bl fl idl dl (id + 1) fe' ide'
            (de.push v) pend np (prog + 1)
        | .error (.defer blk) => round0Go P mk c0 c d q k bn fn idn dn bl fl idl dl (id + 1)
            fe' ide' (de.push Sent.pend)
            (pendPush pend np p.toNat (ctrWord (dn.size != 0) bn) (ctrWord (dl.size != 0) bl)
              (ctrWord (de.size != 0) be) blk) (np + 1) prog
        | .error .fail => ⟨dn, dl, de, ⟨fn, dn.size, idn⟩, ⟨fl, dl.size, idl⟩,
            ⟨fe, de.size, ide⟩, pend, np, prog, true⟩
    | _ => round0Go P mk c0 c d q k bn fn idn dn bl fl idl dl be fe ide de pend np prog

/-- Round 0 of chunk `c` (its flat scan `fc`) of a window starting at
`c0`. -/
def round0 (P : @& Prior) (mk : @& ByteArray) (c0 : Ctr) (c : Nat) (fc : @& FlatChunk) : R0 :=
  if fc.data.size < USize.size then
    round0Go P mk c0 c fc.data 0 fc.count 0 0 #[] #[] 0 0 #[] #[] 0 0 #[] (Array.mkEmpty (fc.count + 1))
      .empty 0 0
  else ⟨#[], #[], #[], default, default, default, .empty, 0, 0, true⟩

/-- Chunk `c`'s start counters. -/
def Win.start (W : @& Win) (c : Nat) : Ctr :=
  ⟨W.n.starts.getD c 0, W.l.starts.getD c 0, W.e.starts.getD c 0⟩

/-- The window's counters at its end. -/
def Win.cEnd (W : Win) : Ctr := W.start W.data.size

/-- Chunk `c`'s geometry. -/
def Win.geo (W : @& Win) (c : Nat) : Geo :=
  ⟨c, W.n.starts.getD c 0, W.l.starts.getD c 0, W.e.starts.getD c 0,
   W.n.keys.getD c default, W.l.keys.getD c default, W.e.keys.getD c default,
   (W.n.tabs.getD c .blank).d0, (W.l.tabs.getD c .blank).d0, (W.e.tabs.getD c .blank).d0⟩

/-- Chunk `c`'s tables, from the window. -/
def Win.own (W : @& Win) (c : Nat) : Own :=
  ⟨W.n.tabs.getD c .blank, W.l.tabs.getD c .blank, W.e.tabs.getD c .blank⟩

/-- The position of a table line's index in its chunk table. -/
@[inline] def lineKey (G : @& Geo) : LineRec → Option Nat
  | .name i _ => G.kn.idx i
  | .level i _ => G.kl.idx i
  | .expr i _ => G.ke.idx i
  | _ => none

/-- What a later round of a chunk returns: its tables, the lines still
pending (and how many), how many it bound, and whether it met an
anomaly. -/
structure RR where
  own : Own
  pend : ByteArray
  npend : Nat
  prog : Nat
  bad : Bool

/-- A later round of chunk `G`: `n` pending lines from byte `q` of
`pend`. -/
def roundRGo (P : @& Prior) (W : @& Win) (G : @& Geo) (d : @& ByteArray)
    (pend : @& ByteArray) (q : Nat) (n : Nat) (tn : Tab Name) (tl : Tab Level) (te : Tab Expr)
    (pend' : ByteArray) (np prog : Nat) : RR :=
  match n with
  | 0 => ⟨⟨tn, tl, te⟩, pend', np, prog, false⟩
  | n + 1 =>
    let pos := get32 pend q
    let wn := get32 pend (q + 4)
    let wl := get32 pend (q + 8)
    let we := get32 pend (q + 12)
    let blk := get32 pend (q + 16) + get32 pend (q + 20) * 65536 * 65536
    if stillBlocked W G tn tl te blk then
      roundRGo P W G d pend (q + 24) n tn tl te (pendPush pend' np pos wn wl we blk) (np + 1) prog
    else if pos < d.size && d.size < USize.size then
      let bn := wordCtr G.ln wn
      let bl := wordCtr G.ll wl
      let be := wordCtr G.le we
      Flat.withLineU d pos.toUSize fun r _ =>
      match lineKey G r with
      | some k =>
        match lineStep false P W G tn tl te bn bl be k r with
        | .name tn => roundRGo P W G d pend (q + 24) n tn tl te pend' np (prog + 1)
        | .level tl => roundRGo P W G d pend (q + 24) n tn tl te pend' np (prog + 1)
        | .expr te => roundRGo P W G d pend (q + 24) n tn tl te pend' np (prog + 1)
        | .defer blk => roundRGo P W G d pend (q + 24) n tn tl te
            (pendPush pend' np pos wn wl we blk) (np + 1) prog
        | .fail => ⟨⟨tn, tl, te⟩, pend', np, prog, true⟩
      | none => ⟨⟨tn, tl, te⟩, pend', np, prog, true⟩
    else ⟨⟨tn, tl, te⟩, pend', np, prog, true⟩

/-- A later round of chunk `c`, whose `np` pending lines are `pend`
(nothing to do without pending lines). -/
def roundR (P : @& Prior) (W : @& Win) (c : Nat) (pend : @& ByteArray) (np : Nat) : RR :=
  if np == 0 then ⟨W.own c, .empty, 0, 0, false⟩
  else
    let o := W.own c
    let G := W.geo c
    match roundRGo P W G (W.data.getD c .empty) pend 0 np (o.n.lateOpen 0) (o.l.lateOpen 0)
        (o.e.lateOpen 0) .empty 0 0 with
    | ⟨⟨tn, tl, te⟩, pend', np', prog, bad⟩ =>
      -- the round-0 arrays back in
      ⟨⟨⟨G.dn, tn.lpos, tn.late⟩, ⟨G.dl, tl.lpos, tl.late⟩, ⟨G.de, te.lpos, te.late⟩⟩,
       pend', np', prog, bad⟩

/-! ## The finished tables after a window -/

/-- Page `p` of a table whose indices below `lo` are `P`'s and whose
indices in `[lo, hi)` are the window segment `s`'s; slot by slot, from
`i`, with a cursor `c` on the window's chunks. -/
def pageGo [Sent α] (P : @& Pages α) (s : @& Seg α) (lo hi p : Nat) (i c : Nat)
    (acc : Array α) : Array α :=
  if i < 4096 then
    let j := p * 4096 + i
    if j < lo then
      pageGo P s lo hi p (i + 1) c (acc.push ((P.get j).getD Sent.pend))
    else if j < hi then
      -- the cursor: chunk `c` while `j` is below its end (a cursor past
      -- `j` is answered by the segment's own lookup)
      if j < s.starts.getD (c + 1) 0 then
        let v := if s.starts.getD c 0 ≤ j ∧ c < s.tabs.size then (s.at c j).getD Sent.pend
          else (s.get j).getD Sent.pend
        pageGo P s lo hi p (i + 1) c (acc.push v)
      else if c < s.tabs.size then pageGo P s lo hi p i (c + 1) acc
      else pageGo P s lo hi p (i + 1) c (acc.push Sent.pend)
    else pageGo P s lo hi p (i + 1) c (acc.push Sent.pend)
  else acc
termination_by (4096 - i, s.tabs.size - c)

/-- Page `p` after a window: the cursor starts at the chunk holding
the page's first index in the window. -/
def pageOf [Sent α] (P : @& Pages α) (s : @& Seg α) (lo hi p : Nat) : Array α :=
  let j0 := max lo (p * 4096)
  pageGo P s lo hi p 0 (Seg.findGo s.starts j0 0 s.tabs.size) (Array.mkEmpty 4096)

/-- The pages that a window over `[lo, hi)` (re)writes: from `lo / 4096`,
how many. -/
@[inline] def pagesFrom (lo : Nat) : Nat := lo / 4096
@[inline] def pagesCount (lo hi : Nat) : Nat := (hi + 4095) / 4096 - lo / 4096

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

/-- A segment of chunk tables, their round-0 arrays and keys, from `a`,
without a page directory. -/
def Seg.ofRound0 (a : Nat) (ds : Array (Array α)) (ks : Array Keys) : Seg α :=
  ⟨ds.map fun d => ⟨d, .empty, #[]⟩, ks, startsGo ks 0 a #[a], #[]⟩

/-- The window after round 0. -/
def Win.ofRound0 (c0 : Ctr) (data : Array ByteArray) (os : Array R0) : Win :=
  ⟨c0, Seg.ofRound0 c0.n (os.map (·.dn)) (os.map (·.kn)),
   Seg.ofRound0 c0.l (os.map (·.dl)) (os.map (·.kl)),
   Seg.ofRound0 c0.e (os.map (·.de)) (os.map (·.ke)), data⟩

/-- The chunks' tables replaced. -/
def Win.setOwn (W : Win) (os : Array Own) : Win :=
  { W with n := { W.n with tabs := os.map (·.n) }, l := { W.l with tabs := os.map (·.l) },
           e := { W.e with tabs := os.map (·.e) } }

/-- A chunk's first index of a table is at least the chunk's start. -/
@[inline] def Seg.firstOK (s : @& Seg α) (c : Nat) : Bool :=
  match s.keys[c]? with
  | some K => K.cnt == 0 || s.starts.getD c 0 ≤ K.first
  | none => false

/-- Round 0's results, checked: no anomaly, every chunk's first index
of each table at least its start, and no table's range in the window
much wider than its entries (a stream with huge gaps would make huge
pages: it is left to the serial parse). -/
def after0 (W : Win) (os : Array R0) : Bool :=
  os.size == W.data.size &&
    (List.range os.size).all (fun c => match os[c]? with
      | some o => !o.bad && W.n.firstOK c && W.l.firstOK c && W.e.firstOK c
      | none => false) &&
    (let cE := W.cEnd
     let cnt (f : R0 → Nat) := os.foldl (fun a o => a + f o) 0
     cE.n - W.c0.n ≤ 8 * cnt (·.kn.cnt) + 8388608 &&
     cE.l - W.c0.l ≤ 8 * cnt (·.kl.cnt) + 8388608 &&
     cE.e - W.c0.e ≤ 8 * cnt (·.ke.cnt) + 8388608)

/-- The rounds a window may take after round 0 (every round opens a
late array; a chunk table holds at most 256). -/
def maxRounds : Nat := 254

end ConLeche.Frontend
