module

public import ConLeche.Frontend.RoundsWork

@[expose] public section

/-!
# The lazy parse: theorem-only lines bound, not built (task #329)

Install reads every declaration's statement, every definition's and
opaque's value and every inductive block, but never a theorem's value
(a stored theorem carries none).  Most of a stream's expression lines
(70–82 % on Mathlib and `init`) are read by theorem values alone.  The
lazy parse does not build them: a backward sweep over the scanned
chunks marks the expression lines install needs (`sweepChunk`), the
rounds build only the marked ones (`round0`'s bitmap,
`ConLeche/Frontend/RoundsWork.lean`) and bind the others to the
placeholder `lazyExpr`, and each theorem's value is built later, from
the lines kept here, by the task that checks the theorem.

Nothing the sweep or the rounds compute is believed.  The check of a
chunk (`checkLineL`, `checkFlatL`) goes through every line once more,
in order, at the counters the serial parse has there:

* a built line is checked as the eager check checks it (`exprCheck`),
  its children read through `lkEB`, which fails on a lazy entry;
* a lazy line's references are checked to be bound below the counters
  (`refsOK`) — then the serial parse's builder succeeds on it — and the
  line is copied, re-encoded, into the chunk's store (`LAcc`): the
  bytes a theorem's value is later built from;
* a theorem's record carries the placeholder `ph vid`, its value's
  index, which must be bound; every other record is built as the
  serial parse builds it, from built entries only.

`ConLeche/Verify/Frontend/Lazy.lean` proves that a chunk passing this
check is one more step of the serial parse, with the serial records
related to these (`DRel`), and that a value the builder below returns
(`buildVal`) is the serial table's entry.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## The theorem placeholder -/

/-- A theorem record's value in the lazy parse: the index of the
expression line its value is (`phId?` reads it back), and a hint where
its build starts (`phHint`; only a hint). -/
@[inline] def ph (vid hint : Nat) : Expr := .app (.bvar vid) (.bvar hint)

@[inline] def phId? : Expr → Option Nat
  | .app (.bvar i) _ => some i
  | _ => none

@[inline] def phHint : Expr → Nat
  | .app _ (.bvar h) => h
  | _ => 4294967295

/-! ## The check's lookups -/

/-- An expression lookup that answers BUILT entries only: a lazy entry
fails, like an unbound one. -/
@[inline] def lkEB (P : @& Prior) (b j : Nat) : Except String Expr :=
  match (if j < b then P.e.get j else none) with
  | some e => if isLazyE e then throw s!"lazy expr index {j}" else pure e
  | none => throw s!"undefined expr index {j}"

/-- Is expression index `j` bound (built or lazy) below the counter? -/
@[inline] def boundE (P : @& Prior) (b j : Nat) : Bool :=
  j < b && (P.e.get j).isSome

/-- Bit `i` of a bitmap. -/
@[inline] def bitGet (bm : @& ByteArray) (i : Nat) : Bool :=
  let b := i / 8
  if h : b < bm.size then (bm[b] >>> (i % 8).toUInt8) &&& 1 == 1 else false

/-- Is index `j` noted as needed by the lazy builds?  (An empty bitmap
notes every index.) -/
@[inline] def neededE (nd : @& ByteArray) (j : Nat) : Bool := nd.size == 0 || bitGet nd j

/-- Is expression index `j` bound below the counter, and, when built,
noted as needed (the store keeps exactly those, `RTab`)? -/
@[inline] def boundN (P : @& Prior) (nd : @& ByteArray) (b j : Nat) : Bool :=
  boundE P b j && (match P.e.get j with
    | some v => isLazyE v || neededE nd j
    | none => false)

/-- An answer is an `ok`. -/
@[inline] def isOk : Except ε α → Bool
  | .ok _ => true
  | .error _ => false

/-- **A lazy line's references**: every name and level it reads bound
below the counters, every expression bound (built or lazy). -/
@[inline] def refsOK (P : @& Prior) (nd : @& ByteArray) (c : Ctr) (x : @& ExprRec) : Bool :=
  match x with
  | .bvar _ => true
  | .sort u => isOk (lkL P c.l u)
  | .const n us => isOk (lkN P c.n n) && us.all fun u => isOk (lkL P c.l u)
  | .app f a => boundN P nd c.e f && boundN P nd c.e a
  | .lam ty bd pw => boundN P nd c.e ty && boundN P nd c.e bd &&
      isOk (pwOfF (lkN P c.n) (lkL P c.l) (lkEB P c.e) pw)
  | .forallE ty bd pw => boundN P nd c.e ty && boundN P nd c.e bd &&
      isOk (pwOfF (lkN P c.n) (lkL P c.l) (lkEB P c.e) pw)
  | .letE ty vl bd => boundN P nd c.e ty && boundN P nd c.e vl && boundN P nd c.e bd
  | .proj tn _ s => isOk (lkN P c.n tn) && boundN P nd c.e s
  | .natVal _ => true
  | .strVal _ => true

/-- A declaration record other than a theorem reads built entries only:
for an inductive block, every index it lists (`indExprIds`). -/
def declBuilt (P : @& Prior) (b : Nat) : DeclRec → Bool
  | .ind tys cts rcs => (indExprIds tys cts rcs).all fun j => isOk (lkEB P b j)
  | _ => true

/-! ## The chunk's store

The lazy lines of a chunk, re-encoded one after the other (`cd`), and
a sparse index: the index and byte offset of the line that starts each
REGION — the first lazy line after a declaration line, where the lines
of the next declaration's value begin — and of every 16th line after
it.  A theorem's placeholder names its region's entry (`hint`): its
value is built forward from there (`regionGo`). -/

/-- The check's accumulator: the chunk's records, its lazy lines, the
sparse index, the lines since its last entry, whether no lazy line
followed the last declaration line, and the current region's entry. -/
structure LAcc where
  ds : Array Declaration
  cd : ByteArray
  spId : Array Nat
  spOff : Array Nat
  nl : Nat
  fresh : Bool
  rg : Nat

/-- The sparse index's stride. -/
def spStride : Nat := 16

/-- No region (a hint past any sparse index). -/
def noHint : Nat := 4294967295

/-- An empty accumulator. -/
def LAcc.init : LAcc := ⟨#[], .empty, #[], #[], spStride, true, noHint⟩

/-- A lazy line, kept. -/
@[inline] def LAcc.lazy (a : LAcc) (i : Nat) (x : ExprRec) : LAcc :=
  match a with
  | ⟨ds, cd, si, so, nl, fresh, rg⟩ =>
    if fresh || spStride ≤ nl then
      -- RC linearity: the sizes are read BEFORE the buffers are pushed
      -- to (read after, `cd` is shared at the push and copied whole)
      let off := cd.size
      let rg := if fresh then so.size else rg
      ⟨ds, Flat.wLine cd (.expr i x), si.push i, so.push off, 1, false, rg⟩
    else ⟨ds, Flat.wLine cd (.expr i x), si, so, nl + 1, false, rg⟩

/-- A record, pushed (the next lazy line starts a region). -/
@[inline] def LAcc.push (a : LAcc) (d : Declaration) : LAcc :=
  match a with
  | ⟨ds, cd, si, so, nl, _, rg⟩ => ⟨ds.push d, cd, si, so, nl, true, rg⟩

/-- The current region's sparse entry, if a lazy line followed the last
declaration line. -/
@[inline] def LAcc.hint (a : LAcc) : Nat := if a.fresh then noHint else a.rg

/-! ## The check -/

/-- A theorem record (a record of another kind never builds one; the
check tests it all the same, so that the proofs need not). -/
@[inline] def isThmDecl : Declaration → Bool
  | .thmDecl .. => true
  | _ => false

/-- **One line, checked** at counters `c` against the finished tables
`P` (built and lazy entries): the counters after it and the
accumulator, or `none`. -/
@[inline] def checkLineL (P : @& Prior) (nd : @& ByteArray) (c : Ctr) (r : @& LineRec) (a : LAcc) :
    Option (Ctr × LAcc) :=
  match r with
  | .expr i x =>
    if c.e ≤ i && P.e.noneIn c.e i then
      match P.e.get i with
      | some v =>
        if isLazyE v then
          if refsOK P nd c x then some ({ c with e := i + 1 }, a.lazy i x) else none
        else if exprCheck (lkN P c.n) (lkL P c.l) (lkEB P c.e) x v then
          some ({ c with e := i + 1 }, a)
        else none
      | none => none
    else none
  | .decl (.thm cvr vid) =>
    match cvOfF (lkN P c.n) (lkL P c.l) (lkEB P c.e) cvr with
    | .ok cv => if boundN P nd c.e vid then some (c, a.push (.thmDecl cv (ph vid a.hint))) else none
    | .error _ => none
  | .decl d =>
    if declBuilt P c.e d then
      match declOfF (lkN P c.n) (lkL P c.l) (lkEB P c.e) d with
      | .ok (.inl x) => if isThmDecl x then none else some (c, a.push x)
      | _ => none
    else none
  | r =>
    match checkLine P c r with
    | some (c', _) => some (c', a)
    | none => none

/-- **The check of a list of lines** (the specification). -/
def checkListL (P : Prior) (nd : ByteArray) (c : Ctr) : List LineRec → LAcc → Option (Ctr × LAcc)
  | [], a => some (c, a)
  | r :: rs, a =>
    match checkLineL P nd c r a with
    | some (c', a') => checkListL P nd c' rs a'
    | none => none

/-- The check of a flat chunk: `k` records from machine-word position
`p`, each read where it is checked. -/
def checkFlatGoL (P : @& Prior) (nd : @& ByteArray) (d : @& ByteArray) (p : USize) (k : Nat)
    (c : Ctr) (a : LAcc) : Option (Ctr × LAcc) :=
  match k with
  | 0 => some (c, a)
  | k + 1 =>
    Flat.withLineU d p fun r q =>
      match checkLineL P nd c r a with
      | some (c', a') => checkFlatGoL P nd d q k c' a'
      | none => none

/-- A flat chunk's lines, checked from counters `c`. -/
def checkFlatL (P : @& Prior) (nd : @& ByteArray) (fc : @& FlatChunk) (c : Ctr) :
    Option (Ctr × LAcc) :=
  if fc.data.size < USize.size then checkFlatGoL P nd fc.data 0 fc.count c LAcc.init else none

/-- One chunk's lazy lines. -/
structure LChunk where
  cd : ByteArray
  spId : Array Nat
  spOff : Array Nat

/-- The lazy parse between windows: the finished tables and their
counters, the records so far, the line and byte counts, and the
chunks' stores so far. -/
structure LGSt where
  P : Prior
  c : Ctr
  ds : Array Declaration
  lineNo : Nat
  total : Nat
  S : Array LChunk

/-! ## The sweep

The scanned chunks are read backward, line by line (each chunk's line
starts indexed first, four bytes a line): an expression line marked in
`mk` marks its children; a declaration line marks what install reads
(statements, definitions' and opaques' values, inductive blocks).  An
unmarked line's children, and every theorem value, are noted in `nd`
(needed by the lazy builds).  The sweep validates nothing: what it
marks only decides what the rounds build. -/

/-- A bitmap of `n` zero bytes (doubling copies; `zeros` stops at 4 MiB). -/
def zeroBytes (n : Nat) : ByteArray :=
  go (zeros 64) 64
where
  go (b : ByteArray) : Nat → ByteArray
    | 0 => b.extract 0 n
    | fuel + 1 => if b.size ≥ n then b.extract 0 n else go (b ++ b) fuel

/-- Set bit `i` (no effect past the end). -/
@[inline] def bitSet (bm : ByteArray) (i : Nat) : ByteArray :=
  let b := i / 8
  if h : b < bm.size then bm.set b (bm[b] ||| ((1 : UInt8) <<< (i % 8).toUInt8)) h else bm

/-- The sweep's bitmaps. -/
structure SwMarks where
  mkd : ByteArray
  nd : ByteArray

@[inline] def SwMarks.mark (m : SwMarks) (i : Nat) : SwMarks :=
  match m with | ⟨a, b⟩ => ⟨bitSet a i, b⟩

@[inline] def SwMarks.need (m : SwMarks) (i : Nat) : SwMarks :=
  match m with | ⟨a, b⟩ => ⟨a, bitSet b i⟩

/-- The children of an expression line. -/
@[inline] def exprKids : ExprRec → List Nat
  | .app f a => [f, a]
  | .lam ty bd _ => [ty, bd]
  | .forallE ty bd _ => [ty, bd]
  | .letE ty v bd => [ty, v, bd]
  | .proj _ _ s => [s]
  | _ => []

/-- A declaration line's marks. -/
def markDecl (m : SwMarks) : DeclRec → SwMarks
  | .ax cv _ => m.mark cv.type
  | .defn cv v _ _ => (m.mark cv.type).mark v
  | .thm cv v => (m.mark cv.type).need v
  | .opaq cv v _ => (m.mark cv.type).mark v
  | .quot cv _ => m.mark cv.type
  | .ind tys cts rcs => (indExprIds tys cts rcs).foldl SwMarks.mark m

/-- One line of the sweep. -/
@[inline] def sweepLine (m : SwMarks) : LineRec → SwMarks
  | .expr i x =>
    if bitGet m.mkd i then (exprKids x).foldl SwMarks.mark m
    else (exprKids x).foldl SwMarks.need m
  | .decl d => markDecl m d
  | _ => m

/-- The line starts of a flat chunk (four bytes each), and its largest
expression index. -/
def lineStarts (fc : @& FlatChunk) : ByteArray × Nat :=
  if fc.data.size < USize.size then go fc.data 0 fc.count (ByteArray.emptyWithCapacity (4 * fc.count)) 0
  else (.empty, 0)
where
  go (d : @& ByteArray) (p : USize) (k : Nat) (acc : ByteArray) (mx : Nat) : ByteArray × Nat :=
    match k with
    | 0 => (acc, mx)
    | k + 1 =>
      let acc := (((acc.push p.toUInt32.toUInt8).push (p.toUInt32 >>> 8).toUInt8).push
        (p.toUInt32 >>> 16).toUInt8).push (p.toUInt32 >>> 24).toUInt8
      Flat.withLineU d p fun r q =>
        match r with
        | .expr i _ => go d q k acc (max mx i)
        | _ => go d q k acc mx

/-- One line of the sweep at byte `p`, decoded. -/
@[noinline] def sweepSlow (d : @& ByteArray) (p : USize) (m : SwMarks) : SwMarks :=
  Flat.withLineU d p fun r _ => sweepLine m r

/-- **The sweep of one chunk, backward**: lines `k - 1` down to `0`,
the two bitmaps threaded apart (no record per line).  The expression
lines with children (`app`, `lam`, `forallE`, `letE`, `proj`) are read
in place, their fields at fixed offsets; a declaration line, or a field
too large for four bytes, is decoded. -/
def sweepGo (d : @& ByteArray) (st : @& ByteArray) (k : Nat) (mk nd : ByteArray) : SwMarks :=
  match k with
  | 0 => ⟨mk, nd⟩
  | k + 1 =>
    let p := (get32 st (4 * k)).toUSize
    let t := Flat.byteU d p
    if t == 0 || t == 1 || t == 2 || t == 6 || t == 9 then
      let i := Flat.r4U d (p + 1)
      let a := Flat.r4U d (p + 5)
      let b := Flat.r4U d (p + 9)
      let c := if t == 6 || t == 9 then Flat.r4U d (p + 13) else 0
      if i == 0xFFFFFFFF || a == 0xFFFFFFFF || b == 0xFFFFFFFF || c == 0xFFFFFFFF then
        match sweepSlow d p ⟨mk, nd⟩ with
        | ⟨mk, nd⟩ => sweepGo d st k mk nd
      else if bitGet mk i.toNat then
        if t == 9 then sweepGo d st k (bitSet mk c.toNat) nd
        else
          let mk := bitSet (bitSet mk a.toNat) b.toNat
          sweepGo d st k (if t == 6 then bitSet mk c.toNat else mk) nd
      else
        if t == 9 then sweepGo d st k mk (bitSet nd c.toNat)
        else
          let nd := bitSet (bitSet nd a.toNat) b.toNat
          sweepGo d st k mk (if t == 6 then bitSet nd c.toNat else nd)
    else if t == 16 then
      match sweepSlow d p ⟨mk, nd⟩ with
      | ⟨mk, nd⟩ => sweepGo d st k mk nd
    else sweepGo d st k mk nd

/-- The sweep of one chunk. -/
@[inline] def sweepChunk (d : @& ByteArray) (st : @& ByteArray) (k : Nat) (m : SwMarks) :
    SwMarks :=
  match m with
  | ⟨mk, nd⟩ => sweepGo d st k mk nd

/-! ## The store and the builds

After the parse the store holds every chunk's lazy lines, the finished
tables (names, levels, and the built expressions) and the final
counters.  A theorem's value is built from it on demand
(`buildVal`): a lazy line is found by its index (`findLine`: the chunk
by binary search over the chunks' first indices, the line by the
sparse index and a short walk), its children built first, a built
entry read from the tables.  The memo is the build's own, dropped with
it. -/

/-- **The retained table**: the built expressions the lazy builds read
(a lazy line's built children, a theorem's built value), and nothing
else of the finished expression table — its pages are dropped after
the parse.  Index `j` is retained when its bit is set; its value is
the `rank`-th, the count of retained indices below it being the
block count of its 64-bit block (`cnt`, four bytes a block) plus the
bits set before it in the block.  Nothing here is trusted: the table
is validated against the finished tables once it is built
(`rtValid`). -/
structure RTab where
  bits : ByteArray
  cnt : ByteArray
  vals : Array Expr

/-- The set bits of a byte. -/
@[inline] def popc8 (x : UInt8) : Nat :=
  let x : UInt8 := x - ((x >>> 1) &&& (0x55 : UInt8))
  let x : UInt8 := (x &&& (0x33 : UInt8)) + ((x >>> 2) &&& (0x33 : UInt8))
  ((x + (x >>> 4)) &&& (0x0F : UInt8)).toNat

/-- The set bits of the bytes `[b, e)`. -/
def popcRange (bits : @& ByteArray) (b e : Nat) (acc : Nat) : Nat :=
  if b < e then popcRange bits (b + 1) e (acc + popc8 (bits.get! b)) else acc
termination_by e - b

/-- The retained indices below `j`. -/
@[inline] def RTab.rank (R : @& RTab) (j : Nat) : Nat :=
  let w := j / 64
  let full := popcRange R.bits (w * 8) (j / 8) (get32 R.cnt (4 * w))
  full + popc8 (R.bits.get! (j / 8) &&& (((1 : UInt8) <<< (j % 8).toUInt8) - 1))

/-- Index `j`'s retained value. -/
@[inline] def RTab.get (R : @& RTab) (j : Nat) : Option Expr :=
  if bitGet R.bits j then R.vals[R.rank j]? else none

/-- The retained table from the sweep's bitmaps (marked and needed) and
the finished tables: byte by byte, every set bit whose index is built
below the counter, its value pushed; a block count every eight bytes. -/
def RTab.build (mk nd : @& ByteArray) (P : @& Prior) (ce : Nat) : RTab :=
  go 0 (ByteArray.emptyWithCapacity (min mk.size nd.size)) .empty #[] 0
where
  go (b : Nat) (bits cnt : ByteArray) (vals : Array Expr) (n : Nat) : RTab :=
    if b < min mk.size nd.size then
      let cnt := if b % 8 == 0 then
          (((cnt.push n.toUInt32.toUInt8).push (n.toUInt32 >>> 8).toUInt8).push
            (n.toUInt32 >>> 16).toUInt8).push (n.toUInt32 >>> 24).toUInt8
        else cnt
      let x := mk.get! b &&& nd.get! b
      if x == 0 then go (b + 1) (bits.push 0) cnt vals n
      else
        let (y, vals, n) := bitsGo b x 0 0 vals n
        go (b + 1) (bits.push y) cnt vals n
    else ⟨bits, cnt, vals⟩
  termination_by min mk.size nd.size - b
  /-- The bits `t..7` of byte `b` (`x`), kept when built. -/
  bitsGo (b : Nat) (x : UInt8) (t : Nat) (y : UInt8) (vals : Array Expr) (n : Nat) :
      UInt8 × Array Expr × Nat :=
    if t < 8 then
      if (x >>> t.toUInt8) &&& 1 == 1 then
        let j := 8 * b + t
        match (if j < ce then P.e.get j else none) with
        | some v =>
          if isLazyE v then bitsGo b x (t + 1) y vals n
          else bitsGo b x (t + 1) (y ||| ((1 : UInt8) <<< t.toUInt8)) (vals.push v) (n + 1)
        | none => bitsGo b x (t + 1) y vals n
      else bitsGo b x (t + 1) y vals n
    else (y, vals, n)
  termination_by 8 - t

/-- **The retained table, validated**: every index it answers is built
in the finished tables below the counter, with that value (`==`, the
pointer comparison first). -/
def rtValid (R : @& RTab) (P : @& Prior) (ce : Nat) : Bool :=
  go 0
where
  go (j : Nat) : Bool :=
    if j < R.bits.size * 8 then
      (match R.get j with
       | some v =>
         match (if j < ce then P.e.get j else none) with
         | some w => !isLazyE w && v == w
         | none => false
       | none => true) && go (j + 1)
    else true
  termination_by R.bits.size * 8 - j

/-- The store. -/
structure LStore where
  chunks : Array LChunk
  /-- each chunk's first lazy index (chunks without lazy lines are left out) -/
  firsts : Array Nat
  /-- the finished tables' names and levels (no expressions) -/
  P : Prior
  c : Ctr
  rt : RTab

/-- A built expression of the store: the retained table's. -/
@[inline] def rtLk (S : @& LStore) (k : Nat) : Except String Expr :=
  match S.rt.get k with
  | some v => pure v
  | none => throw s!"expr index {k} not retained"

/-- The last position in `[lo, hi)` of a sorted array whose entry is
at most `j` (`lo` if none is). -/
def lastLE (a : @& Array Nat) (j lo hi : Nat) : Nat :=
  if lo + 1 < hi then
    let mid := (lo + hi) / 2
    if a.getD mid 0 ≤ j then lastLE a j mid hi else lastLE a j lo mid
  else lo
termination_by hi - lo

/-- From byte `p` of a chunk's lines, forward (at most `fuel` lines) to
the line binding `j`. -/
def walkTo (d : @& ByteArray) (j : Nat) (p : USize) : Nat → Option ExprRec
  | 0 => none
  | fuel + 1 =>
    if p < d.usize then
      -- the index is read first, the line built only when it is `j`
      let i := (Flat.rNatU d (p + 1)).1
      if i == j then
        Flat.withLineU d p fun r _ =>
          match r with
          | .expr i x => if i == j then some x else none
          | _ => none
      else if i < j then walkTo d j (Flat.lineEndU d p) fuel
      else none
    else none

/-- The lazy line binding `j`, in chunk `C`. -/
@[inline] def LChunk.find (C : @& LChunk) (j : Nat) : Option ExprRec :=
  if C.cd.size < USize.size && C.spId.size == C.spOff.size && 0 < C.spId.size then
    let s := lastLE C.spId j 0 C.spId.size
    walkTo C.cd j (C.spOff.getD s 0).toUSize (spStride + 1)
  else none

/-- The lazy line binding `j`, in the store. -/
@[inline] def LStore.find (S : @& LStore) (j : Nat) : Option ExprRec :=
  if 0 < S.firsts.size && S.firsts.size == S.chunks.size then
    let k := lastLE S.firsts j 0 S.firsts.size
    -- read BORROWED: `S.chunks[k]?` would hand out a reference, an
    -- atomic count on a chunk every worker reads
    if h : k < S.chunks.size then S.chunks[k].find j else none
  else none

/-- The builds' memo. -/
abbrev Memo := Std.HashMap Nat Expr

/-- A child's value during a build of index `j`: from the memo, or a
built entry of the tables. -/
@[inline] def memoLk (S : @& LStore) (memo : @& Memo) (j k : Nat) : Except String Expr :=
  if k < j then
    match memo.get? k with
    | some v => pure v
    | none => rtLk S k
  else throw s!"forward expr index {k}"

/-- The children of a line still to be built: lazy ones not in the
memo. -/
@[inline] def missingKids (S : @& LStore) (memo : @& Memo) (ks : List Nat) : List Nat :=
  ks.filter fun k => !memo.contains k && !isOk (rtLk S k)

/-- **The build**, with an explicit stack (no native recursion: a
value's DAG can be deep): the top index is built once its lazy
children are in the memo, else they are pushed above it. -/
def buildGo (S : @& LStore) : Nat → List Nat → Memo → Memo
  | 0, _, memo => memo
  | _ + 1, [], memo => memo
  | fuel + 1, j :: rest, memo =>
    if memo.contains j || isOk (rtLk S j) then buildGo S fuel rest memo
    else
      match S.find j with
      | none => memo
      | some x =>
        match missingKids S memo (exprKids x) with
        | [] =>
          match exprOfF (lkN S.P S.c.n) (lkL S.P S.c.l) (memoLk S memo j) x with
          | .ok v => buildGo S fuel rest (memo.insert j v)
          | .error _ => memo
        | ms =>
          if ms.all (· < j) then buildGo S fuel (ms ++ j :: rest) memo else memo

/-- The build's step budget: far beyond any value. -/
def buildFuel : Nat := 1 <<< 62

/-- **A value's region, built forward**: from byte `p` of a chunk's
lines, every line up to index `vid` whose children are done is built
(the others are left to `buildGo`). -/
def regionGo (S : @& LStore) (d : @& ByteArray) (vid : Nat) (p : USize) : Nat → Memo → Memo
  | 0, memo => memo
  | fuel + 1, memo =>
    if p < d.usize then
      Flat.withLineU d p fun r q =>
        match r with
        | .expr j x =>
          if vid < j then memo
          else
            let memo := if memo.contains j then memo else
              -- children outside the region (an earlier value's lines)
              -- first, on demand
              let memo := match missingKids S memo (exprKids x) with
                | [] => memo
                | ms => buildGo S buildFuel ms memo
              match exprOfF (lkN S.P S.c.n) (lkL S.P S.c.l) (memoLk S memo j) x with
              | .ok v => memo.insert j v
              | .error _ => memo
            if j == vid then memo else regionGo S d vid q fuel memo
        | _ => memo
    else memo

/-- The region pass's line budget. -/
def regionFuel : Nat := 1 <<< 24

/-- The region pass of a value in chunk `C`, from its hint. -/
@[inline] def regionIn (S : @& LStore) (C : @& LChunk) (vid hint : Nat) : Memo :=
  if h : C.cd.size < USize.size ∧ hint < C.spOff.size then
    regionGo S C.cd vid (C.spOff[hint]'h.2).toUSize regionFuel {}
  else {}

/-- The region pass of a value, from its hint. -/
def regionOf (S : @& LStore) (vid hint : Nat) : Memo :=
  if 0 < S.firsts.size && S.firsts.size == S.chunks.size then
    let k := lastLE S.firsts vid 0 S.firsts.size
    if h : k < S.chunks.size then regionIn S S.chunks[k] vid hint else {}
  else {}

/-- **A theorem value, built** from its index (and its region hint). -/
def buildVal (S : @& LStore) (vid hint : Nat) : Option Expr :=
  match rtLk S vid with
  | .ok v => some v
  | .error _ =>
    (buildGo S buildFuel [vid] (regionOf S vid hint)).get? vid

/-! ## Assembling the store, and filling the records -/

/-- The store of a finished parse: the chunks with lazy lines, their
first indices, the tables and counters. -/
def LStore.ofChunks (S : Array LChunk) (P : Prior) (c : Ctr) (rt : RTab) : LStore :=
  let cs := S.filter fun C => 0 < C.spId.size
  ⟨cs, cs.map fun C => C.spId.getD 0 0, ⟨P.n, P.l, ⟨#[]⟩⟩, c, rt⟩

/-- A run-time record with its theorem value built (`none`: the build
failed, or a theorem's value is not a placeholder). -/
def fillDecl (S : @& LStore) : Declaration → Option Declaration
  | .thmDecl cv w =>
    match phId? w with
    | some vid => (buildVal S vid (phHint w)).map (.thmDecl cv ·)
    | none => none
  | d => some d

/-- The records `[i, hi)`, filled, onto `acc`. -/
def fillRange (S : @& LStore) (ds : @& Array Declaration) (i hi : Nat) (acc : Array Declaration) :
    Option (Array Declaration) :=
  if i < hi then
    match fillDecl S ds[i]! with
    | some d => fillRange S ds (i + 1) hi (acc.push d)
    | none => none
  else some acc
termination_by hi - i

/-- A chunk's step of the serial parse from an empty carry, without the
chunk's bytes: what `chunkStepF` does with them when the chunk's scan
ended at its end. -/
def chunkStepNB (st : StateD) (lineNo total sz : Nat) (fc : @& FlatChunk) :
    Except (CheckError × Nat) (StateD × ByteArray × Nat × Nat) :=
  if total + sz ≥ USize.size then .error sizeError
  else
    match applyFlat st fc lineNo with
    | .error e => .error e
    | .ok (st, lineNo, _) => .ok (st, .empty, lineNo, total + sz)

/-- `chunkFits` from the chunk's size. -/
@[inline] def chunkFitsN (sz : Nat) (fc : @& FlatChunk) (total : Nat) : Bool :=
  match fc.stop with
  | .tail i => i.toNat == sz && total + sz < USize.size
  | _ => false

end ConLeche.Frontend
