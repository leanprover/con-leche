module

public import ConLeche.Frontend.ExportC
public import ConLeche.Frontend.Flat

@[expose] public section

/-!
# The pipelined parse (task #329)

`feedChunk` (`ConLeche/Frontend/ExportC.lean`) reads a line and applies
it, then the next.  The two halves are not alike: the READ — the byte
recogniser, `scanLineSpec`, run as `scanLineFwd` — looks at the line's
bytes and nothing else, while the APPLY reads and extends the tables
every earlier line built.  The read is most of the parse's work, so it
is taken off the applying thread:

* `scanChunk` reads every complete line of a chunk into an array of
  syntax records and says where and why it stopped, without a state;
* `applyScanned` applies such an array to the state, in order, and
  reports the stop the way `feedChunk` reports it;
* `applyScanned_scanChunk`: the two together ARE `feedChunk` — map,
  then fold, is the fused fold;
* `chunkStepS` is `chunkStep` with the chunk's scan handed in, and
  `chunkStepS_scanChunk` says that handed the chunk's own scan it is
  `chunkStep`;
* what crosses from the scanning task to the applying thread is the
  same scan written FLAT (`FlatChunk`, a few byte buffers instead of
  an object per line): `scanFlat` writes it, `applyFlat` applies it,
  reading each record where it is applied, and `chunkStepF_of_encodes`
  says the flat step is `chunkStep`.

The driver `parseExportStreamP` reads the stream, cuts it at the last
newline of each read (so that a chunk's lines are complete and its
scan does not depend on the chunk before it), scans every chunk on a
worker task, and applies the chunks' scans in order on its own thread,
a bounded number of chunks ahead.  It is `parseChunks` of those chunks
— every step is `chunkStepF` of the chunk's own flat scan, which is
`chunkStep` — and it returns its result with the proof that
`parseChunks` of some list of chunks returns it, as `checkDeclsIO`
(`Main.lean`) returns its environment with the proof that the fold
returns it.
-/

namespace ConLeche.Frontend

open ConLeche

/-! ## The read half and the apply half -/

/-- Where a chunk's scan stopped, after its complete lines. -/
inductive ScanStop where
  /-- at a line start: the incomplete tail begins here (or the chunk ended) -/
  | tail (i : USize)
  /-- a malformed line, with a newline after it: the rendered message -/
  | err (msg : String)
  /-- the recogniser made no progress (never, by its own law) -/
  | noProgress

/-- A chunk's complete lines as syntax records, and where the scan
stopped. -/
structure ScannedChunk where
  recs : Array LineRec
  stop : ScanStop

/-- **The read half of `feedChunk`**: every complete line from `i`,
scanned and kept; no state.  Its branches are `feedChunk`'s, line for
line, with the apply taken out. -/
def scanChunkGo (b : @& ByteArray) (i : USize) (acc : Array LineRec) : ScannedChunk :=
  if _h : i < b.usize then
    match scanLineSpec b i with
    | .err e =>
      if newlineFrom b i then ⟨acc, .err (ScanErr.render ⟨e.offset - i.toNat, e.what⟩)⟩
      else ⟨acc, .tail i⟩
    | .ok r j =>
      if j == 0 then ⟨acc, .tail i⟩
      else if _hj : i < j then scanChunkGo b j (acc.push r)
      else ⟨acc.push r, .noProgress⟩
  else ⟨acc, .tail i⟩
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i _h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A chunk, scanned from its start. -/
def scanChunk (b : @& ByteArray) : ScannedChunk := scanChunkGo b 0 #[]

/-- The same scan with the record array's capacity given up front (a
hint: the capacity is not observable). -/
def scanChunkCap (cap : Nat) (b : @& ByteArray) : ScannedChunk :=
  scanChunkGo b 0 (Array.emptyWithCapacity cap)

theorem scanChunkCap_eq (cap : Nat) (b : ByteArray) : scanChunkCap cap b = scanChunk b := rfl

/-- **The apply half**: the records from index `k`, applied in order,
each failure at its line number. -/
def applyRecs (st : StateD) (rs : @& Array LineRec) (k : Nat) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × Nat) :=
  if h : k < rs.size then
    match applyLine st rs[k] with
    | .error msg => .error (.internal msg, lineNo + 1)
    | .ok (.inr v) => .error (v.toError, lineNo + 1)
    | .ok (.inl st) => applyRecs st rs (k + 1) (lineNo + 1)
  else .ok (st, lineNo)
termination_by rs.size - k

/-- A chunk's scan, applied: the records, then the stop, reported as
`feedChunk` reports it. -/
def applyScanned (st : StateD) (sc : @& ScannedChunk) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × Nat × USize) :=
  match applyRecs st sc.recs 0 lineNo with
  | .error e => .error e
  | .ok (st, n) =>
    match sc.stop with
    | .tail i => .ok (st, n, i)
    | .err msg => .error (.internal msg, n + 1)
    | .noProgress => .error (.internal "the line scanner made no progress", n)

/-! ## Map, then fold, is the fused fold -/

/-- The apply half over a list, for the proof. -/
def applyList (st : StateD) : List LineRec → Nat → Except (CheckError × Nat) (StateD × Nat)
  | [], n => .ok (st, n)
  | r :: rs, n =>
    match applyLine st r with
    | .error msg => .error (.internal msg, n + 1)
    | .ok (.inr v) => .error (v.toError, n + 1)
    | .ok (.inl st) => applyList st rs (n + 1)

theorem applyRecs_eq (st : StateD) (rs : Array LineRec) (k n : Nat) :
    applyRecs st rs k n = applyList st (rs.toList.drop k) n := by
  fun_induction applyRecs st rs k n with
  | case1 st k n h msg happ =>
    rw [List.drop_eq_getElem_cons (show k < rs.toList.length by simpa using h), applyList]
    simp [happ]
  | case2 st k n h v happ =>
    rw [List.drop_eq_getElem_cons (show k < rs.toList.length by simpa using h), applyList]
    simp [happ]
  | case3 st k n h st' happ ih =>
    rw [ih, List.drop_eq_getElem_cons (show k < rs.toList.length by simpa using h)]
    conv => rhs; rw [applyList]
    simp [happ]
  | case4 st k n h =>
    rw [List.drop_eq_nil_of_le (by simpa using h), applyList]

theorem applyList_append (st : StateD) (l₁ l₂ : List LineRec) (n : Nat) :
    applyList st (l₁ ++ l₂) n =
      match applyList st l₁ n with
      | .error e => .error e
      | .ok (st', n') => applyList st' l₂ n' := by
  induction l₁ generalizing st n with
  | nil => rfl
  | cons r l₁ ih =>
    simp only [List.cons_append, applyList]
    cases applyLine st r with
    | error msg => rfl
    | ok v => cases v with
      | inr v => rfl
      | inl st' => exact ih st' (n + 1)

/-- The read half from an accumulator, then the apply half: the
accumulator's records applied, then `feedChunk`. -/
theorem applyScanned_scanChunkGo (b : ByteArray) (i : USize) (acc : Array LineRec) :
    ∀ (st : StateD) (n : Nat),
    applyScanned st (scanChunkGo b i acc) n =
      match applyList st acc.toList n with
      | .error e => .error e
      | .ok (st', n') => feedChunk st' b i n' := by
  fun_induction scanChunkGo b i acc with
  | case1 i acc h e he hnl =>
    intro st n
    simp only [applyScanned, applyRecs_eq, List.drop_zero]
    cases applyList st acc.toList n with
    | error e => rfl
    | ok p => obtain ⟨st', n'⟩ := p; simp only []; rw [feedChunk, dite_eq_left_of_eq_true (eq_true h)]; simp [he, hnl]
  | case2 i acc h e he hnl =>
    intro st n
    simp only [applyScanned, applyRecs_eq, List.drop_zero]
    cases applyList st acc.toList n with
    | error e => rfl
    | ok p => obtain ⟨st', n'⟩ := p; simp only []; rw [feedChunk]; simp [he, hnl]
  | case3 i acc h r j hj hj0 =>
    intro st n
    simp only [applyScanned, applyRecs_eq, List.drop_zero]
    cases applyList st acc.toList n with
    | error e => rfl
    | ok p => obtain ⟨st', n'⟩ := p; simp only []; rw [feedChunk]; simp [hj, hj0]
  | case4 i acc h r j hj hj0 hij ih =>
    intro st n
    rw [ih, Array.toList_push, applyList_append]
    cases applyList st acc.toList n with
    | error e => rfl
    | ok p =>
      obtain ⟨st', n'⟩ := p
      simp only [applyList]
      conv => rhs; rw [feedChunk]
      simp only [h, hj, hj0, hij, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      cases applyLine st' r with
      | error msg => rfl
      | ok v => cases v with
        | inr v => rfl
        | inl st'' => rfl
  | case5 i acc h r j hj hj0 hij =>
    intro st n
    simp only [applyScanned, applyRecs_eq, List.drop_zero, Array.toList_push, applyList_append]
    cases applyList st acc.toList n with
    | error e => rfl
    | ok p =>
      obtain ⟨st', n'⟩ := p
      simp only [applyList]
      conv => rhs; rw [feedChunk]
      simp only [h, hj, hj0, hij, ↓reduceDIte, Bool.false_eq_true, ↓reduceIte]
      cases applyLine st' r with
      | error msg => rfl
      | ok v => cases v with
        | inr v => rfl
        | inl st'' => rfl
  | case6 i acc h =>
    intro st n
    simp only [applyScanned, applyRecs_eq, List.drop_zero]
    cases applyList st acc.toList n with
    | error e => rfl
    | ok p => obtain ⟨st', n'⟩ := p; simp only []; rw [feedChunk, dite_eq_right_of_eq_false (eq_false h)]

/-- **Map, then fold, is the fused fold**: a chunk's scan, applied, is
`feedChunk` from the chunk's start. -/
theorem applyScanned_scanChunk (st : StateD) (b : ByteArray) (n : Nat) :
    applyScanned st (scanChunk b) n = feedChunk st b 0 n := by
  rw [scanChunk, applyScanned_scanChunkGo]; rfl

/-! ## The chunk step with the scan handed in -/

/-- **`chunkStep`, with the chunk's scan handed in**: when no tail is
carried the chunk is the buffer and its scan is applied; a carried
tail (which the driver's newline cut never leaves) is put in front of
the chunk and the step is `chunkStep`'s own. -/
def chunkStepS (st : StateD) (carry : ByteArray) (lineNo total : Nat) (buf0 : ByteArray)
    (sc : @& ScannedChunk) : Except (CheckError × Nat) (StateD × ByteArray × Nat × Nat) :=
  if carry.isEmpty then
    if total + buf0.size ≥ USize.size then .error sizeError
    else
      match applyScanned st sc lineNo with
      | .error e => .error e
      | .ok (st, lineNo, tail) =>
        .ok (st, buf0.extract tail.toNat buf0.size, lineNo, total + buf0.size)
  else chunkStep st carry lineNo total buf0

/-- Handed the chunk's own scan, the step is `chunkStep`. -/
theorem chunkStepS_scanChunk (st : StateD) (carry : ByteArray) (lineNo total : Nat)
    (buf0 : ByteArray) :
    chunkStepS st carry lineNo total buf0 (scanChunk buf0) =
      chunkStep st carry lineNo total buf0 := by
  unfold chunkStepS chunkStep
  split
  · rename_i he
    simp only [applyScanned_scanChunk]
    rfl
  · rfl

/-! ## The flat scan (task #329, FLATSCAN)

What a scan task hands to the applying thread is `FlatChunk`: the
chunk's records written one after the other into ONE `ByteArray`
(`ConLeche/Frontend/Flat.lean`), their count, and the stop.  A task's
value is marked multi-threaded by the runtime, object by object, under
its one global lock, and every object of it then pays atomic reference
counts on the applying thread; a `ScannedChunk` is an object per line
and more, a `FlatChunk` three objects.  The applying thread reads each
record's fields back out of the bytes as it applies them, and builds
no record (`applyFlatGoU`, through `Flat.withLineU`).

`ScannedChunk` stays the specification: `FlatChunk.Encodes fc sc` says
that `fc`'s bytes are `sc`'s records, written; the flat scan encodes
the record scan (`scanFlat_encodes`), and applying a flat chunk is
applying what it encodes (`applyFlat_eq`). -/

/-- A chunk's scanned lines as bytes: `count` records written one after
the other into `data` (`Flat.wLine`), and where the scan stopped. -/
structure FlatChunk where
  data : ByteArray
  count : Nat
  stop : ScanStop

/-- `fc` holds `sc`: its bytes are `sc`'s records, written one after
the other, its count is theirs and its stop is `sc`'s. -/
def FlatChunk.Encodes (fc : FlatChunk) (sc : ScannedChunk) : Prop :=
  fc.data.data.toList = Flat.encElems Flat.encLine sc.recs.toList ∧
    fc.count = sc.recs.size ∧ fc.stop = sc.stop

/-- **The flat read half**: `scanChunkGo`, line for line, with each
record written into `d` instead of pushed onto an array. -/
def scanFlatGo (b : @& ByteArray) (i : USize) (d : ByteArray) (n : Nat) : FlatChunk :=
  if _h : i < b.usize then
    match scanLineSpec b i with
    | .err e =>
      if newlineFrom b i then ⟨d, n, .err (ScanErr.render ⟨e.offset - i.toNat, e.what⟩)⟩
      else ⟨d, n, .tail i⟩
    | .ok r j =>
      if j == 0 then ⟨d, n, .tail i⟩
      else if _hj : i < j then scanFlatGo b j (Flat.wLine d r) (n + 1)
      else ⟨Flat.wLine d r, n + 1, .noProgress⟩
  else ⟨d, n, .tail i⟩
termination_by b.size - i.toNat
decreasing_by
  exact Nat.sub_lt_sub_left (usizeInBounds b i _h) (USize.lt_iff_toNat_lt.mp _hj)

/-- A chunk, scanned flat from its start, into a buffer of the given
capacity (a hint: the capacity is not observable). -/
def scanFlat (cap : Nat) (b : @& ByteArray) : FlatChunk :=
  scanFlatGo b 0 (ByteArray.emptyWithCapacity cap) 0

theorem encElems_push (acc : Array LineRec) (r : LineRec) :
    Flat.encElems Flat.encLine (acc.push r).toList =
      Flat.encElems Flat.encLine acc.toList ++ Flat.encLine r := by
  rw [Array.toList_push]
  generalize acc.toList = l
  induction l with
  | nil => simp [Flat.encElems]
  | cons x l ih => simp [Flat.encElems, ih, List.append_assoc]

/-- The flat scan from a buffer that holds `acc` holds the record scan
from `acc`. -/
theorem scanFlatGo_encodes (b : ByteArray) (i : USize) (acc : Array LineRec) :
    ∀ (d : ByteArray), d.data.toList = Flat.encElems Flat.encLine acc.toList →
    (scanFlatGo b i d acc.size).Encodes (scanChunkGo b i acc) := by
  fun_induction scanChunkGo b i acc with
  | case1 i acc h e he hnl =>
    intro d hd
    rw [scanFlatGo, dite_eq_left_of_eq_true (eq_true h)]
    simp only [he, hnl, ↓reduceIte]
    exact ⟨hd, rfl, rfl⟩
  | case2 i acc h e he hnl =>
    intro d hd
    rw [scanFlatGo, dite_eq_left_of_eq_true (eq_true h)]
    simp only [he, hnl, Bool.false_eq_true, ↓reduceIte]
    exact ⟨hd, rfl, rfl⟩
  | case3 i acc h r j hj hj0 =>
    intro d hd
    rw [scanFlatGo, dite_eq_left_of_eq_true (eq_true h)]
    simp only [hj, hj0, ↓reduceIte]
    exact ⟨hd, rfl, rfl⟩
  | case4 i acc h r j hj hj0 hij ih =>
    intro d hd
    rw [scanFlatGo, dite_eq_left_of_eq_true (eq_true h)]
    simp only [hj, hj0, Bool.false_eq_true, ↓reduceIte, hij, ↓reduceDIte]
    have := ih (Flat.wLine d r) (by rw [Flat.wLine_spec, hd, encElems_push])
    rw [Array.size_push] at this
    exact this
  | case5 i acc h r j hj hj0 hij =>
    intro d hd
    rw [scanFlatGo, dite_eq_left_of_eq_true (eq_true h)]
    simp only [hj, hj0, Bool.false_eq_true, ↓reduceIte, hij, ↓reduceDIte]
    exact ⟨by rw [Flat.wLine_spec, hd, encElems_push], by simp, rfl⟩
  | case6 i acc h =>
    intro d hd
    rw [scanFlatGo, dite_eq_right_of_eq_false (eq_false h)]
    exact ⟨hd, rfl, rfl⟩

/-- **The flat scan holds the record scan.** -/
theorem scanFlat_encodes (cap : Nat) (b : ByteArray) : (scanFlat cap b).Encodes (scanChunk b) :=
  scanFlatGo_encodes b 0 #[] _ (by simp [ByteArray.emptyWithCapacity, Flat.encElems]; rfl)

/-- The applying step's result, as `applyRecs` reports it. -/
@[inline] def applyCont (st : StateD) (r : LineRec) (lineNo : Nat)
    (k : StateD → Except (CheckError × Nat) (StateD × Nat)) :
    Except (CheckError × Nat) (StateD × Nat) :=
  match applyLine st r with
  | .error msg => .error (.internal msg, lineNo + 1)
  | .ok (.inr v) => .error (v.toError, lineNo + 1)
  | .ok (.inl st) => k st

/-- **The flat apply half**: `k` records from machine-word position `p`
of `d`, applied in order, each read where it is applied
(`Flat.withLineU`: with the continuation inlined the record is never
built). -/
def applyFlatGoU (st : StateD) (d : @& ByteArray) (p : USize) (k : Nat) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × Nat) :=
  match k with
  | 0 => .ok (st, lineNo)
  | k + 1 =>
    Flat.withLineU d p fun r q =>
      applyCont st r lineNo fun st => applyFlatGoU st d q k (lineNo + 1)

/-- The same with `Nat` positions and the specification's readers: what
runs on a buffer too large for a machine word (never, in practice). -/
def applyFlatGo (st : StateD) (d : @& ByteArray) (p : Nat) (k : Nat) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × Nat) :=
  match k with
  | 0 => .ok (st, lineNo)
  | k + 1 =>
    Flat.withLine d p fun r q =>
      applyCont st r lineNo fun st => applyFlatGo st d q k (lineNo + 1)

theorem applyList_cons (st : StateD) (r : LineRec) (rs : List LineRec) (n : Nat) :
    applyList st (r :: rs) n = applyCont st r n fun st => applyList st rs (n + 1) := by
  simp only [applyList, applyCont]

theorem applyFlatGoU_eq (d : ByteArray) (hd : d.size < USize.size) (L : List LineRec) :
    ∀ (st : StateD) (p : USize) (n : Nat) (rest : List UInt8),
    d.data.toList.drop p.toNat = Flat.encElems Flat.encLine L ++ rest →
    applyFlatGoU st d p L.length n = applyList st L n := by
  induction L with
  | nil => intro st p n rest _; rfl
  | cons r L ih =>
    intro st p n rest h
    simp only [Flat.encElems, List.append_assoc] at h
    obtain ⟨q, e, hq⟩ := Flat.withLineU_spec r d hd p _ h
      (fun r q => applyCont st r n fun st => applyFlatGoU st d q L.length (n + 1))
    have h' := Flat.drop_after h
    rw [← hq] at h'
    rw [List.length_cons, applyFlatGoU, e, applyList_cons]
    simp only [applyCont]
    split <;> try rfl
    exact ih _ q _ rest h'

theorem applyFlatGo_eq (d : ByteArray) (L : List LineRec) :
    ∀ (st : StateD) (p : Nat) (n : Nat) (rest : List UInt8),
    d.data.toList.drop p = Flat.encElems Flat.encLine L ++ rest →
    applyFlatGo st d p L.length n = applyList st L n := by
  induction L with
  | nil => intro st p n rest _; rfl
  | cons r L ih =>
    intro st p n rest h
    simp only [Flat.encElems, List.append_assoc] at h
    obtain ⟨e, h'⟩ := (Flat.rdLine r).run h
    rw [List.length_cons, applyFlatGo, Flat.withLine_eq, e, applyList_cons]
    simp only [applyCont]
    split <;> try rfl
    exact ih _ _ _ rest h'

/-- A flat chunk, applied: the records, then the stop, as
`applyScanned` reports them.  A buffer whose size is a machine word
(always, in practice: the test is once per chunk) is read with the
fast readers. -/
def applyFlat (st : StateD) (fc : @& FlatChunk) (lineNo : Nat) :
    Except (CheckError × Nat) (StateD × Nat × USize) :=
  let r := if fc.data.size < USize.size then applyFlatGoU st fc.data 0 fc.count lineNo
    else applyFlatGo st fc.data 0 fc.count lineNo
  match r with
  | .error e => .error e
  | .ok (st, n) =>
    match fc.stop with
    | .tail i => .ok (st, n, i)
    | .err msg => .error (.internal msg, n + 1)
    | .noProgress => .error (.internal "the line scanner made no progress", n)

/-- **Applying a flat chunk is applying the scan it holds.** -/
theorem applyFlat_eq (st : StateD) (fc : FlatChunk) (sc : ScannedChunk) (h : fc.Encodes sc)
    (n : Nat) : applyFlat st fc n = applyScanned st sc n := by
  obtain ⟨hd, hc, hs⟩ := h
  have hr : (if fc.data.size < USize.size then applyFlatGoU st fc.data 0 fc.count n
      else applyFlatGo st fc.data 0 fc.count n) = applyList st sc.recs.toList n := by
    rw [hc, ← Array.length_toList]
    split
    · exact applyFlatGoU_eq fc.data (by assumption) _ st 0 n [] (by simp [hd])
    · exact applyFlatGo_eq fc.data _ st 0 n [] (by simp [hd])
  simp only [applyFlat, applyScanned, applyRecs_eq, List.drop_zero, hr, hs]

/-- `chunkStepS` with a flat scan handed in. -/
def chunkStepF (st : StateD) (carry : ByteArray) (lineNo total : Nat) (buf0 : ByteArray)
    (fc : @& FlatChunk) : Except (CheckError × Nat) (StateD × ByteArray × Nat × Nat) :=
  if carry.isEmpty then
    if total + buf0.size ≥ USize.size then .error sizeError
    else
      match applyFlat st fc lineNo with
      | .error e => .error e
      | .ok (st, lineNo, tail) =>
        .ok (st, buf0.extract tail.toNat buf0.size, lineNo, total + buf0.size)
  else chunkStep st carry lineNo total buf0

/-- Handed a flat scan that holds the chunk's own scan, the step is
`chunkStep`. -/
theorem chunkStepF_of_encodes (st : StateD) (carry : ByteArray) (lineNo total : Nat)
    (buf0 : ByteArray) (fc : FlatChunk) (h : fc.Encodes (scanChunk buf0)) :
    chunkStepF st carry lineNo total buf0 fc = chunkStep st carry lineNo total buf0 := by
  rw [← chunkStepS_scanChunk]
  unfold chunkStepF chunkStepS
  simp only [applyFlat_eq st fc _ h]

/-! ## The streaming invariant -/

/-- The state the streaming parse has reached: some list of chunks
leads `parseChunks` to it — whatever chunks follow, the parse of all
of them is the parse of the rest from here. -/
def Reached (st : StateD) (carry : ByteArray) (lineNo total : Nat) : Prop :=
  ∃ done : List ByteArray, ∀ rest : List ByteArray,
    parseChunks (done ++ rest) = parseChunks.go st carry lineNo total rest

theorem Reached.init : Reached .init .empty 0 0 := ⟨[], fun _ => rfl⟩

theorem Reached.step {st carry lineNo total} (h : Reached st carry lineNo total)
    {c : ByteArray} {st' carry' lineNo' total'}
    (hs : chunkStep st carry lineNo total c = .ok (st', carry', lineNo', total')) :
    Reached st' carry' lineNo' total' := by
  obtain ⟨done, hd⟩ := h
  refine ⟨done ++ [c], fun rest => ?_⟩
  rw [List.append_assoc, List.singleton_append, hd, parseChunks.go, hs]

theorem Reached.error {st carry lineNo total} (h : Reached st carry lineNo total)
    {c : ByteArray} {e} (hs : chunkStep st carry lineNo total c = .error e) :
    ∃ cs, parseChunks cs = .error e := by
  obtain ⟨done, hd⟩ := h
  refine ⟨done ++ [c], ?_⟩
  rw [hd, parseChunks.go, hs]

theorem Reached.finish {st carry lineNo total} (h : Reached st carry lineNo total) :
    ∃ cs, parseChunks cs = chunkFinish st carry lineNo := by
  obtain ⟨done, hd⟩ := h
  have := hd []
  rw [List.append_nil] at this
  exact ⟨done, this⟩

/-! ## The driver -/

/-- A chunk handed to a worker: the task's value is the chunk and its
own scan, flat. -/
abbrev ScanTask :=
  { t : Task (ByteArray × FlatChunk) // t.get.2.Encodes (scanChunk t.get.1) }

/-- The parse result with the evidence that `parseChunks` returns it. -/
abbrev ParseOutcome := { r : Except (CheckError × Nat) ParseResultD // ∃ cs, parseChunks cs = r }

instance : Nonempty ParseOutcome := ⟨⟨parseChunks [], [], rfl⟩⟩

/-- The last newline of `b` below `i`. -/
def lastNewlineBelow (b : @& ByteArray) : Nat → Option Nat
  | 0 => none
  | i + 1 => if b.get! i == 10 then some i else lastNewlineBelow b i

/-- The chunk `pending ++ buf0[0, k)`, built on the worker, and its
flat scan.  `spent`, the scan the applying thread last finished with,
is dropped HERE, on the worker (its buffer's size is the next one's
capacity). -/
def spawnScan (spent : Option ScanTask) (pending buf0 : ByteArray) (k : Nat) : ScanTask :=
  ⟨Task.spawn fun _ =>
    let cap := match spent with
      | some t => t.val.get.2.data.size
      | none => 0
    let blk := if pending.isEmpty then buf0.extract 0 k else pending ++ buf0.extract 0 k
    (blk, scanFlat cap blk), scanFlat_encodes _ _⟩

/-- Fill the queue: read until `inflight` chunks are in flight or the
stream has ended; returns the queue, its length, the spent scan, the
leftover bytes and whether the stream ended. -/
partial def fillQ (h : IO.FS.Handle) (inflight : Nat) (chunk : USize)
    (q : Std.Queue ScanTask) (n : Nat) (spent : Option ScanTask) (pending : ByteArray)
    (eof : Bool) : IO (Std.Queue ScanTask × Nat × Option ScanTask × ByteArray × Bool) := do
  if eof || n ≥ inflight then return (q, n, spent, pending, eof)
  let buf0 ← h.read chunk
  if buf0.isEmpty then
    -- the end: the leftover bytes, if any, are the last chunk
    if pending.isEmpty then return (q, n, spent, pending, true)
    else return (q.enqueue (spawnScan spent pending .empty 0), n + 1, none, .empty, true)
  else
    match lastNewlineBelow buf0 buf0.size with
    | none => fillQ h inflight chunk q n spent (pending ++ buf0) false
    | some k =>
      let t := spawnScan spent pending buf0 (k + 1)
      fillQ h inflight chunk (q.enqueue t) (n + 1) none (buf0.extract (k + 1) buf0.size) false

/-- The applying loop of the pipelined parse, from a reached state (the
rounds parse falls back to it, `ConLeche/Driver/ParParse.lean`). -/
partial def loopP (h : IO.FS.Handle) (inflight : Nat) (chunk : USize) (st : StateD)
    (carry : ByteArray) (lineNo total : Nat) (hr : Reached st carry lineNo total)
    (q : Std.Queue ScanTask) (n : Nat) (spent : Option ScanTask) (pending : ByteArray)
    (eof : Bool) : IO ParseOutcome := do
  let (q, n, spent, pending, eof) ← fillQ h inflight chunk q n spent pending eof
  match q.dequeue? with
  | none => return ⟨chunkFinish st carry lineNo, hr.finish⟩
  | some (t, q) =>
    match hs : chunkStepF st carry lineNo total t.val.get.1 t.val.get.2 with
    | .error e =>
      return ⟨.error e, hr.error (c := t.val.get.1) (by
        rw [← chunkStepF_of_encodes _ _ _ _ _ _ t.property]; exact hs)⟩
    | .ok (st', carry', lineNo', total') =>
      loopP h inflight chunk st' carry' lineNo' total' (hr.step (c := t.val.get.1) (by
        rw [← chunkStepF_of_encodes _ _ _ _ _ _ t.property]; exact hs))
        q (n - 1) (some t) pending eof

/-- **The pipelined streaming parse.**  The handle is read strictly
forward, `chunk` bytes at a time, never seeked or re-opened (the
source may be a pipe; `Main.lean`).  Each read is cut at its last
newline: the bytes before it, behind the bytes the previous reads left
over, are a chunk of complete lines, handed to a worker task that
copies and scans it flat (`spawnScan`); the bytes after it wait for the
next read.  At most `inflight` chunks are being scanned ahead.  The
applying loop takes the chunks in order and applies each one's scan to
the parse state (`chunkStepF`), threading the state as a plain argument
so that the tables stay uniquely referenced (task #78).

Every step is `chunkStepF` of a chunk's own flat scan, which is
`chunkStep` (`chunkStepF_of_encodes`), and the loop carries `Reached`:
what it returns is what `parseChunks` returns on the chunks it applied
(`ParseOutcome`).  Which chunks those are is the cut's business, and
`parseChunks_ok_parseBytes` (`ConLeche/Verify/Frontend/Chunks.lean`)
says it does not matter. -/
def parseExportHandleP (h : IO.FS.Handle) (inflight : Nat)
    (chunk : USize := chunkSize) : IO ParseOutcome :=
  loopP h inflight chunk .init .empty 0 0 .init ∅ 0 none .empty false

/-- The pipelined streaming parse of a file. -/
def parseExportStreamP (path : System.FilePath) (inflight : Nat)
    (chunk : USize := chunkSize) : IO ParseOutcome := do
  parseExportHandleP (← IO.FS.Handle.mk path .read) inflight chunk

end ConLeche.Frontend
