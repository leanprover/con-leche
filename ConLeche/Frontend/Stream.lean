module

public import ConLeche.Frontend.ExportC
public import ConLeche.Frontend.CheckerIO

@[expose] public section

/-!
# The streaming parse: the serial driver, and the scan apart from the apply (task #329)

`feedChunk` (`ConLeche/Frontend/ExportC.lean`) reads a line and applies
it, then the next.  The two halves are not alike: the READ — the byte
recogniser, `scanLineSpec`, run as `scanLineFwd` — looks at the line's
bytes and nothing else, while the APPLY reads and extends the tables
every earlier line built.  The rounds parse
(`ConLeche/Driver/OwnerParse.lean`) scans a chunk once and works over
its records, so the two are taken apart here:

* `scanChunk` reads every complete line of a chunk into an array of
  syntax records and says where and why it stopped, without a state;
* `applyScanned` applies such an array to the state, in order, and
  reports the stop the way `feedChunk` reports it;
* `applyScanned_scanChunk`: the two together ARE `feedChunk` — map,
  then fold, is the fused fold;
* `chunkStepS` is `chunkStep` with the chunk's scan handed in, and
  `chunkStepS_scanChunk` says that handed the chunk's own scan it is
  `chunkStep`.

`Reached done` is the streaming invariant: the chunks `done` lead
`parseChunks` to the state at hand.  The serial parse `parseFileS`
folds every read of the file by `chunkStep` through the checker's IO
class (`CheckerIO.foldChunks`, `ConLeche/Frontend/CheckerIO.lean`); in
the model of the files the fold is `parseChunks` of the file's reads.
It is the parse at `--jobs=1`, and the rounds parse's fallback applies
its step (`ConLeche/Driver/StreamParse.lean`).
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
    match applyLine st rs[k] lineNo with
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
    match applyLine st r n with
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
    cases applyLine st r n with
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
      cases applyLine st' r n' with
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
      cases applyLine st' r n' with
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

/-! ## The streaming invariant -/

/-- The state the streaming parse has reached after the chunks `done`:
whatever chunks follow, the parse of all of them is the parse of the
rest from here. -/
def Reached (done : List ByteArray) (st : StateD) (carry : ByteArray) (lineNo total : Nat) :
    Prop :=
  ∀ rest : List ByteArray, parseChunks (done ++ rest) = parseChunks.go st carry lineNo total rest

theorem Reached.init : Reached [] .init .empty 0 0 := fun _ => rfl

theorem Reached.step {done st carry lineNo total} (h : Reached done st carry lineNo total)
    {c : ByteArray} {st' carry' lineNo' total'}
    (hs : chunkStep st carry lineNo total c = .ok (st', carry', lineNo', total')) :
    Reached (done ++ [c]) st' carry' lineNo' total' := by
  intro rest
  rw [List.append_assoc, List.singleton_append, h, parseChunks.go, hs]

theorem Reached.error {done st carry lineNo total} (h : Reached done st carry lineNo total)
    {c : ByteArray} {e} (hs : chunkStep st carry lineNo total c = .error e) :
    parseChunks (done ++ [c]) = .error e := by
  rw [h, parseChunks.go, hs]

theorem Reached.finish {done st carry lineNo total} (h : Reached done st carry lineNo total) :
    parseChunks done = chunkFinish st carry lineNo := by
  have := h []
  rw [List.append_nil] at this
  exact this

/-! ## The serial streaming parse -/

/-- The serial parse's state between reads: the tables, the carried
tail, the line and byte counts. -/
abbrev SerSt := StateD × ByteArray × Nat × Nat

/-- The serial parse's step on one read: `chunkStep`, a failure ending
the fold with its result. -/
@[inline] def serStep : SerSt → ByteArray → Except (Except (CheckError × Nat) ParseResultD) SerSt
  | (st, carry, lineNo, total), c =>
    match chunkStep st carry lineNo total c with
    | .error e => .error (.error e)
    | .ok s => .ok s

/-- The serial parse's end: `chunkFinish`. -/
@[inline] def serFin : SerSt → Except (CheckError × Nat) ParseResultD
  | (st, carry, lineNo, _) => chunkFinish st carry lineNo

/-- **The serial streaming parse of a file** (task #424): the reads of
`chunk` bytes folded by `chunkStep` (the fused scan and apply: no
record array is built, nothing crosses a thread), through the class's
`foldChunks`, which reads the file through a handle in order up to its
size, so the file must be a regular file (a pipe or FIFO has no size
before it is read: the class's `fileSize` throws on one, and the run
ends with exit 3).  The state is threaded as a plain value, so that the
tables stay uniquely referenced (task #78).  In the model the fold is
`parseChunks` of the file's reads (`ConLeche/Verify/Frontend/StreamModel.lean`),
and `parseChunks_ok_parseBytes` (`ConLeche/Verify/Frontend/Chunks.lean`)
says that the reads' boundaries do not matter. -/
def parseFileS {μ : Type → Type} [CheckerIO μ] (path : System.FilePath)
    (chunk : USize := chunkSize) : μ (Except (CheckError × Nat) ParseResultD) :=
  foldChunks path chunk ((StateD.init.markLinear, .empty, 0, 0) : SerSt) serStep serFin

end ConLeche.Frontend
