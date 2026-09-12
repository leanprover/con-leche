module

public import ConLeche.Verify.Frontend.Lines

public section

/-!
# The chunk boundary is invisible (task #290)

The binary reads its input in chunks (`parseExportHandleD`, 4 MiB at a
time) and feeds each through `chunkStep` — every complete line of the
buffer, the incomplete tail carried into the next chunk.  `parseChunks`
is that loop over a list of chunks, purely, and this module proves
that it computes the wholesale parse of the concatenation:

* `feedChunk_prefix`: feeding a buffer whose input is followed by more
  bytes parses the buffer's complete lines exactly as the wholesale
  parse of the longer input does, and stops where the wholesale parse
  continues.  This is where the line locality of
  `ConLeche/Verify/Frontend/Local.lean` is used in full: a line is read
  the same whatever follows its newline, so a chunk boundary after the
  newline changes nothing.
* `feedChunk_tail_nonl`: the carried tail holds no newline — the
  invariant that makes the last chunk's `chunkFinish` the wholesale
  parse's final line.
* `parseChunks_eq_parseExportD`: the two parses agree, for every
  chunking of a file that fits in the address space.
-/

namespace ConLeche.Frontend

theorem newlineFrom_iff (b : ByteArray) (i : USize) : newlineFrom b i = true ↔ 10 ∈ tailAt b i := by
  fun_induction newlineFrom b i with
  | case1 i h ih =>
    rw [tailAt_of_lt h, List.mem_cons, ← ih]
    simp only [Bool.or_eq_true, beq_iff_eq]
    constructor
    · rintro (h | h)
      · exact .inl h.symm
      · exact .inr h
    · rintro (h | h)
      · exact .inl h.symm
      · exact .inr h
  | case2 i h => rw [tailAt_of_not_lt h]; simp

/-- The bytes of a buffer whose input is followed by more: feeding the
buffer parses its complete lines as the wholesale parse does, and stops
where the wholesale parse continues. -/
theorem feedChunk_prefix (st : StateD) (b : ByteArray) (i : USize) (lineNo : Nat)
    (m : List UInt8) :
    parseLines st (tailAt b i ++ m) lineNo =
      match feedChunk st b i lineNo with
      | .error e => .error e
      | .ok (st', lineNo', tail) => parseLines st' (tailAt b tail ++ m) lineNo' := by
  fun_induction feedChunk st b i lineNo with
  | case1 st i lineNo h e he hnl =>
    -- a scan error, with a newline in the tail: the same error, at the same byte
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r, rest, hnv, hs⟩ |
      ⟨r, rest, hnv, hs, _⟩
    · rw [hs] at he; injection he with he; subst he
      obtain ⟨pre, x, hpx, hpre⟩ := split_first_nl ((newlineFrom_iff b i).mp hnl)
      rcases naiveLine_local pre hpre with ⟨r₀, h₀⟩ | ⟨t', r', hr', h₀⟩
      · rw [hpx, h₀ x] at hnv; simp at hnv
      · rw [hpx, h₀ x] at hnv
        injection hnv with hnv1 hnv2; subst hnv1; subst hnv2
        rw [hpx, List.append_assoc, List.cons_append, parseLines.eq_def, h₀ (x ++ m)]
        simp only [posAt]
        have := hr'.length_le
        congr 3
        simp only [List.length_append, List.length_cons, ScanErr.mk.injEq, and_true]
        omega
    · rw [hs] at he; simp at he
    · rw [hs] at he; simp at he
  | case2 st i lineNo h e he hnl => rfl
  | case3 st i lineNo h r j hj hj0 => rfl
  | case4 st i lineNo h r j hj hj0 msg happ =>
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2; simp at hj0
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj1
      obtain ⟨pre, hpx, hpre, _⟩ := naiveLine_some hnv
      rcases naiveLine_local pre hpre with ⟨r₀, h₀⟩ | ⟨t', r'', _, h₀⟩
      · rw [hpx, h₀ rest] at hnv; injection hnv with hnv1; injection hnv1 with hnv1; subst hnv1
        rw [hpx, List.append_assoc, List.cons_append, parseLines_line (h₀ (rest ++ m)), happ]
      · rw [hpx, h₀ rest] at hnv; simp at hnv
  | case5 st i lineNo h r j hj hj0 v happ =>
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2; simp at hj0
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj1
      obtain ⟨pre, hpx, hpre, _⟩ := naiveLine_some hnv
      rcases naiveLine_local pre hpre with ⟨r₀, h₀⟩ | ⟨t', r'', _, h₀⟩
      · rw [hpx, h₀ rest] at hnv; injection hnv with hnv1; injection hnv1 with hnv1; subst hnv1
        rw [hpx, List.append_assoc, List.cons_append, parseLines_line (h₀ (rest ++ m)), happ]
      · rw [hpx, h₀ rest] at hnv; simp at hnv
  | case6 st i lineNo h r j hj hj0 st' happ hij ih =>
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _, _, _, htail⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2; simp at hj0
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj1; subst hj2
      obtain ⟨pre, hpx, hpre, _⟩ := naiveLine_some hnv
      rcases naiveLine_local pre hpre with ⟨r₀, h₀⟩ | ⟨t', r'', _, h₀⟩
      · rw [hpx, h₀ rest] at hnv; injection hnv with hnv1; injection hnv1 with hnv1; subst hnv1
        rw [hpx] at ih htail ⊢
        rw [List.append_assoc, List.cons_append, parseLines_line (h₀ (rest ++ m)), happ,
          ← ih, htail]
      · rw [hpx, h₀ rest] at hnv; simp at hnv
  | case7 st i lineNo h r j hj hj0 st' happ hij =>
    exfalso
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _, hpos, hnat, _⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2; simp at hj0
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2
      exact hij (USize.lt_iff_toNat_lt.mpr (by rw [hnat]; exact hpos))
  | case8 st i lineNo h => rfl

/-- The carried tail holds no newline. -/
theorem feedChunk_tail_nonl {st st' : StateD} {b : ByteArray} {i tail : USize} {lineNo lineNo' : Nat}
    (h : feedChunk st b i lineNo = .ok (st', lineNo', tail)) : 10 ∉ tailAt b tail := by
  fun_induction feedChunk st b i lineNo with
  | case1 st i lineNo hi e he hnl => simp at h
  | case2 st i lineNo hi e he hnl =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    exact fun hm => hnl ((newlineFrom_iff b i).mpr hm)
  | case3 st i lineNo hi r j hj hj0 =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    have hi' : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp hi)
    rcases scanLineSpec_cases b i hi' with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _, hpos, hnat, _⟩
    · rw [hs] at hj; simp at hj
    · exact naiveLine_none hnv
    · exfalso
      rw [hs] at hj; injection hj with hj1 hj2; subst hj2
      have : (posAt i.toNat (tailAt b i) rest).toUSize = 0 := by simpa using hj0
      have := congrArg USize.toNat this
      rw [hnat] at this
      simp at this; omega
  | case4 st i lineNo hi r j hj hj0 msg happ => simp at h
  | case5 st i lineNo hi r j hj hj0 v happ => simp at h
  | case6 st i lineNo hi r j hj hj0 st' happ hij ih => exact ih h
  | case7 st i lineNo hi r j hj hj0 st' happ hij => simp at h
  | case8 st i lineNo hi =>
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, _, rfl⟩ := h
    rw [tailAt_of_not_lt hi]; exact List.not_mem_nil

/-! ## Bytes of buffers -/

theorem bytes_empty : bytes ByteArray.empty = [] := rfl

theorem bytes_of_isEmpty {b : ByteArray} (h : b.isEmpty = true) : bytes b = [] := by
  have : b.size = 0 := by simp only [ByteArray.isEmpty, beq_iff_eq] at h; exact h
  simp only [bytes, List.take_eq_nil_iff, Array.toList_eq_nil_iff]
  right
  exact Array.size_eq_zero_iff.mp this

theorem eq_empty_of_isEmpty {b : ByteArray} (h : b.isEmpty = true) : b = ByteArray.empty := by
  have : b.size = 0 := by simp only [ByteArray.isEmpty, beq_iff_eq] at h; exact h
  apply ByteArray.ext
  exact Array.size_eq_zero_iff.mp this

theorem bytes_append {a b : ByteArray} (h : (a ++ b).size < USize.size) :
    bytes (a ++ b) = bytes a ++ bytes b := by
  rw [ByteArray.size_append] at h
  rw [bytes_eq_of_size_lt (by rw [ByteArray.size_append]; exact h),
    bytes_eq_of_size_lt (by omega), bytes_eq_of_size_lt (by omega), ByteArray.data_append,
    Array.toList_append]

theorem tailAt_zero (b : ByteArray) : tailAt b 0 = bytes b := by
  simp [tailAt]

/-- The carried tail's bytes are the tail of the buffer. -/
theorem bytes_extract_tail {b : ByteArray} (t : USize) (h : b.size < USize.size) :
    bytes (b.extract t.toNat b.size) = tailAt b t := by
  have hsz : (b.extract t.toNat b.size).size ≤ b.size := by
    rw [ByteArray.size_extract]; omega
  rw [bytes_eq_of_size_lt (by omega), tailAt, bytes_eq_of_size_lt h, ByteArray.data_extract,
    Array.toList_extract, List.extract_eq_take_drop, List.take_of_length_le]
  simp only [List.length_drop, Array.length_toList]
  have : b.size = b.data.size := rfl
  omega

/-! ## The loop -/

/-- The chunked loop, from any carry without a newline, is the line fold
of the carry followed by the chunks. -/
theorem parseChunks_go :
    ∀ (cs : List ByteArray) (st : StateD) (carry : ByteArray) (lineNo : Nat),
    (∀ c ∈ cs, c.isEmpty = false) → 10 ∉ bytes carry →
    carry.size + (concatBytes cs).size < USize.size →
    parseChunks.go st carry lineNo cs =
      (parseLines st (bytes carry ++ bytes (concatBytes cs)) lineNo).map ParseResultD.ofState := by
  intro cs
  induction cs with
  | nil =>
    intro st carry lineNo _ hnl hsz
    simp only [parseChunks.go, chunkFinish, concatBytes, bytes_empty, List.append_nil]
    split
    · rename_i he
      rw [bytes_of_isEmpty he, parseLines, naiveLine_nil]
      rfl
    · have hcs : carry.size < USize.size := by simpa [concatBytes] using hsz
      have hi : (0 : USize).toNat ≤ (bytes carry).length := by simp
      rw [← tailAt_zero]
      rcases scanLineSpec_cases carry 0 hi with ⟨t, rest, hnv, hs⟩ | ⟨r, rest, hnv, hs⟩ |
        ⟨r, rest, hnv, hs, _⟩
      · rw [parseLines, hnv]
        simp only [applyFinalLine, hs, posAt, USize.toNat_zero, Nat.zero_add, Nat.sub_zero]
        rfl
      · rw [parseLines, hnv]
        simp only [applyFinalLine, hs]
        cases applyLine st r with
        | error msg => rfl
        | ok v => cases v <;> rfl
      · exfalso
        obtain ⟨pre, hpx, _, _⟩ := naiveLine_some hnv
        rw [tailAt_zero] at hpx
        exact hnl (hpx ▸ List.mem_append.mpr (.inr (List.mem_cons_self ..)))
  | cons c cs ih =>
    intro st carry lineNo hne hnl hsz
    have hc : c.isEmpty = false := hne c (List.mem_cons_self ..)
    simp only [parseChunks.go, hc, Bool.false_eq_true, ↓reduceIte, chunkStep]
    -- the buffer is `carry ++ c` either way
    have hbuf : (if carry.isEmpty = true then c else carry ++ c) = carry ++ c := by
      split
      · rename_i he; rw [eq_empty_of_isEmpty he, ByteArray.empty_append]
      · rfl
    rw [hbuf]
    have hsz' : (carry ++ c).size < USize.size := by
      simp only [ByteArray.size_append, concatBytes] at hsz ⊢; omega
    have hbytes : bytes carry ++ bytes (concatBytes (c :: cs)) =
        tailAt (carry ++ c) 0 ++ bytes (concatBytes cs) := by
      rw [tailAt_zero, bytes_append hsz', concatBytes, bytes_append (by
        simp only [ByteArray.size_append, concatBytes] at hsz ⊢; omega), List.append_assoc]
    rw [hbytes, feedChunk_prefix st (carry ++ c) 0 lineNo (bytes (concatBytes cs))]
    cases hf : feedChunk st (carry ++ c) 0 lineNo with
    | error e => rfl
    | ok p =>
      obtain ⟨st', lineNo', tail⟩ := p
      simp only
      rw [ih st' (( carry ++ c).extract tail.toNat (carry ++ c).size) lineNo'
        (fun c' hc' => hne c' (List.mem_cons_of_mem _ hc'))
        (by rw [bytes_extract_tail tail hsz']; exact feedChunk_tail_nonl hf)
        (by
          have := ByteArray.size_extract (a := carry ++ c) (b := tail.toNat) (e := (carry ++ c).size)
          simp only [ByteArray.size_append, concatBytes] at hsz this ⊢; omega),
        bytes_extract_tail tail hsz']

/-- **The chunk boundary is invisible.**  The streaming parse of any
chunking of a byte string that fits in the address space is the line
fold of the whole. -/
theorem parseChunks_eq_parseLines (prelude : PreludeIx) (inModel census : Bool)
    (cs : List ByteArray) (hne : ∀ c ∈ cs, c.isEmpty = false)
    (hsz : (concatBytes cs).size < USize.size) :
    parseChunks prelude inModel census cs =
      (parseLines (.init prelude inModel census) (bytes (concatBytes cs)) 0).map
        ParseResultD.ofState := by
  unfold parseChunks
  rw [parseChunks_go cs _ ByteArray.empty 0 hne
    (by rw [bytes_empty]; exact List.not_mem_nil) (by simpa using hsz), bytes_empty,
    List.nil_append]

/-- The streaming parse of a file's chunks is `parseExportD` of the file. -/
theorem parseChunks_eq_parseExportD (prelude : PreludeIx) (inModel census : Bool)
    (contents : String) (cs : List ByteArray) (hcs : contents.toUTF8 = concatBytes cs)
    (hne : ∀ c ∈ cs, c.isEmpty = false) (hsz : contents.utf8ByteSize < USize.size) :
    parseChunks prelude inModel census cs = parseExportD contents prelude inModel census := by
  have hsz' : (concatBytes cs).size < USize.size := by
    rw [← hcs, String.toUTF8_eq_toByteArray, String.size_toByteArray]; exact hsz
  rw [parseChunks_eq_parseLines prelude inModel census cs hne hsz',
    parseExportD_eq_parseLines contents prelude inModel census hsz, lit, hcs,
    bytes_eq_of_size_lt hsz']

end ConLeche.Frontend
