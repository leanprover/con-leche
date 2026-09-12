module

public import ConLeche.Frontend.ExportC
import ConLeche.Verify.Frontend.Local

public section

/-!
# The parse is a fold over the lines (task #290)

`parseBytes` reads its input through `feedChunk` — a loop over a
`ByteArray` at `USize` positions, whose reader is `scanLineSpec`, the
naive recogniser lifted to positions — and finishes with
`applyFinalLine`.  This module states what that computes as a
function of the byte LIST alone: `parseLines`, the recogniser applied
line by line with `applyLine` after each, and `parseBytes_eq_parseLines`
says the two agree whenever the input fits in the machine's address
space (`USize` positions are machine words; the hypothesis is what
makes them the list positions) — and `parseBytes`'s size guard makes
every parse that returns a result one that does
(`parseBytes_ok_size`), so no theorem downstream carries the
hypothesis.

`parseLines` is then read through the newline structure of its input:
`parseLines_split` says a parse of `l ++ 10 :: m` reaches `m` as a line
start — after some successful steps on the lines of `l` — and
`parseLines_reach` that a successful parse is a chain of successful
steps (`Reach`), which is how the file theorem carries a state
invariant across the arbitrary parts of the file.
-/

namespace ConLeche.Frontend

/-- The parse of a byte list, line by line: the recogniser on the
input, `applyLine` on its record, the rest again; the last line is the
one without a newline.  Error messages are those of `feedChunk` and
`applyFinalLine`: the line number and, for a syntactic failure, the
byte offset into the line.  Exposed: `ConLeche/Verify/Frontend/Chunks.lean`
unfolds it. -/
@[expose] def parseLines (st : StateD) (l : List UInt8) (lineNo : Nat) :
    Except (CheckError × Nat) StateD :=
  match naiveLine l with
  | .err e rest =>
    .error (.internal (ScanErr.render ⟨l.length - rest.length, e⟩), lineNo + 1)
  | .ok (r, none) _ =>
    match applyLine st r with
    | .error msg => .error (.internal msg, lineNo + 1)
    | .ok (.inr v) => .error (v.toError, lineNo + 1)
    | .ok (.inl st) => .ok st
  | .ok (r, some rest) _ =>
    match applyLine st r with
    | .error msg => .error (.internal msg, lineNo + 1)
    | .ok (.inr v) => .error (v.toError, lineNo + 1)
    | .ok (.inl st) =>
      if _h : rest.length < l.length then parseLines st rest (lineNo + 1)
      else .error (.internal "the line scanner made no progress", lineNo + 1)
termination_by l.length

/-! ## `feedChunk` and `applyFinalLine` compute `parseLines` -/

/-- What `parseBytes` does with a `feedChunk` result. -/
def finishChunk (b : ByteArray) : Except (CheckError × Nat) (StateD × Nat × USize) →
    Except (CheckError × Nat) StateD
  | .error e => .error e
  | .ok (st, lineNo, tail) =>
    if tail < b.usize then applyFinalLine st b tail (lineNo + 1) else .ok st

theorem naiveLine_nil : naiveLine [] = .ok (.blank, none) [] := by rfl

/-- The reader at a position, by the three outcomes of the naive line:
an error at its byte, a final line (position `0`), or a line with the
position of its rest — a position past the start that is a `USize`
and whose tail is that rest. -/
theorem scanLineSpec_cases (b : ByteArray) (i : USize) (hi : i.toNat ≤ (bytes b).length) :
    (∃ t rest, naiveLine (tailAt b i) = .err t rest ∧
      scanLineSpec b i = .err ⟨posAt i.toNat (tailAt b i) rest, t⟩) ∨
    (∃ r rest, naiveLine (tailAt b i) = .ok (r, none) rest ∧ scanLineSpec b i = .ok r 0) ∨
    (∃ r rest, naiveLine (tailAt b i) = .ok (r, some rest) rest ∧
      scanLineSpec b i = .ok r (posAt i.toNat (tailAt b i) rest).toUSize ∧
      rest.length < (tailAt b i).length ∧
      i.toNat < posAt i.toNat (tailAt b i) rest ∧
      (posAt i.toNat (tailAt b i) rest).toUSize.toNat = posAt i.toNat (tailAt b i) rest ∧
      tailAt b (posAt i.toNat (tailAt b i) rest).toUSize = rest) := by
  unfold scanLineSpec
  cases hnv : naiveLine (tailAt b i) with
  | err t rest => exact .inl ⟨t, rest, rfl, rfl⟩
  | ok p rest' =>
    obtain ⟨r, o⟩ := p
    cases o with
    | none => exact .inr (.inl ⟨r, rest', rfl, rfl⟩)
    | some rest =>
      obtain ⟨pre, hpre, _, hrr⟩ := naiveLine_some hnv
      rw [hrr]
      have hsuf : rest <:+ tailAt b i := by
        rw [hpre]; exact (List.suffix_cons _ _).trans (List.suffix_append _ _)
      have hlen := congrArg List.length hpre
      simp only [List.length_append, List.length_cons] at hlen
      refine .inr (.inr ⟨r, rest, rfl, rfl, by omega, by simp only [posAt]; omega,
        toNat_toUSize_posAt hi hsuf, tailAt_posAt hi hsuf⟩)

theorem feedChunk_spec (st : StateD) (b : ByteArray) (i : USize) (lineNo : Nat) :
    finishChunk b (feedChunk st b i lineNo) = parseLines st (tailAt b i) lineNo := by
  fun_induction feedChunk st b i lineNo with
  | case1 st i lineNo h e he hnl =>
    -- a scan error, and there is a newline: the error is reported here
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r, rest, hnv, hs⟩ |
      ⟨r, rest, hnv, hs, _⟩
    · rw [hs] at he; injection he with he; subst he
      rw [parseLines, hnv]
      simp only [finishChunk, posAt, Nat.add_sub_cancel_left]
    · rw [hs] at he; simp at he
    · rw [hs] at he; simp at he
  | case2 st i lineNo h e he hnl =>
    -- a scan error and no newline: the incomplete tail, then the final line fails the same way
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r, rest, hnv, hs⟩ |
      ⟨r, rest, hnv, hs, _⟩
    · rw [parseLines, hnv]
      simp only [finishChunk, h, ↓reduceIte, applyFinalLine, hs, posAt, Nat.add_sub_cancel_left]
    · rw [hs] at he; simp at he
    · rw [hs] at he; simp at he
  | case3 st i lineNo h r j hj hj0 =>
    -- the buffer ended before a newline: the incomplete tail is the final line
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _, hpos, hnat, _⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj1
      rw [parseLines, hnv]
      simp only [finishChunk, h, ↓reduceIte, applyFinalLine, hs]
      rfl
    · exfalso
      rw [hs] at hj; injection hj with hj1 hj2; subst hj2
      have : (posAt i.toNat (tailAt b i) rest).toUSize = 0 := by simpa using hj0
      have := congrArg USize.toNat this
      rw [hnat] at this
      simp at this; omega
  | case4 st i lineNo h r j hj hj0 msg happ =>
    -- the line failed to apply
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2; simp at hj0
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj1
      rw [parseLines, hnv]; simp only [happ, finishChunk]
  | case5 st i lineNo h r j hj hj0 v happ =>
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2; simp at hj0
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj1
      rw [parseLines, hnv]; simp only [happ, finishChunk]
  | case6 st i lineNo h r j hj hj0 st' happ hij ih =>
    -- the line applied and the loop goes on at the newline's successor
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, hlt, _, _, htail⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2; simp at hj0
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj1; subst hj2
      conv => rhs; rw [parseLines, hnv]
      simp only [happ, dif_pos hlt]
      rw [ih, htail]
  | case7 st i lineNo h r j hj hj0 st' happ hij =>
    -- the scanner made no progress: impossible, a `some` position is ahead of the start
    exfalso
    have hi : i.toNat ≤ (bytes b).length := by
      simp only [length_bytes]; exact Nat.le_of_lt (USize.lt_iff_toNat_lt.mp h)
    rcases scanLineSpec_cases b i hi with ⟨t, rest, hnv, hs⟩ | ⟨r', rest, hnv, hs⟩ |
      ⟨r', rest, hnv, hs, _, hpos, hnat, _⟩
    · rw [hs] at hj; simp at hj
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2; simp at hj0
    · rw [hs] at hj; injection hj with hj1 hj2; subst hj2
      exact hij (USize.lt_iff_toNat_lt.mpr (by rw [hnat]; exact hpos))
  | case8 st i lineNo h =>
    -- past the end: nothing to read, and the empty final line is blank
    simp only [finishChunk, h, ↓reduceIte]
    rw [tailAt_of_not_lt h, parseLines, naiveLine_nil]
    rfl

/-- **The size guard**: an input of `USize.size` bytes or more is
refused before any of it is read. -/
theorem parseBytes_size (b : ByteArray) (inModel census : Bool)
    (hsz : USize.size ≤ b.size) : parseBytes b inModel census = .error sizeError := by
  unfold parseBytes
  rw [if_pos hsz]
  rfl

/-- An accepted parse read a buffer the machine word addresses: the
guard is what stands where a size hypothesis would. -/
theorem parseBytes_ok_size {b : ByteArray} {inModel census : Bool} {r : ParseResultD}
    (h : parseBytes b inModel census = .ok r) : b.size < USize.size := by
  rcases Nat.lt_or_ge b.size USize.size with hlt | hge
  · exact hlt
  · rw [parseBytes_size b inModel census hge] at h
    cases h

/-- **The wholesale parse is the line fold**, whenever the input fits
in the address space — which, by the guard, every parse that returns a
result does (`parseBytes_ok_size`). -/
theorem parseBytes_eq_parseLines (b : ByteArray) (inModel census : Bool)
    (hsz : b.size < USize.size) :
    parseBytes b inModel census =
      (parseLines (.init inModel census) (bytes b) 0).map ParseResultD.ofState := by
  have key := feedChunk_spec (.init inModel census) b 0 0
  rw [tailAt_zero_of_size_lt hsz, ← bytes_eq_of_size_lt hsz] at key
  rw [← key]
  unfold parseBytes
  rw [if_neg (Nat.not_le.mpr hsz)]
  simp only [bind, Except.bind, pure, Except.pure]
  cases feedChunk (.init inModel census) b 0 0 with
  | error e => rfl
  | ok p =>
    obtain ⟨st, lineNo, tail⟩ := p
    simp only [finishChunk]
    split
    · cases applyFinalLine st b tail (lineNo + 1) <;> rfl
    · rfl

/-! ## Reading `parseLines` through the newlines -/

/-- A chain of successful line applications. -/
inductive Reach : StateD → StateD → Prop
  | refl (st : StateD) : Reach st st
  | step {st st₁ st₂ : StateD} (r : LineRec) (h : applyLine st r = .ok (.inl st₁))
      (h₂ : Reach st₁ st₂) : Reach st st₂

theorem Reach.trans {st₁ st₂ st₃ : StateD} (h₁ : Reach st₁ st₂) (h₂ : Reach st₂ st₃) :
    Reach st₁ st₃ := by
  induction h₁ with
  | refl => exact h₂
  | step r h _ ih => exact .step r h (ih h₂)

theorem Reach.single {st st₁ : StateD} (r : LineRec) (h : applyLine st r = .ok (.inl st₁)) :
    Reach st st₁ := .step r h (.refl _)

/-- An invariant preserved by every successful step is preserved by a chain. -/
theorem Reach.preserve {P : StateD → Prop}
    (hP : ∀ st r st', applyLine st r = .ok (.inl st') → P st → P st')
    {st st' : StateD} (h : Reach st st') (hst : P st) : P st' := by
  induction h with
  | refl => exact hst
  | step r h _ ih => exact ih (hP _ _ _ h hst)

/-- One line with a newline after it: the parse applies its record and
goes on with the rest. -/
theorem parseLines_line {st : StateD} {l x : List UInt8} {r : LineRec} {n : Nat}
    (hl : naiveLine (l ++ 10 :: x) = .ok (r, some x) x) :
    parseLines st (l ++ 10 :: x) n =
      match applyLine st r with
      | .error msg => .error (.internal msg, n + 1)
      | .ok (.inr v) => .error (v.toError, n + 1)
      | .ok (.inl st) => parseLines st x (n + 1) := by
  rw [parseLines, hl]
  simp only []
  have : x.length < (l ++ 10 :: x).length := by simp; omega
  cases applyLine st r with
  | error msg => rfl
  | ok v => cases v with
    | inr v => rfl
    | inl st => simp only [dif_pos this]

/-- A newline-free line, then the rest: one successful step, or the
parse fails. -/
theorem parseLines_split_nonl {l : List UInt8} (hnl : 10 ∉ l) {st st' : StateD}
    {m : List UInt8} {n : Nat} (h : parseLines st (l ++ 10 :: m) n = .ok st') :
    ∃ st₁, Reach st st₁ ∧ parseLines st₁ m (n + 1) = .ok st' := by
  rcases naiveLine_local l hnl with ⟨r, hr⟩ | ⟨t, r', _, hr⟩
  · rw [parseLines_line (hr m)] at h
    split at h
    · exact absurd h (by simp)
    · exact absurd h (by simp)
    · rename_i st₁ happ
      exact ⟨st₁, .single r happ, h⟩
  · rw [parseLines, hr m] at h
    exact absurd h (by simp)

/-- **A parse reaches every line start.**  A successful parse of
`l ++ 10 :: m` — for ANY `l` — first reaches the state at which `m`
starts, by successful steps, and then parses `m` from there. -/
theorem parseLines_split : ∀ (k : Nat) (l : List UInt8), l.length ≤ k →
    ∀ (st st' : StateD) (m : List UInt8) (n : Nat),
    parseLines st (l ++ 10 :: m) n = .ok st' →
    ∃ st₁ n₁, Reach st st₁ ∧ parseLines st₁ m n₁ = .ok st' := by
  intro k
  induction k with
  | zero =>
    intro l hl st st' m n h
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this
    obtain ⟨st₁, hreach, hp⟩ := parseLines_split_nonl List.not_mem_nil h
    exact ⟨st₁, n + 1, hreach, hp⟩
  | succ k ih =>
    intro l hl st st' m n h
    by_cases hnl : 10 ∈ l
    · obtain ⟨pre, l₂, rfl, hpre⟩ := split_first_nl hnl
      rw [List.append_assoc, List.cons_append] at h
      obtain ⟨st₁, hreach, hp⟩ := parseLines_split_nonl hpre h
      have hlen : l₂.length ≤ k := by
        simp only [List.length_append, List.length_cons] at hl; omega
      obtain ⟨st₂, n₂, hreach₂, hp₂⟩ := ih l₂ hlen st₁ st' m (n + 1) hp
      exact ⟨st₂, n₂, hreach.trans hreach₂, hp₂⟩
    · obtain ⟨st₁, hreach, hp⟩ := parseLines_split_nonl hnl h
      exact ⟨st₁, n + 1, hreach, hp⟩

/-- **A successful parse is a chain of successful steps.** -/
theorem parseLines_reach : ∀ (k : Nat) (l : List UInt8), l.length ≤ k →
    ∀ (st st' : StateD) (n : Nat), parseLines st l n = .ok st' → Reach st st' := by
  intro k
  induction k with
  | zero =>
    intro l hl st st' n h
    have : l = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst this
    rw [parseLines, naiveLine_nil] at h
    simp only at h
    rw [show applyLine st .blank = .ok (.inl st) from rfl] at h
    simp only [Except.ok.injEq] at h
    rw [← h]; exact .refl _
  | succ k ih =>
    intro l hl st st' n h
    by_cases hnl : 10 ∈ l
    · obtain ⟨pre, l₂, rfl, hpre⟩ := split_first_nl hnl
      obtain ⟨st₁, hreach, hp⟩ := parseLines_split_nonl hpre h
      have hlen : l₂.length ≤ k := by
        simp only [List.length_append, List.length_cons] at hl; omega
      exact hreach.trans (ih l₂ hlen st₁ st' (n + 1) hp)
    · rw [parseLines] at h
      split at h
      · exact absurd h (by simp)
      · rename_i r rest hnv
        split at h
        · exact absurd h (by simp)
        · exact absurd h (by simp)
        · rename_i st₁ happ
          simp only [Except.ok.injEq] at h
          rw [← h]; exact .single r happ
      · rename_i r rest rest' hnv
        exact absurd (naiveLine_some hnv) (fun ⟨pre, hpre, _, _⟩ =>
          hnl (hpre ▸ List.mem_append.mpr (.inr (List.mem_cons_self ..))))

end ConLeche.Frontend
