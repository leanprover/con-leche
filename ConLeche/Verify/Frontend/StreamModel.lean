module

public import ConLeche.Frontend.Stream
public import ConLeche.Verify.Frontend.ModelIO
import ConLeche.Verify.Frontend.Chunks

/-!
# A stream's reads in the IO model (task #424)

The stream parse reads its file through the checker's IO class, by a
fold over the file's positional reads (`foldChunks`, `foldWindows`,
`ConLeche/Frontend/CheckerIO.lean`).  In the model the folds run over
the file's bytes cut as the binary's reads cut them
(`ConLeche/Verify/Frontend/ModelIO.lean`): `readsFrom`, reads
of `csz` bytes, and for the windows `winsOf`, the reads cut at their
last newlines and grouped.  Here: the cuts lose and add no byte.

* `concatBytes_readsFrom`: the reads put together are the file.
* `concatBytes_winsOf`: the windows' chunks, then the bytes after the
  last newline, put together are the reads put together.
* `foldList_serStep`: the serial fold over a list of reads is
  `parseChunks` of them.
* `parseChunks_single_of_concat`: a result of `parseChunks` on chunks
  that put together are `b` is the result on `[b]`, the file as one
  chunk — the form the main corollary (`ConLeche.main_no_False`) needs.
-/

public section

namespace ConLeche.Frontend

open ConLeche

theorem concatBytes_append (l₁ l₂ : List ByteArray) :
    concatBytes (l₁ ++ l₂) = concatBytes l₁ ++ concatBytes l₂ := by
  induction l₁ with
  | nil => simp [concatBytes]
  | cons c l ih => simp [concatBytes, ih, ByteArray.append_assoc]

/-- The reads put together are the file from `off`. -/
theorem concatBytes_readsFrom {csz : Nat} (hc : 0 < csz) (b : ByteArray) (off : Nat) :
    concatBytes (readsFrom csz b off) = b.extract off b.size := by
  fun_induction readsFrom csz b off with
  | case1 off h ih =>
    rw [concatBytes, ih, ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
      Nat.max_eq_right (by omega)]
  | case2 off h =>
    have : b.size ≤ off := by
      refine Nat.le_of_not_lt fun h' => h ⟨hc, h'⟩
    exact (ByteArray.extract_eq_empty_iff.mpr (by omega)).symm

theorem concatBytes_reads {csz : Nat} (hc : 0 < csz) (b : ByteArray) :
    concatBytes (readsFrom csz b 0) = b := by
  rw [concatBytes_readsFrom hc, ByteArray.extract_zero_size]

theorem lastNewlineBelow_lt {b : ByteArray} : ∀ {i k : Nat}, lastNewlineBelow b i = some k → k < i
  | 0, _, h => by simp [lastNewlineBelow] at h
  | i + 1, k, h => by
    simp only [lastNewlineBelow] at h
    split at h
    · cases h; omega
    · have := lastNewlineBelow_lt h; omega

/-- A read cut at its last newline: the chunk and the bytes after it
are the carried bytes and the read. -/
theorem cutRead_some {pending buf0 c p : ByteArray} (h : cutRead pending buf0 = (some c, p)) :
    c ++ p = pending ++ buf0 := by
  unfold cutRead at h
  split at h
  · cases h
  · rename_i k hk
    have hlt := lastNewlineBelow_lt hk
    simp only [Prod.mk.injEq, Option.some.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hb : buf0.extract 0 (k + 1) ++ buf0.extract (k + 1) buf0.size = buf0 := by
      rw [ByteArray.extract_append_extract, Nat.min_eq_left (by omega),
        Nat.max_eq_right (by omega), ByteArray.extract_zero_size]
    split
    · rename_i he
      rw [hb, eq_empty_of_isEmpty he, ByteArray.empty_append]
    · rw [ByteArray.append_assoc, hb]

theorem cutRead_none {pending buf0 p : ByteArray} (h : cutRead pending buf0 = (none, p)) :
    p = pending ++ buf0 := by
  unfold cutRead at h
  split at h
  · cases h; rfl
  · simp at h

/-- The trailing bytes as a list of chunks: none when there are none. -/
@[expose] def tailL (t : ByteArray) : List ByteArray := if t.isEmpty then [] else [t]

theorem concatBytes_tailL (t : ByteArray) : concatBytes (tailL t) = t := by
  unfold tailL
  split
  · rename_i h; rw [eq_empty_of_isEmpty h]; rfl
  · simp [concatBytes, ByteArray.append_empty]

/-- The chunks of a list of windows, in order. -/
@[expose] def winChunks (ws : List (Array ByteArray)) : List ByteArray := ws.flatMap (·.toList)

/-- **The windows lose and add no byte**: their chunks, then the bytes
after the last newline, put together are the chunks so far, the bytes
carried and the reads. -/
theorem concatBytes_winsOf (m : Nat) (rs : List ByteArray) :
    ∀ (acc : Array ByteArray) (pending : ByteArray),
    concatBytes (winChunks (winsOf m acc pending rs).1 ++ tailL (winsOf m acc pending rs).2) =
      concatBytes acc.toList ++ pending ++ concatBytes rs := by
  induction rs with
  | nil =>
    intro acc pending
    simp only [winsOf, concatBytes_append, concatBytes_tailL]
    split
    · rename_i h
      have : acc = #[] := by simpa using h
      subst this; simp [winChunks, concatBytes, ByteArray.append_empty]
    · simp [winChunks, concatBytes, ByteArray.append_empty]
  | cons r rs ih =>
    intro acc pending
    simp only [winsOf]
    split
    · rename_i p hp
      rw [ih, cutRead_none hp, concatBytes]
      simp [ByteArray.append_assoc]
    · rename_i c p hp
      have hcp := cutRead_some hp
      split
      · simp only [winChunks, List.flatMap_cons, List.append_assoc] at ih ⊢
        rw [concatBytes_append, ih]
        simp only [Array.toList_push, concatBytes_append, concatBytes,
          ByteArray.empty_append, ByteArray.append_empty]
        rw [ByteArray.append_assoc, ByteArray.append_assoc, ← ByteArray.append_assoc (a := c), hcp]
        simp [ByteArray.append_assoc]
      · rw [ih]
        simp only [Array.toList_push, concatBytes_append, concatBytes, ByteArray.append_empty]
        rw [ByteArray.append_assoc, ByteArray.append_assoc, ← ByteArray.append_assoc (a := c), hcp]
        simp [ByteArray.append_assoc]

theorem concatBytes_windowsOf {csz : USize} (hc : 0 < csz.toNat) {m : Nat} (hm : 0 < m)
    (b : ByteArray) :
    concatBytes (winChunks (windowsOf csz m b).1 ++ tailL (windowsOf csz m b).2) = b := by
  unfold windowsOf
  rw [ite_eq_right (show ¬ m = 0 by omega), concatBytes_winsOf, concatBytes_reads hc]
  simp [concatBytes]

/-- **The serial fold is `parseChunks`**: over a list of reads, from a
state, the fold of `serStep` is the streaming parse's loop. -/
theorem foldList_serStep (cs : List ByteArray) :
    ∀ (st : StateD) (carry : ByteArray) (lineNo total : Nat),
    foldList serStep serFin (st, carry, lineNo, total) cs =
      parseChunks.go st carry lineNo total cs := by
  induction cs with
  | nil => intro st carry lineNo total; rfl
  | cons c cs ih =>
    intro st carry lineNo total
    simp only [foldList, serStep, parseChunks.go]
    cases chunkStep st carry lineNo total c with
    | error e => rfl
    | ok s => obtain ⟨st', carry', lineNo', total'⟩ := s; exact ih _ _ _ _

/-- **The file as one chunk**: a result of `parseChunks` on chunks that
put together are `b` is its result on `[b]`. -/
theorem parseChunks_single_of_concat {cs : List ByteArray} {b : ByteArray} {r : ParseResultD}
    (hc : concatBytes cs = b) (h : parseChunks cs = .ok r) : parseChunks [b] = .ok r := by
  have hb := parseChunks_ok_parseBytes h
  have hsz := parseChunks_ok_size h
  rw [hc] at hb hsz
  rw [parseChunks_eq_parseBytes [b] (by simpa [concatBytes, ByteArray.append_empty] using hsz)]
  simpa [concatBytes, ByteArray.append_empty] using hb

end ConLeche.Frontend
