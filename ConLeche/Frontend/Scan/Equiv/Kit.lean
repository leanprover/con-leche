module

public import ConLeche.Frontend.Scan.Naive

/- Exposed: the twins unfold `bytes`, `tailAt`, `posAt` and `liftRes`. -/
@[expose] public section

/-!
# The bridge between the fast recogniser and the naive one (task #261)

The fast recogniser (`ConLeche/Frontend/Scan/Fast.lean`) reads a
`ByteArray` at `USize` positions; the naive one
(`ConLeche/Frontend/Scan/Naive.lean`) reads a `List UInt8` and returns
the unread rest.  This module is the dictionary between the two, and
the shape of every twin lemma:

    fastX b i = liftRes b i (naiveX (tailAt b i))

`bytes b` is the list the fast side can reach (the array cut at
`b.usize`, which is the whole array whenever it fits in memory),
`tailAt b i` its suffix from `i`, and `liftRes` reads a naive result
as a `ScanRes`, turning the rest into a position: the rest of the
input at `i` is short by `posAt` bytes.  `liftRes_shift` is the one
lemma that chains positions: a result a sub-scanner produced at `j`
lifts the same at every `i ≤ j`, so a loop's continuation is the
sub-scanner's rest.  The suffix lemmas (`*_rest_suffix`) are what make
that applicable: a naive scanner only ever returns a suffix of its
input.

Nothing here is executed; the module is imported by the twins and by
the csimp theorem (`ConLeche/Frontend/Scan/Equiv.lean`).
-/

namespace ConLeche.Frontend

/-! ## The bytes a `USize` position reaches -/

/-- The list of the array's bytes, cut at `b.usize` — the whole array
for every array that fits in memory (`bytes_eq_of_size_lt`), and what
a recogniser indexing with machine words sees of one that does not.
`b.data.toList` rather than `b.toList`: the latter is a loop the
kernel cannot unfold on a literal. -/
def bytes (b : ByteArray) : List UInt8 := b.data.toList.take b.usize.toNat

/-- The unread input at position `i`. -/
def tailAt (b : ByteArray) (i : USize) : List UInt8 := (bytes b).drop i.toNat

theorem toNat_usize (b : ByteArray) : b.usize.toNat = b.size % USize.size := by
  simp [ByteArray.usize, Nat.toUSize, USize.size]

theorem toNat_usize_le (b : ByteArray) : b.usize.toNat ≤ b.size := by
  rw [toNat_usize]; exact Nat.mod_le _ _

@[simp] theorem length_bytes (b : ByteArray) : (bytes b).length = b.usize.toNat := by
  simp only [bytes, List.length_take, Array.length_toList]
  exact Nat.min_eq_left (toNat_usize_le b)

theorem bytes_eq_of_size_lt {b : ByteArray} (h : b.size < USize.size) :
    bytes b = b.data.toList := by
  unfold bytes
  rw [toNat_usize, Nat.mod_eq_of_lt h]
  exact List.take_of_length_le (by simp only [Array.length_toList]; exact Nat.le_refl _)

@[simp] theorem length_tailAt (b : ByteArray) (i : USize) :
    (tailAt b i).length = b.usize.toNat - i.toNat := by
  simp [tailAt]

theorem tailAt_of_not_lt {b : ByteArray} {i : USize} (h : ¬ i < b.usize) : tailAt b i = [] := by
  apply List.drop_eq_nil_of_le
  simp only [length_bytes]
  exact Nat.le_of_not_lt (fun h' => h (USize.lt_iff_toNat_lt.mpr h'))

theorem getElem_bytes {b : ByteArray} {k : Nat} (h : k < (bytes b).length) :
    (bytes b)[k] = b.data.toList[k]'(by
      simp only [length_bytes] at h; exact Nat.lt_of_lt_of_le h (toNat_usize_le b)) := by
  simp [bytes]

/-- The step every loop takes: the tail at `i` is the byte at `i`
followed by the tail at `i + 1`. -/
theorem tailAt_of_lt {b : ByteArray} {i : USize} (h : i < b.usize) :
    tailAt b i = b.uget i (usizeInBounds b i h) :: tailAt b (i + 1) := by
  have hi : i.toNat < (bytes b).length := by
    simp only [length_bytes]; exact USize.lt_iff_toNat_lt.mp h
  unfold tailAt
  rw [List.drop_eq_getElem_cons hi, getElem_bytes hi, usizeStep b i h]
  congr 1

theorem byteAt_eq (b : ByteArray) (i : USize) : byteAt b i = (tailAt b i).headD 0 := by
  unfold byteAt
  split
  · next h => rw [tailAt_of_lt h]; rfl
  · next h => rw [tailAt_of_not_lt h]; rfl

theorem toNat_tailAt_lt {b : ByteArray} {i : USize} (h : i < b.usize) :
    i.toNat < (bytes b).length := by
  simp only [length_bytes]; exact USize.lt_iff_toNat_lt.mp h

theorem toNat_lt_size_of_le {b : ByteArray} {n : Nat} (h : n ≤ (bytes b).length) :
    n < USize.size := by
  simp only [length_bytes] at h
  exact Nat.lt_of_le_of_lt h (USize.toNat_lt_size _)

/-! ## Lifting a naive result -/

/-- The position the rest `rest` of the input `l` at `i` stands at. -/
def posAt (i : Nat) (l rest : List UInt8) : Nat := i + (l.length - rest.length)

/-- A naive result read as the fast recogniser's, at `i`. -/
def liftRes (b : ByteArray) (i : USize) : NRes α → ScanRes α
  | .ok v rest => .ok v (posAt i.toNat (tailAt b i) rest).toUSize
  | .err t rest => .err ⟨posAt i.toNat (tailAt b i) rest, t⟩

/-- The position of a rest is a `USize` position: it is at most the
array's `usize` whenever the rest is a suffix of the tail. -/
theorem posAt_le {b : ByteArray} {i : USize} {rest : List UInt8}
    (hi : i.toNat ≤ (bytes b).length) (hr : rest <:+ tailAt b i) :
    posAt i.toNat (tailAt b i) rest ≤ (bytes b).length := by
  have := hr.length_le
  simp only [posAt, length_tailAt, length_bytes] at *
  omega

theorem toNat_toUSize_posAt {b : ByteArray} {i : USize} {rest : List UInt8}
    (hi : i.toNat ≤ (bytes b).length) (hr : rest <:+ tailAt b i) :
    (posAt i.toNat (tailAt b i) rest).toUSize.toNat = posAt i.toNat (tailAt b i) rest := by
  have := posAt_le hi hr
  simp [Nat.toUSize, USize.toNat_ofNat', Nat.mod_eq_of_lt (toNat_lt_size_of_le this)]

/-- The tail at the position of a suffix IS that suffix. -/
theorem tailAt_posAt {b : ByteArray} {i : USize} {rest : List UInt8}
    (hi : i.toNat ≤ (bytes b).length) (hr : rest <:+ tailAt b i) :
    tailAt b (posAt i.toNat (tailAt b i) rest).toUSize = rest := by
  have hl := hr.length_le
  rw [tailAt, toNat_toUSize_posAt hi hr]
  obtain ⟨t, ht⟩ := hr
  have hlen := congrArg List.length ht
  simp only [List.length_append, length_tailAt] at hlen hl
  simp only [posAt, length_tailAt, length_bytes] at hi ⊢
  have : i.toNat + (b.usize.toNat - i.toNat - rest.length) = i.toNat + t.length := by omega
  rw [this, ← List.drop_drop, ← tailAt, ← ht, List.drop_left]

/-- A result a sub-scanner produced at `j` lifts the same at every
`i ≤ j`: positions chain. -/
theorem liftRes_shift {b : ByteArray} {i j : USize} (r : NRes α)
    (hij : i.toNat ≤ j.toNat) (hj : j.toNat ≤ (bytes b).length)
    (hr : r.rest <:+ tailAt b j) :
    liftRes b i r = liftRes b j r := by
  have hl := hr.length_le
  have key : posAt i.toNat (tailAt b i) r.rest = posAt j.toNat (tailAt b j) r.rest := by
    simp only [posAt, length_tailAt, length_bytes] at *
    omega
  cases r with
  | ok v rest => simp only [liftRes, NRes.rest] at *; rw [key]
  | err t rest => simp only [liftRes, NRes.rest] at *; rw [key]

/-- The `.ok` position of a lifted result, as a `Nat`, is `posAt`. -/
theorem liftRes_ok_pos {b : ByteArray} {i : USize} {v : α} {rest : List UInt8}
    (hi : i.toNat ≤ (bytes b).length) (hr : rest <:+ tailAt b i) :
    liftRes b i (.ok v rest) = .ok v (posAt i.toNat (tailAt b i) rest).toUSize ∧
      (posAt i.toNat (tailAt b i) rest).toUSize.toNat = posAt i.toNat (tailAt b i) rest ∧
      tailAt b (posAt i.toNat (tailAt b i) rest).toUSize = rest :=
  ⟨rfl, toNat_toUSize_posAt hi hr, tailAt_posAt hi hr⟩

/-- Progress: a rest shorter than the input sits at a later position. -/
theorem lt_posAt_iff {b : ByteArray} {i : USize} {rest : List UInt8}
    (hi : i.toNat < (bytes b).length) (hr : rest <:+ tailAt b i) :
    i < (posAt i.toNat (tailAt b i) rest).toUSize ↔ rest.length < (tailAt b i).length := by
  have := hr.length_le
  rw [USize.lt_iff_toNat_lt, toNat_toUSize_posAt (Nat.le_of_lt hi) hr]
  simp only [posAt, length_tailAt, length_bytes] at *
  omega

/-! ## Small steps in `USize` -/

/-- Adding a small count to a position, as `Nat` addition. -/
theorem toUSize_toNat_add (i : USize) (n : Nat) (h : i.toNat + n < USize.size) :
    i + n.toUSize = (i.toNat + n).toUSize := by
  apply USize.toNat_inj.mp
  simp only [Nat.toUSize, USize.toNat_add, USize.toNat_ofNat', USize.size] at *
  rw [Nat.add_mod_mod, Nat.mod_eq_of_lt h]

theorem posAt_drop {i : Nat} {l : List UInt8} {m : Nat} (hm : m ≤ l.length) :
    posAt i l (l.drop m) = i + m := by
  simp only [posAt, List.length_drop]; omega

/-- A naive `.ok` that dropped `m` bytes lifts to the position `i + m`. -/
theorem liftRes_ok_drop {b : ByteArray} {i : USize} {v : α} {m : Nat}
    (hm : m ≤ (tailAt b i).length) :
    liftRes b i (.ok v ((tailAt b i).drop m)) = .ok v (i + m.toUSize) := by
  simp only [liftRes, posAt_drop hm]
  rw [toUSize_toNat_add]
  simp only [length_tailAt] at hm
  have := USize.toNat_lt_size i
  have := USize.toNat_lt_size b.usize
  omega

/-- A naive `.err` at the input itself lifts to the position `i`. -/
theorem liftRes_err_self {α : Type} (b : ByteArray) (i : USize) (t : ErrTag) :
    liftRes b i (.err t (tailAt b i) : NRes α) = .err ⟨i.toNat, t⟩ := by
  simp [liftRes, posAt]

/-! ## Literals -/

/-- A literal that fits in a machine word is its own `bytes`. -/
theorem tailAt_zero_of_size_lt {lit : ByteArray} (h : lit.size < USize.size) :
    tailAt lit 0 = lit.data.toList := by
  simp [tailAt, bytes_eq_of_size_lt h]

theorem size_lt_of_lt (s : String) (h : s.toUTF8.size < 2 ^ 32) :
    s.toUTF8.size < USize.size :=
  Nat.lt_of_lt_of_le h USize.le_size

/-- `String.toUTF8` is not exposed to a `module`, but it is `rfl`-equal
to the representation projection `String.toByteArray`, which is; a
literal's bytes are computed by `rw [lit_eq_toByteArray]; rfl` (and
`… ; decide` for a fact about them). -/
theorem lit_eq_toByteArray (s : String) : lit s = s.toByteArray.data.toList := by
  unfold lit; rw [String.toUTF8_eq_toByteArray]

/-- A literal fits in a machine word: `size_toUTF8_lt "true" 4 rfl (by decide)`. -/
theorem size_toUTF8_lt (s : String) (n : Nat) (h : s.toByteArray.size = n)
    (hn : n < 2 ^ 32) : s.toUTF8.size < USize.size := by
  rw [String.toUTF8_eq_toByteArray, h]
  exact Nat.lt_of_lt_of_le hn USize.le_size

/-! ## Suffix lemmas: a naive scanner only returns a suffix of its input -/

theorem NRes.rest_map (f : α → β) (r : NRes α) : (r.map f).rest = r.rest := by
  cases r <;> rfl

theorem dropWhile_suffix' (p : UInt8 → Bool) (l : List UInt8) : l.dropWhile p <:+ l :=
  List.dropWhile_suffix p

theorem naiveNum_rest_suffix {l : List UInt8} {n : Nat} {r : List UInt8}
    (h : naiveNum l = some (n, r)) : r <:+ l := by
  unfold naiveNum at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact List.dropWhile_suffix _

theorem naiveNat_rest_suffix (l : List UInt8) : (naiveNat l).rest <:+ l := by
  unfold naiveNat
  split
  · exact List.suffix_rfl
  · next n r h => exact naiveNum_rest_suffix h

theorem naiveLit_rest_suffix {s : String} {l r : List UInt8} (h : naiveLit s l = some r) :
    r <:+ l := by
  unfold naiveLit at h
  split at h
  · simp only [Option.some.injEq] at h; rw [← h]; exact List.drop_suffix _ _
  · exact absurd h (by simp)

theorem naiveBool_rest_suffix (l : List UInt8) : (naiveBool l).rest <:+ l := by
  unfold naiveBool
  split
  · next r h => exact naiveLit_rest_suffix h
  · split
    · next r h => exact naiveLit_rest_suffix h
    · exact List.suffix_rfl

theorem naiveStrBody_rest_suffix {l body r : List UInt8}
    (h : naiveStrBody l = some (body, r)) : r <:+ l := by
  induction l using naiveStrBody.induct generalizing body r with
  | case1 => simp [naiveStrBody] at h
  | case2 c l' hc =>
    rw [naiveStrBody.eq_def] at h
    simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact List.suffix_cons _ _
  | case3 c hc hb => simp [naiveStrBody, hc, hb] at h
  | case4 c hc hb d l' hd => simp [naiveStrBody, hc, hb, hd] at h
  | case5 c hc hb d l' hd ih =>
    rw [naiveStrBody.eq_def] at h
    simp only [hc, hb, hd, ↓reduceIte, Bool.false_eq_true] at h
    cases hs : naiveStrBody l' with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨body', r'⟩ := p
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact (ih hs).trans ((List.suffix_cons d l').trans (List.suffix_cons c (d :: l')))
  | case6 c l' hc hb hlt =>
    rw [naiveStrBody.eq_def] at h
    simp [hc, hb, hlt] at h
  | case7 c l' hc hb hlt ih =>
    rw [naiveStrBody.eq_def] at h
    simp only [hc, hb, hlt, ↓reduceIte, Bool.false_eq_true] at h
    cases hs : naiveStrBody l' with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨body', r'⟩ := p
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact (ih hs).trans (List.suffix_cons c l')

theorem naiveStr_rest_suffix (l : List UInt8) : (naiveStr l).rest <:+ l := by
  unfold naiveStr
  split
  · next l' =>
    split
    · exact List.suffix_rfl
    · next body rest h =>
      have hr := (naiveStrBody_rest_suffix h).trans (List.suffix_cons (34 : UInt8) l')
      split
      · split <;> first | exact hr | exact List.suffix_rfl
      · split <;> first | exact hr | exact List.suffix_rfl
  · exact List.suffix_rfl

theorem naiveQuotedNat_rest_suffix (l : List UInt8) : (naiveQuotedNat l).rest <:+ l := by
  unfold naiveQuotedNat
  split
  · next l' =>
    split
    · exact List.suffix_rfl
    · next ds rest h1 h2 =>
      show rest <:+ 34 :: l'
      have : 34 :: rest <:+ l' := by rw [← h1]; exact List.dropWhile_suffix _
      exact ((List.suffix_cons 34 rest).trans this).trans (List.suffix_cons 34 l')
    · exact List.suffix_rfl
  · exact List.suffix_rfl

theorem naiveBinderInfo_rest_suffix (l : List UInt8) : (naiveBinderInfo l).rest <:+ l := by
  unfold naiveBinderInfo
  split
  · next l' =>
    have cons : ∀ {r : List UInt8}, r <:+ l' → r <:+ 34 :: l' :=
      fun h => h.trans (List.suffix_cons _ _)
    split
    · next r h => exact cons (naiveLit_rest_suffix h)
    · split
      · next r h => exact cons (naiveLit_rest_suffix h)
      · split
        · next r h => exact cons (naiveLit_rest_suffix h)
        · split
          · next r h => exact cons (naiveLit_rest_suffix h)
          · exact List.suffix_rfl
  · exact List.suffix_rfl

theorem naiveKeyBody_rest_suffix {l k r : List UInt8}
    (h : naiveKeyBody l = some (k, r)) : r <:+ l := by
  induction l using naiveKeyBody.induct generalizing k r with
  | case1 => simp [naiveKeyBody] at h
  | case2 c l' hc =>
    simp only [naiveKeyBody, hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.2]; exact List.suffix_cons _ _
  | case3 c l' hc hb => simp [naiveKeyBody, hc, hb] at h
  | case4 c l' hc hb ih =>
    simp only [naiveKeyBody, hc, hb, ↓reduceIte, Bool.false_eq_true] at h
    cases hs : naiveKeyBody l' with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨k', r'⟩ := p
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.2]
      exact (ih hs).trans (List.suffix_cons c l')

theorem naiveValue_rest_suffix {l r : List UInt8} (h : naiveValue l = some r) : r <:+ l := by
  unfold naiveValue at h
  split at h
  · next r' hr =>
    simp only [Option.some.injEq] at h
    rw [← h]
    have : 58 :: r' <:+ l := by rw [← hr]; exact List.dropWhile_suffix _
    exact (List.dropWhile_suffix _).trans ((List.suffix_cons _ _).trans this)
  · exact absurd h (by simp)

end ConLeche.Frontend
