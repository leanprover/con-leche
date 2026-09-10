module

public import ConLeche.Frontend.Scan.Equiv.Kit
import ConLeche.Frontend.Scan.Equiv.Scalars
import ConLeche.Frontend.Scan.Equiv.Keys

public section

/-!
# The object twins (task #261)

Every object of the dialect is a fast slot loop
(`ConLeche/Frontend/Scan/Fast.lean`) against ONE generic naive loop
with the object's table (`naiveObjLoop`, `ConLeche/Frontend/Scan/Naive.lean`).
Each twin below has the shape

    scanXLoop b i wantMember seen ⟨the slots⟩ =
      liftRes b i (naiveObjLoop xFields required (tailAt b i) wantMember seen ⟨the state⟩)

and its proof is the fast loop's own induction, uniformly: whitespace
and the comma step the tail; the closing brace compares the masks; a
quote is the member step of `Equiv/Keys.lean` (`keyEnd_of_some`,
`keyAt_eq`, `valueAt_eq`), then a case on the key, the slot's scalar
twin, `liftRes_shift` for the error pass-through, and `lt_posAt_iff`
for the progress guard.  The four member lists (`rules`, `recs`,
`types`, `ctors`) are the generic list loop with the object as item.

The proofs are one script, not eighteen: the naive loop's step lemmas
(`objN_*`) read `naiveObjLoop` at a `ByteArray` position under exactly
the fast loop's own branch conditions, the member step's arithmetic is
packaged once (`memberFacts`, `numSlotFacts`, `subSlotFacts`,
`biSlotFacts` and their failure twins), and one tactic macro per case
shape (`o_ws`, `o_brace_ok`, `o_num`, `o_sub`, …) closes the
correspondingly numbered case of `fun_induction`.  A loop with `n`
keys has `12 + 4n` cases: nine before the key dispatch, four per key
(duplicate, the value scanner's failure, the step, the progress
guard), then the unknown key, the byte that starts no member, and the
end of the array.  `objWrap`/`listWrap` are the wrappers' one lemma.
-/

namespace ConLeche.Frontend

/-! ## The naive loop, step by step

Each lemma reads `naiveObjLoop` at `tailAt b i` under one of the fast
loop's branch conditions, stated about the byte the fast loop reads. -/

section ObjNaive
variable {σ : Type} (fields : Key → Option (Slot σ)) (required : UInt32)

theorem objN_end {b : ByteArray} {i : USize} (h : ¬ i < b.usize) (w : Bool) (seen : UInt32)
    (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st = .err .expectedComma (tailAt b i) := by
  rw [tailAt_of_not_lt h, naiveObjLoop.eq_1]

theorem objN_ws {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : isWs (b.uget i (usizeInBounds b i h)) = true) (w : Bool) (seen : UInt32) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st
      = naiveObjLoop fields required (tailAt b (i + 1)) w seen st := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, ↓reduceIte]

theorem objN_brace {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : (b.uget i (usizeInBounds b i h) == 125) = true) (w : Bool) (seen : UInt32) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st
      = (if w && seen != 0 then .err .expectedKey (tailAt b i)
         else if (seen &&& required) != required then .err .missingKey (tailAt b i)
         else .ok st (tailAt b (i + 1))) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem objN_comma {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : (b.uget i (usizeInBounds b i h) == 44) = true) (w : Bool) (seen : UInt32) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st
      = (if w then .err .expectedKey (tailAt b i)
         else naiveObjLoop fields required (tailAt b (i + 1)) true seen st) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, h44, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem objN_other {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (h34 : ¬ (b.uget i (usizeInBounds b i h) == 34) = true) (w : Bool) (seen : UInt32) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st = .err .expectedComma (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, h44, h34, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem objN_notwant {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (h34 : (b.uget i (usizeInBounds b i h) == 34) = true) {w : Bool} (hw : (!w) = true)
    (seen : UInt32) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st = .err .expectedComma (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, h44, h34, hw, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem objN_nokey {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (h34 : (b.uget i (usizeInBounds b i h) == 34) = true) {w : Bool} (hw : ¬ (!w) = true)
    (hkb : naiveKeyBody (tailAt b (i + 1)) = none) (seen : UInt32) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st = .err .expectedKey (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, h44, h34, hw, hkb, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem objN_noval {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (h34 : (b.uget i (usizeInBounds b i h) == 34) = true) {w : Bool} (hw : ¬ (!w) = true)
    {k r1 : List UInt8} (hkb : naiveKeyBody (tailAt b (i + 1)) = some (k, r1))
    (hv : naiveValue r1 = none) (seen : UInt32) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st = .err .expectedColon (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, h44, h34, hw, hkb, hv, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem objN_unknown {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (h34 : (b.uget i (usizeInBounds b i h) == 34) = true) {w : Bool} (hw : ¬ (!w) = true)
    {k r1 lv : List UInt8} (hkb : naiveKeyBody (tailAt b (i + 1)) = some (k, r1))
    (hv : naiveValue r1 = some lv) (hf : fields (keyOf k) = none) (seen : UInt32) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st = .err .unknownKey (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, h44, h34, hw, hkb, hv, hf, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem objN_dup {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (h34 : (b.uget i (usizeInBounds b i h) == 34) = true) {w : Bool} (hw : ¬ (!w) = true)
    {k r1 lv : List UInt8} (hkb : naiveKeyBody (tailAt b (i + 1)) = some (k, r1))
    (hv : naiveValue r1 = some lv) {α : Type} {mask : UInt32} {sc : List UInt8 → NRes α}
    {set : α → σ → σ} (hf : fields (keyOf k) = some (Slot.of mask sc set))
    {seen : UInt32} (hdup : (seen &&& mask != 0) = true) (st : σ) :
    naiveObjLoop fields required (tailAt b i) w seen st = .err .duplicateKey (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, h44, h34, hw, hkb, hv, hf, Slot.of, hdup, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem objN_read_err {α : Type} {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (h34 : (b.uget i (usizeInBounds b i h) == 34) = true) {w : Bool} (hw : ¬ (!w) = true)
    {k r1 lv : List UInt8} (hkb : naiveKeyBody (tailAt b (i + 1)) = some (k, r1))
    (hv : naiveValue r1 = some lv) {mask : UInt32} {sc : List UInt8 → NRes α} {set : α → σ → σ}
    (hf : fields (keyOf k) = some (Slot.of mask sc set))
    {seen : UInt32} (hdup : ¬ (seen &&& mask != 0) = true) {st : σ}
    {t : ErrTag} {r : List UInt8} (hread : sc lv = .err t r) :
    naiveObjLoop fields required (tailAt b i) w seen st = .err t r := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  simp only [hws, h125, h44, h34, hw, hkb, hv, hf, Slot.of, hdup, hread, ↓reduceIte,
    Bool.false_eq_true]

theorem objN_read_ok {α : Type} {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h125 : ¬ (b.uget i (usizeInBounds b i h) == 125) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (h34 : (b.uget i (usizeInBounds b i h) == 34) = true) {w : Bool} (hw : ¬ (!w) = true)
    {k r1 lv : List UInt8} (hkb : naiveKeyBody (tailAt b (i + 1)) = some (k, r1))
    (hv : naiveValue r1 = some lv) {mask : UInt32} {sc : List UInt8 → NRes α} {set : α → σ → σ}
    (hf : fields (keyOf k) = some (Slot.of mask sc set))
    {seen : UInt32} (hdup : ¬ (seen &&& mask != 0) = true) {st : σ}
    {x : α} {rest : List UInt8} (hread : sc lv = .ok x rest)
    (hlt : rest.length < (tailAt b i).length) :
    naiveObjLoop fields required (tailAt b i) w seen st
      = naiveObjLoop fields required rest false (seen ||| mask) (set x st) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveObjLoop.eq_2]
  have hlt' : rest.length < (b.uget i (usizeInBounds b i h) :: tailAt b (i + 1)).length := by
    rw [← tailAt_of_lt h]; exact hlt
  simp only [hws, h125, h44, h34, hw, hkb, hv, hf, Slot.of, hdup, hread, hlt', ↓reduceIte,
    Bool.false_eq_true, ↓reduceDIte]

end ObjNaive


/-! ## Lifting a mapped result -/

theorem liftRes_map_err {α β : Type} {b : ByteArray} {i : USize} (f : α → β) (t : ErrTag)
    (r : List UInt8) :
    liftRes b i ((NRes.err t r : NRes α).map f) = liftRes b i (NRes.err t r) := rfl

theorem liftRes_err_pos {α : Type} (b : ByteArray) (i : USize) (t : ErrTag) (r : List UInt8) :
    liftRes b i (NRes.err t r : NRes α) = .err ⟨posAt i.toNat (tailAt b i) r, t⟩ := rfl

theorem liftRes_map_err_self {α β : Type} {b : ByteArray} {i : USize} (f : α → β) (t : ErrTag) :
    liftRes b i ((NRes.err t (tailAt b i) : NRes α).map f) = .err ⟨i.toNat, t⟩ :=
  liftRes_err_self b i t

theorem liftRes_map_ok_step {α β : Type} {b : ByteArray} {i : USize} (f : α → β) (v : α)
    (h : i < b.usize) :
    liftRes b i ((NRes.ok v (tailAt b (i + 1)) : NRes α).map f) = .ok (f v) (i + 1) :=
  liftRes_ok_step h

/-! ## The member step's facts -/

/-- The two guards of the fast member step give the naive key, its
value's input, and where that input sits. -/
theorem memberFacts {b : ByteArray} {i ke v : USize} (h : i < b.usize)
    (hke0 : ke = keyEnd b (i + 1)) (hv0 : v = valueAt b i ke)
    (hke : ¬ (ke == 0) = true) (hvi : ¬ (v == i) = true) :
    ∃ k r1 lv, naiveKeyBody (tailAt b (i + 1)) = some (k, r1) ∧
      naiveValue r1 = some lv ∧
      keyAt b i (ke - (i + 1)) = keyOf k ∧
      tailAt b v = lv ∧
      v.toNat = posAt i.toNat (tailAt b i) lv ∧
      i.toNat < v.toNat ∧
      lv <:+ tailAt b i ∧ lv.length < (tailAt b i).length := by
  subst hke0; subst hv0
  have hi : i.toNat < (bytes b).length := toNat_tailAt_lt h
  have hke' : keyEnd b (i + 1) ≠ 0 := by simpa using hke
  obtain ⟨k, r1, hkb⟩ : ∃ k r1, naiveKeyBody (tailAt b (i + 1)) = some (k, r1) := by
    cases hx : naiveKeyBody (tailAt b (i + 1)) with
    | none => exact absurd ((keyEnd_eq_zero_iff h).mpr hx) hke'
    | some p => obtain ⟨k, r1⟩ := p; exact ⟨k, r1, rfl⟩
  have hva := valueAt_eq h hkb
  cases hv : naiveValue r1 with
  | none =>
    rw [hv] at hva
    exact absurd (by simp [hva] : (valueAt b i (keyEnd b (i + 1)) == i) = true) hvi
  | some lv =>
    rw [hv] at hva
    obtain ⟨hsuf, hlt⟩ := naiveValue_of_key h hkb hv
    have hvn : (valueAt b i (keyEnd b (i + 1))).toNat = posAt i.toNat (tailAt b i) lv := by
      rw [hva]; exact toNat_toUSize_posAt (Nat.le_of_lt hi) hsuf
    refine ⟨k, r1, lv, hkb, hv, keyAt_eq h hkb, ?_, hvn, ?_, hsuf, hlt⟩
    · rw [hva]; exact tailAt_posAt (Nat.le_of_lt hi) hsuf
    · rw [hvn]; simp only [posAt, length_tailAt, length_bytes] at *; omega

/-- The colon guard: the value position stayed at `i` exactly when the
key is not followed by one. -/
theorem colonFacts {b : ByteArray} {i ke v : USize} (h : i < b.usize)
    (hke0 : ke = keyEnd b (i + 1)) (hv0 : v = valueAt b i ke)
    (hke : ¬ (ke == 0) = true) (hvi : (v == i) = true) :
    ∃ k r1, naiveKeyBody (tailAt b (i + 1)) = some (k, r1) ∧ naiveValue r1 = none := by
  subst hke0; subst hv0
  have hi : i.toNat < (bytes b).length := toNat_tailAt_lt h
  have hke' : keyEnd b (i + 1) ≠ 0 := by simpa using hke
  obtain ⟨k, r1, hkb⟩ : ∃ k r1, naiveKeyBody (tailAt b (i + 1)) = some (k, r1) := by
    cases hx : naiveKeyBody (tailAt b (i + 1)) with
    | none => exact absurd ((keyEnd_eq_zero_iff h).mpr hx) hke'
    | some p => obtain ⟨k, r1⟩ := p; exact ⟨k, r1, rfl⟩
  refine ⟨k, r1, hkb, ?_⟩
  have hva := valueAt_eq h hkb
  cases hv : naiveValue r1 with
  | none => rfl
  | some lv =>
    exfalso
    rw [hv] at hva
    obtain ⟨hsuf, hlt⟩ := naiveValue_of_key h hkb hv
    have hvn : (valueAt b i (keyEnd b (i + 1))).toNat = posAt i.toNat (tailAt b i) lv := by
      rw [hva]; exact toNat_toUSize_posAt (Nat.le_of_lt hi) hsuf
    have heq : valueAt b i (keyEnd b (i + 1)) = i := by simpa using hvi
    rw [heq] at hvn
    simp only [posAt, length_tailAt] at hvn hlt
    omega

/-- The value's input, once located, is inside the array. -/
theorem valueFacts {b : ByteArray} {i v : USize} {lv : List UInt8}
    (h : i < b.usize) (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hsuf : lv <:+ tailAt b i) :
    v.toNat ≤ b.usize.toNat := by
  have hi : i.toNat < (bytes b).length := toNat_tailAt_lt h
  have := posAt_le (Nat.le_of_lt hi) hsuf
  simp only [length_bytes] at this
  omega

/-- Where a scanner that stopped at `e` inside the value leaves the loop. -/
theorem restFacts {b : ByteArray} {i v e : USize} {lv r : List UInt8}
    (h : i < b.usize) (htv : tailAt b v = lv)
    (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hiv : i.toNat < v.toNat) (hsuf : lv <:+ tailAt b i)
    (hlt : lv.length < (tailAt b i).length) (hrs : r <:+ lv)
    (he : e.toNat = posAt v.toNat (tailAt b v) r) (hte : tailAt b e = r) :
    i.toNat ≤ e.toNat ∧ e.toNat ≤ b.usize.toNat ∧
      (tailAt b e).length < (tailAt b i).length ∧ i < e := by
  have hvb : v.toNat ≤ b.usize.toNat := valueFacts h hvn hsuf
  have hvl : v.toNat ≤ (bytes b).length := by simp only [length_bytes]; exact hvb
  have hrt : r <:+ tailAt b v := by rw [htv]; exact hrs
  have hle : posAt v.toNat (tailAt b v) r ≤ (bytes b).length := posAt_le hvl hrt
  have hrl : r.length ≤ lv.length := by rw [← htv]; exact hrt.length_le
  simp only [length_bytes] at hle
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [he]; simp only [posAt]; omega
  · rw [he]; exact hle
  · rw [hte]; omega
  · rw [USize.lt_iff_toNat_lt, he]; simp only [posAt]; omega

/-- A number slot: `numEnd` says the digit run is there, and where it ends. -/
theorem numSlotFacts {b : ByteArray} {i v e : USize} {lv : List UInt8}
    (h : i < b.usize) (htv : tailAt b v = lv)
    (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hiv : i.toNat < v.toNat) (hsuf : lv <:+ tailAt b i)
    (hlt : lv.length < (tailAt b i).length)
    (he0 : e = numEnd b v) (he : ¬ (e == v) = true) :
    naiveNat lv = .ok (readNatAt b v e) (tailAt b e) ∧
      i.toNat ≤ e.toNat ∧ e.toNat ≤ b.usize.toNat ∧
      (tailAt b e).length < (tailAt b i).length ∧ i < e := by
  subst he0
  have hvb : v.toNat ≤ b.usize.toNat := valueFacts h hvn hsuf
  have hvl : v.toNat ≤ (bytes b).length := by simp only [length_bytes]; exact hvb
  have he' : ¬ numEnd b v = v := by simpa using he
  obtain ⟨n, r, hnum⟩ : ∃ n r, naiveNum (tailAt b v) = some (n, r) := by
    cases hx : naiveNum (tailAt b v) with
    | none => exact absurd ((numEnd_eq_self_iff b v).mpr hx) he'
    | some p => obtain ⟨n, r⟩ := p; exact ⟨n, r, rfl⟩
  obtain ⟨hpos, hval⟩ := numEnd_of_some hnum
  have hrs : r <:+ tailAt b v := naiveNum_rest_suffix hnum
  have hen : (numEnd b v).toNat = posAt v.toNat (tailAt b v) r := by
    rw [hpos]; exact toNat_toUSize_posAt hvl hrs
  have hten : tailAt b (numEnd b v) = r := by rw [hpos]; exact tailAt_posAt hvl hrs
  obtain ⟨h1, h2, h3, h4⟩ :=
    restFacts h htv hvn hiv hsuf hlt (by rw [← htv]; exact hrs) hen hten
  refine ⟨?_, h1, h2, h3, h4⟩
  rw [hten, hval, ← htv]
  exact naiveNat_of_some hnum

theorem numSlotNone {b : ByteArray} {v e : USize} {lv : List UInt8} (htv : tailAt b v = lv)
    (he0 : e = numEnd b v) (he : (e == v) = true) : naiveNat lv = .err .expectedNat lv := by
  subst he0
  have he' : numEnd b v = v := by simpa using he
  rw [← htv]; exact naiveNat_of_none ((numEnd_eq_self_iff b v).mp he')

/-- A sub-scanner slot that succeeded: where its rest sits. -/
theorem subSlotFacts {α : Type} {b : ByteArray} {i v e : USize} {x : α} {res : NRes α}
    {lv : List UInt8} (h : i < b.usize) (htv : tailAt b v = lv)
    (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hiv : i.toNat < v.toNat) (hsuf : lv <:+ tailAt b i)
    (hlt : lv.length < (tailAt b i).length) (hrs : res.rest <:+ lv)
    (hres : liftRes b v res = .ok x e) :
    res = .ok x (tailAt b e) ∧ i.toNat ≤ e.toNat ∧ e.toNat ≤ b.usize.toNat ∧
      (tailAt b e).length < (tailAt b i).length ∧ i < e := by
  have hvb : v.toNat ≤ b.usize.toNat := valueFacts h hvn hsuf
  have hvl : v.toNat ≤ (bytes b).length := by simp only [length_bytes]; exact hvb
  cases hr : res with
  | err t r => rw [hr] at hres; simp only [liftRes] at hres; exact absurd hres (by simp)
  | ok x' r =>
    rw [hr] at hres hrs
    simp only [NRes.rest] at hrs
    simp only [liftRes, ScanRes.ok.injEq] at hres
    obtain ⟨hx, he⟩ := hres
    subst hx
    have hrt : r <:+ tailAt b v := by rw [htv]; exact hrs
    have hen : e.toNat = posAt v.toNat (tailAt b v) r := by
      rw [← he]; exact toNat_toUSize_posAt hvl hrt
    have hten : tailAt b e = r := by rw [← he]; exact tailAt_posAt hvl hrt
    obtain ⟨h1, h2, h3, h4⟩ := restFacts h htv hvn hiv hsuf hlt hrs hen hten
    exact ⟨by rw [hten], h1, h2, h3, h4⟩

/-- A sub-scanner slot that failed: the naive error, lifted at `i`. -/
theorem subSlotErr {α : Type} {b : ByteArray} {i v : USize} {err : ScanErr} {res : NRes α}
    {lv : List UInt8} (h : i < b.usize) (htv : tailAt b v = lv)
    (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hsuf : lv <:+ tailAt b i) (hrs : res.rest <:+ lv)
    (hres : liftRes b v res = .err err) :
    ∃ t r, res = .err t r ∧ err = ⟨posAt i.toNat (tailAt b i) r, t⟩ := by
  have hvb : v.toNat ≤ b.usize.toNat := valueFacts h hvn hsuf
  cases hr : res with
  | ok x r => rw [hr] at hres; simp only [liftRes] at hres; exact absurd hres (by simp)
  | err t r =>
    rw [hr] at hres hrs
    simp only [NRes.rest] at hrs
    refine ⟨t, r, rfl, ?_⟩
    have hshift : liftRes b i (NRes.err t r : NRes α) = liftRes b v (NRes.err t r) :=
      liftRes_shift (NRes.err t r) (by rw [hvn]; simp only [posAt]; omega)
        (by simp only [length_bytes]; exact hvb)
        (by simp only [NRes.rest]; rw [htv]; exact hrs)
    have hthis := hshift.trans hres
    rw [liftRes_err_pos] at hthis
    simpa using hthis.symm

/-- The `binderInfo` slot: its fast scanner returns `0` exactly on the
naive error. -/
theorem biSlotFacts {b : ByteArray} {i v e : USize} {lv : List UInt8}
    (h : i < b.usize) (htv : tailAt b v = lv)
    (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hiv : i.toNat < v.toNat) (hsuf : lv <:+ tailAt b i)
    (hlt : lv.length < (tailAt b i).length)
    (he0 : e = scanBinderInfo b v) (he : ¬ (e == 0) = true) :
    naiveBinderInfo lv = .ok () (tailAt b e) ∧
      i.toNat ≤ e.toNat ∧ e.toNat ≤ b.usize.toNat ∧
      (tailAt b e).length < (tailAt b i).length ∧ i < e := by
  subst he0
  have hvb : v.toNat ≤ b.usize.toNat := valueFacts h hvn hsuf
  have hvl : v.toNat ≤ (bytes b).length := by simp only [length_bytes]; exact hvb
  have hbi := scanBinderInfo_eq b v
  have he' : ¬ scanBinderInfo b v = 0 := by simpa using he
  cases hn : naiveBinderInfo (tailAt b v) with
  | err t r => rw [hn] at hbi; exact absurd hbi he'
  | ok u r =>
    rw [hn] at hbi
    have hrs : r <:+ tailAt b v := by
      have := naiveBinderInfo_rest_suffix (tailAt b v); rw [hn] at this; exact this
    have hen : (scanBinderInfo b v).toNat = posAt v.toNat (tailAt b v) r := by
      rw [hbi]; exact toNat_toUSize_posAt hvl hrs
    have hten : tailAt b (scanBinderInfo b v) = r := by
      rw [hbi]; exact tailAt_posAt hvl hrs
    obtain ⟨h1, h2, h3, h4⟩ :=
      restFacts h htv hvn hiv hsuf hlt (by rw [← htv]; exact hrs) hen hten
    refine ⟨?_, h1, h2, h3, h4⟩
    rw [hten, ← htv, hn]

theorem biSlotNone {b : ByteArray} {i v e : USize} {lv : List UInt8}
    (h : i < b.usize) (htv : tailAt b v = lv)
    (hvn : v.toNat = posAt i.toNat (tailAt b i) lv)
    (hiv : i.toNat < v.toNat) (hsuf : lv <:+ tailAt b i)
    (he0 : e = scanBinderInfo b v) (he : (e == 0) = true) :
    naiveBinderInfo lv = .err .badBinderInfo lv := by
  subst he0
  have hvb : v.toNat ≤ b.usize.toNat := valueFacts h hvn hsuf
  have hvl : v.toNat ≤ (bytes b).length := by simp only [length_bytes]; exact hvb
  have hbi := scanBinderInfo_eq b v
  have he' : scanBinderInfo b v = 0 := by simpa using he
  cases hn : naiveBinderInfo (tailAt b v) with
  | err t r =>
    have hb : naiveBinderInfo (tailAt b v) = .err .badBinderInfo (tailAt b v) := by
      unfold naiveBinderInfo at hn ⊢
      split at hn
      · split at hn
        · exact absurd hn (by simp)
        · split at hn
          · exact absurd hn (by simp)
          · split at hn
            · exact absurd hn (by simp)
            · split at hn
              · exact absurd hn (by simp)
              · rfl
      · rfl
    rw [← htv]; exact hb
  | ok u r =>
    rw [hn] at hbi
    have hrs : r <:+ tailAt b v := by
      have := naiveBinderInfo_rest_suffix (tailAt b v); rw [hn] at this; exact this
    have hen : (scanBinderInfo b v).toNat = posAt v.toNat (tailAt b v) r := by
      rw [hbi]; exact toNat_toUSize_posAt hvl hrs
    rw [he'] at hen
    simp only [posAt, USize.toNat_ofNat, Nat.zero_mod] at hen
    omega

/-! ## The uniform case script -/

/-- The rest of a sub-scanner's naive twin is a suffix of its input. -/
syntax "sub_suffix" : tactic
macro_rules
  | `(tactic| sub_suffix) => `(tactic|
      first
      | exact naiveNat_rest_suffix _
      | exact naiveBool_rest_suffix _
      | exact naiveBinderInfo_rest_suffix _
      | exact naiveStr_rest_suffix _
      | exact naiveNatList_rest_suffix _
      | exact naivePw_rest_suffix _
      | exact naiveHints_rest_suffix _)

/-- A slot's `read` returns a suffix of the value's input, because its
scanner does. -/
macro "slot_rest" : tactic => `(tactic|
  (first | rw [Slot.of_read_rest] | (simp only [Slot.drop]; rw [Slot.of_read_rest])
   sub_suffix))

/-- The twin of the sub-scanner a slot ran, rewritten into the case's
hypothesis. -/
syntax "sub_twin" ident ident : tactic
macro_rules
  | `(tactic| sub_twin $hs:ident $ht:ident) => `(tactic|
      first
      | rw [scanBool_eq, $ht:ident] at $hs:ident
      | rw [scanString_eq, $ht:ident] at $hs:ident
      | rw [scanNatList_eq, $ht:ident] at $hs:ident
      | rw [scanPw_eq, $ht:ident] at $hs:ident
      | rw [scanHints_eq, $ht:ident] at $hs:ident)

/-! ### One macro per case shape

`fun_induction` on a slot loop with `n` keys yields, in order: the
whitespace step, the three arms of the closing brace, the two of the
comma, the quote where a comma was due, the two key guards, then four
cases per key (duplicate, the value scanner's failure, the step, the
progress guard), then the unknown key, the byte that starts no member,
and the end of the array. -/

/-- The naive loop's rest is a suffix of the tail. -/
macro "obj_rest" fs:ident : tactic => `(tactic|
  (rw [NRes.rest_map]; exact naiveObjLoop_rest_suffix _ _ $fs:ident _ _ _ _))

macro "o_end" : tactic => `(tactic|
  (rename_i h
   rw [objN_end _ _ h, liftRes_map_err_self]))

macro "o_ws" fs:ident : tactic => `(tactic|
  (rename_i h c hws ih
   rw [objN_ws _ _ h hws, ih]
   exact (liftRes_step _ h (by obj_rest $fs:ident)).symm))

macro "o_brace_key" : tactic => `(tactic|
  (rename_i h c hws h125 hmask
   rw [objN_brace _ _ h hws h125]
   simp only [hmask, ↓reduceIte]
   rw [liftRes_map_err_self]))

macro "o_brace_req" : tactic => `(tactic|
  (rename_i h c hws h125 hmask hreq
   rw [objN_brace _ _ h hws h125]
   simp only [hmask, hreq, ↓reduceIte, Bool.false_eq_true]
   rw [liftRes_map_err_self]))

macro "o_brace_ok" : tactic => `(tactic|
  (rename_i h c hws h125 hmask hreq
   rw [objN_brace _ _ h hws h125]
   simp only [hmask, hreq, ↓reduceIte, Bool.false_eq_true]
   rw [liftRes_map_ok_step _ _ h]
   try rfl))

macro "o_comma_key" : tactic => `(tactic|
  (rename_i h c hws h125 h44
   rw [objN_comma _ _ h hws h125 h44]
   simp only [↓reduceIte]
   rw [liftRes_map_err_self]))

macro "o_comma" fs:ident : tactic => `(tactic|
  (rename_i h c hws h125 h44 hw ih
   rw [objN_comma _ _ h hws h125 h44]
   simp only [hw, ↓reduceIte, Bool.false_eq_true]
   rw [ih]
   exact (liftRes_step _ h (by obj_rest $fs:ident)).symm))

macro "o_other" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34
   rw [objN_other _ _ h hws h125 h44 h34, liftRes_map_err_self]))

macro "o_notwant" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw
   rw [objN_notwant _ _ h hws h125 h44 h34 hw, liftRes_map_err_self]))

macro "o_nokey" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke hke
   rw [objN_nokey _ _ h hws h125 h44 h34 hw
     ((keyEnd_eq_zero_iff h).mp (by simpa using hke)), liftRes_map_err_self]))

macro "o_nocolon" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi
   obtain ⟨k, r1, hkb, hv⟩ := colonFacts h rfl rfl hke hvi
   rw [objN_noval _ _ h hws h125 h44 h34 hw hkb hv, liftRes_map_err_self]))

/-- The unknown-key case: one `_` per key of the object, for the
`keyAt … ≠ .kX` hypotheses the fast dispatch left. -/
syntax "o_unknown" ident (ppSpace colGt ident)* : tactic
macro_rules
  | `(tactic| o_unknown $tbl:ident $[$xs:ident]*) => `(tactic|
      (rename_i h c hws h125 h44 h34 hw ke v hke hvi $[$xs:ident]*
       obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
         memberFacts h rfl rfl hke hvi
       have hf : $tbl:ident (keyOf k) = none := by
         cases hx : keyOf k <;> first | rfl | exact absurd (hka.trans hx) ‹_›
       rw [objN_unknown _ _ h hws h125 h44 h34 hw hkb hv hf, liftRes_map_err_self]))

macro "o_dup" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   rw [objN_dup _ _ h hws h125 h44 h34 hw hkb hv (by rw [hkey']; rfl) hdup,
     liftRes_map_err_self]))

macro "o_num_none" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup e he
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   rw [objN_read_err _ _ h hws h125 h44 h34 hw hkb hv (by rw [hkey']; rfl) hdup
     (numSlotNone htv rfl he), liftRes_map_err]
   simp only [liftRes]
   exact congrArg (fun n => ScanRes.err ⟨n, ErrTag.expectedNat⟩) hvn))

macro "o_num" fs:ident : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup e he hj ih
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   obtain ⟨hread, hile, heb, hrlt, hie⟩ := numSlotFacts h htv hvn hiv hlvs hlvlt rfl he
   rw [objN_read_ok _ _ h hws h125 h44 h34 hw hkb hv (by rw [hkey']; rfl) hdup hread hrlt, ih]
   exact (liftRes_jump _ hile heb (by obj_rest $fs:ident)).symm))

macro "o_num_stuck" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup e he hj
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   exact absurd (numSlotFacts h htv hvn hiv hlvs hlvlt rfl he).2.2.2.2 hj))

macro "o_bi_none" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup e he
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   rw [objN_read_err _ _ h hws h125 h44 h34 hw hkb hv (by rw [hkey']; rfl) hdup
     (biSlotNone h htv hvn hiv hlvs rfl he), liftRes_map_err]
   simp only [liftRes]
   exact congrArg (fun n => ScanRes.err ⟨n, ErrTag.badBinderInfo⟩) hvn))

macro "o_bi" fs:ident : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup e he hj ih
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   obtain ⟨hread, hile, heb, hrlt, hie⟩ := biSlotFacts h htv hvn hiv hlvs hlvlt rfl he
   rw [objN_read_ok _ _ h hws h125 h44 h34 hw hkb hv (by rw [hkey']; rfl) hdup hread hrlt, ih]
   exact (liftRes_jump _ hile heb (by obj_rest $fs:ident)).symm))

macro "o_bi_stuck" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup e he hj
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   exact absurd (biSlotFacts h htv hvn hiv hlvs hlvlt rfl he).2.2.2.2 hj))

macro "o_sub_err" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup err hsc
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   sub_twin hsc htv
   obtain ⟨t, r, hr, hlift⟩ := subSlotErr h htv hvn hlvs (by sub_suffix) hsc
   rw [objN_read_err _ _ h hws h125 h44 h34 hw hkb hv (by rw [hkey']; rfl) hdup hr,
     liftRes_map_err, liftRes_err_pos, hlift]))

macro "o_sub" fs:ident : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup x e hsc hj ih
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   have hkey' := hka.symm.trans hkey
   sub_twin hsc htv
   obtain ⟨hread, hile, heb, hrlt, hie⟩ :=
     subSlotFacts h htv hvn hiv hlvs hlvlt (by sub_suffix) hsc
   rw [objN_read_ok _ _ h hws h125 h44 h34 hw hkb hv (by rw [hkey']; rfl) hdup hread hrlt, ih]
   exact (liftRes_jump _ hile heb (by obj_rest $fs:ident)).symm))

macro "o_sub_stuck" : tactic => `(tactic|
  (rename_i h c hws h125 h44 h34 hw ke v hke hvi hkey hdup x e hsc hj
   obtain ⟨k, r1, lv, hkb, hv, hka, htv, hvn, hiv, hlvs, hlvlt⟩ :=
     memberFacts h rfl rfl hke hvi
   sub_twin hsc htv
   exact absurd (subSlotFacts h htv hvn hiv hlvs hlvlt (by sub_suffix) hsc).2.2.2.2 hj))

/-- The nine cases every slot loop opens with. -/
macro "obj_head" fs:ident : tactic => `(tactic|
  (case case1 => o_ws $fs:ident
   case case2 => o_brace_key
   case case3 => o_brace_req
   case case4 => o_brace_ok
   case case5 => o_comma_key
   case case6 => o_comma $fs:ident
   case case7 => o_notwant
   case case8 => o_nokey
   case case9 => o_nocolon))

/-- The four cases of a number slot. -/
macro "obj_num" fs:ident n1:ident n2:ident n3:ident n4:ident : tactic => `(tactic|
  (case $n1:ident => o_dup
   case $n2:ident => o_num_none
   case $n3:ident => o_num $fs:ident
   case $n4:ident => o_num_stuck))

/-- The four cases of a `binderInfo` slot. -/
macro "obj_bi" fs:ident n1:ident n2:ident n3:ident n4:ident : tactic => `(tactic|
  (case $n1:ident => o_dup
   case $n2:ident => o_bi_none
   case $n3:ident => o_bi $fs:ident
   case $n4:ident => o_bi_stuck))

/-- The four cases of a sub-scanner slot. -/
macro "obj_sub" fs:ident n1:ident n2:ident n3:ident n4:ident : tactic => `(tactic|
  (case $n1:ident => o_dup
   case $n2:ident => o_sub_err
   case $n3:ident => o_sub $fs:ident
   case $n4:ident => o_sub_stuck))

/-! ## The object wrapper -/

theorem naiveObject_cons_123 {σ α : Type} (fields : Key → Option (Slot σ)) (required : UInt32)
    (init : σ) (finish : σ → α) (l' : List UInt8) :
    naiveObject fields required init finish (123 :: l')
      = (naiveObjLoop fields required l' true 0 init).map finish := rfl

theorem naiveObject_of_ne {σ α : Type} (fields : Key → Option (Slot σ)) (required : UInt32)
    (init : σ) (finish : σ → α) {l : List UInt8} (h : ¬ l.headD 0 = 123) :
    naiveObject fields required init finish l = .err .expectedObject l := by
  unfold naiveObject
  split
  · next l' => exact absurd rfl h
  · rfl

/-! ## Wrappers -/

theorem objWrap {σ α : Type} {fields : Key → Option (Slot σ)} {required : UInt32}
    {init : σ} {finish : σ → α}
    (hf : ∀ k slot, fields k = some slot → ∀ l st, (slot.read l st).rest <:+ l)
    {b : ByteArray} {i : USize} {res : ScanRes α}
    (hloop : res = liftRes b (i + 1)
      ((naiveObjLoop fields required (tailAt b (i + 1)) true 0 init).map finish)) :
    (if byteAt b i == 123 then res else ScanRes.err ⟨i.toNat, .expectedObject⟩)
      = liftRes b i (naiveObject fields required init finish (tailAt b i)) := by
  by_cases hb : byteAt b i = 123
  · have hlt : i < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hb]; decide)
    have h1 := tailAt_of_lt hlt
    have h2 : b.uget i (usizeInBounds b i hlt) = 123 := by
      rw [← hb, byteAt_eq, h1]; rfl
    have hT : tailAt b i = 123 :: tailAt b (i + 1) := by rw [h1, h2]
    rw [if_pos (by simp [hb]), hloop, hT, naiveObject_cons_123]
    exact (liftRes_step _ hlt (by
      rw [NRes.rest_map]; exact naiveObjLoop_rest_suffix _ _ hf _ _ _ _)).symm
  · have hhd : ¬ (tailAt b i).headD 0 = 123 := by rw [← byteAt_eq]; exact hb
    rw [if_neg (by simpa using hb), naiveObject_of_ne _ _ _ _ hhd, liftRes_err_self]

theorem listWrap {α : Type} {start : UInt8 → Bool} {item : List UInt8 → NRes α}
    (hitem : ∀ l, (item l).rest <:+ l)
    {b : ByteArray} {i : USize} {res : ScanRes (List α)}
    (hloop : res = liftRes b (i + 1) (naiveListLoop start item (tailAt b (i + 1)) [] true)) :
    (if byteAt b i == 91 then res else ScanRes.err ⟨i.toNat, .expectedList⟩)
      = liftRes b i (naiveList start item (tailAt b i)) := by
  by_cases hb : byteAt b i = 91
  · have hlt : i < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hb]; decide)
    have h1 := tailAt_of_lt hlt
    have h2 : b.uget i (usizeInBounds b i hlt) = 91 := by
      rw [← hb, byteAt_eq, h1]; rfl
    have hT : tailAt b i = 91 :: tailAt b (i + 1) := by rw [h1, h2]
    rw [if_pos (by simp [hb]), hloop, hT, naiveList_cons_91]
    exact (liftRes_step _ hlt (naiveListLoop_rest_suffix _ _ hitem _ _ _)).symm
  · have hhd : ¬ (tailAt b i).headD 0 = 91 := by rw [← byteAt_eq]; exact hb
    rw [if_neg (by simpa using hb), naiveList_of_ne _ _ hhd, liftRes_err_self]

/-! ## The generic list loop, with an object as item -/

section ListNaive
variable {α : Type} (start : UInt8 → Bool) (item : List UInt8 → NRes α)

theorem lstN_end {b : ByteArray} {i : USize} (h : ¬ i < b.usize) (acc : List α) (w : Bool) :
    naiveListLoop start item (tailAt b i) acc w = .err .expectedList (tailAt b i) := by
  rw [tailAt_of_not_lt h, naiveListLoop.eq_1]

theorem lstN_ws {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : isWs (b.uget i (usizeInBounds b i h)) = true) (acc : List α) (w : Bool) :
    naiveListLoop start item (tailAt b i) acc w
      = naiveListLoop start item (tailAt b (i + 1)) acc w := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveListLoop.eq_2]
  simp only [hws, ↓reduceIte]

theorem lstN_close {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h93 : (b.uget i (usizeInBounds b i h) == 93) = true) (acc : List α) (w : Bool) :
    naiveListLoop start item (tailAt b i) acc w
      = (if w && !acc.isEmpty then .err .expectedList (tailAt b i)
         else .ok acc.reverse (tailAt b (i + 1))) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveListLoop.eq_2]
  simp only [hws, h93, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem lstN_comma {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h93 : ¬ (b.uget i (usizeInBounds b i h) == 93) = true)
    (h44 : (b.uget i (usizeInBounds b i h) == 44) = true) (acc : List α) (w : Bool) :
    naiveListLoop start item (tailAt b i) acc w
      = (if w then .err .expectedList (tailAt b i)
         else naiveListLoop start item (tailAt b (i + 1)) acc true) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveListLoop.eq_2]
  simp only [hws, h93, h44, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem lstN_other {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h93 : ¬ (b.uget i (usizeInBounds b i h) == 93) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (hst : ¬ start (b.uget i (usizeInBounds b i h)) = true) (acc : List α) (w : Bool) :
    naiveListLoop start item (tailAt b i) acc w = .err .expectedList (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveListLoop.eq_2]
  simp only [hws, h93, h44, hst, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem lstN_notwant {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h93 : ¬ (b.uget i (usizeInBounds b i h) == 93) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (hst : start (b.uget i (usizeInBounds b i h)) = true) {w : Bool} (hw : (!w) = true)
    (acc : List α) :
    naiveListLoop start item (tailAt b i) acc w = .err .expectedList (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveListLoop.eq_2]
  simp only [hws, h93, h44, hst, hw, ↓reduceIte, Bool.false_eq_true]
  rw [← tailAt_of_lt h]

theorem lstN_item_err {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h93 : ¬ (b.uget i (usizeInBounds b i h) == 93) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (hst : start (b.uget i (usizeInBounds b i h)) = true) {w : Bool} (hw : ¬ (!w) = true)
    (acc : List α) {t : ErrTag} {r : List UInt8} (hit : item (tailAt b i) = .err t r) :
    naiveListLoop start item (tailAt b i) acc w = .err t r := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveListLoop.eq_2]
  rw [← tailAt_of_lt h]
  simp only [hws, h93, h44, hst, hw, hit, ↓reduceIte, Bool.false_eq_true]

theorem lstN_item_ok {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h93 : ¬ (b.uget i (usizeInBounds b i h) == 93) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (hst : start (b.uget i (usizeInBounds b i h)) = true) {w : Bool} (hw : ¬ (!w) = true)
    (acc : List α) {x : α} {r : List UInt8} (hit : item (tailAt b i) = .ok x r)
    (hlt : r.length < (tailAt b i).length) :
    naiveListLoop start item (tailAt b i) acc w
      = naiveListLoop start item r (x :: acc) false := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveListLoop.eq_2]
  rw [← tailAt_of_lt h]
  simp only [hws, h93, h44, hst, hw, hit, hlt, ↓reduceIte, Bool.false_eq_true, ↓reduceDIte]

theorem lstN_item_stuck {b : ByteArray} {i : USize} (h : i < b.usize)
    (hws : ¬ isWs (b.uget i (usizeInBounds b i h)) = true)
    (h93 : ¬ (b.uget i (usizeInBounds b i h) == 93) = true)
    (h44 : ¬ (b.uget i (usizeInBounds b i h) == 44) = true)
    (hst : start (b.uget i (usizeInBounds b i h)) = true) {w : Bool} (hw : ¬ (!w) = true)
    (acc : List α) {x : α} {r : List UInt8} (hit : item (tailAt b i) = .ok x r)
    (hlt : ¬ r.length < (tailAt b i).length) :
    naiveListLoop start item (tailAt b i) acc w = .err .noProgress (tailAt b i) := by
  conv => lhs; rw [tailAt_of_lt h]
  rw [naiveListLoop.eq_2]
  rw [← tailAt_of_lt h]
  simp only [hws, h93, h44, hst, hw, hit, hlt, ↓reduceIte, Bool.false_eq_true, ↓reduceDIte]

end ListNaive

theorem listErrFacts {α : Type} {b : ByteArray} {i : USize} {res : NRes α} {err : ScanErr}
    (hres : liftRes b i res = .err err) :
    ∃ t r, res = .err t r ∧ err = ⟨posAt i.toNat (tailAt b i) r, t⟩ := by
  cases hr : res with
  | ok x r => rw [hr] at hres; simp only [liftRes] at hres; exact absurd hres (by simp)
  | err t r =>
    refine ⟨t, r, rfl, ?_⟩
    rw [hr, liftRes_err_pos] at hres
    simpa using hres.symm

theorem listOkFacts {α : Type} {b : ByteArray} {i e : USize} {x : α} {res : NRes α}
    (h : i < b.usize) (hrs : res.rest <:+ tailAt b i) (hres : liftRes b i res = .ok x e) :
    res = .ok x (tailAt b e) ∧ i.toNat ≤ e.toNat ∧ e.toNat ≤ b.usize.toNat ∧
      (i < e ↔ (tailAt b e).length < (tailAt b i).length) := by
  have hi : i.toNat < (bytes b).length := toNat_tailAt_lt h
  cases hr : res with
  | err t r => rw [hr] at hres; simp only [liftRes] at hres; exact absurd hres (by simp)
  | ok x' r =>
    rw [hr] at hres hrs
    simp only [NRes.rest] at hrs
    simp only [liftRes, ScanRes.ok.injEq] at hres
    obtain ⟨hx, he⟩ := hres
    subst hx
    have hen : e.toNat = posAt i.toNat (tailAt b i) r := by
      rw [← he]; exact toNat_toUSize_posAt (Nat.le_of_lt hi) hrs
    have hten : tailAt b e = r := by rw [← he]; exact tailAt_posAt (Nat.le_of_lt hi) hrs
    have hle := posAt_le (Nat.le_of_lt hi) hrs
    simp only [length_bytes] at hle
    refine ⟨by rw [hten], by rw [hen]; simp only [posAt]; omega, by rw [hen]; exact hle, ?_⟩
    rw [hten, ← he]
    exact lt_posAt_iff hi hrs

/-! ### One macro per case shape of a list loop -/

macro "l_end" : tactic => `(tactic|
  (rename_i h
   rw [lstN_end _ _ h, liftRes_err_self]))

macro "l_ws" fs:ident : tactic => `(tactic|
  (rename_i h c hws ih
   rw [lstN_ws _ _ h hws, ih]
   exact (liftRes_step _ h (naiveListLoop_rest_suffix _ _ $fs:ident _ _ _)).symm))

macro "l_close_err" : tactic => `(tactic|
  (rename_i h c hws h93 hne
   rw [lstN_close _ _ h hws h93]
   simp only [hne, ↓reduceIte]
   rw [liftRes_err_self]))

macro "l_close_ok" : tactic => `(tactic|
  (rename_i h c hws h93 hne
   rw [lstN_close _ _ h hws h93]
   simp only [hne, ↓reduceIte, Bool.false_eq_true]
   rw [liftRes_ok_step h]))

macro "l_comma_err" : tactic => `(tactic|
  (rename_i h c hws h93 h44
   rw [lstN_comma _ _ h hws h93 h44]
   simp only [↓reduceIte]
   rw [liftRes_err_self]))

macro "l_comma" fs:ident : tactic => `(tactic|
  (rename_i h c hws h93 h44 hw ih
   rw [lstN_comma _ _ h hws h93 h44]
   simp only [hw, ↓reduceIte, Bool.false_eq_true]
   rw [ih]
   exact (liftRes_step _ h (naiveListLoop_rest_suffix _ _ $fs:ident _ _ _)).symm))

macro "l_other" : tactic => `(tactic|
  (rename_i h c hws h93 h44 hst
   rw [lstN_other _ _ h hws h93 h44 hst, liftRes_err_self]))

macro "l_notwant" : tactic => `(tactic|
  (rename_i h c hws h93 h44 hst hw
   rw [lstN_notwant _ _ h hws h93 h44 hst hw, liftRes_err_self]))

macro "l_item_err" tw:ident : tactic => `(tactic|
  (rename_i h c hws h93 h44 hst hw err hit
   rw [$tw:ident] at hit
   obtain ⟨t, r, hr, hlift⟩ := listErrFacts hit
   rw [lstN_item_err _ _ h hws h93 h44 hst hw _ hr, liftRes_err_pos, hlift]))

macro "l_item" tw:ident fs:ident : tactic => `(tactic|
  (rename_i h c hws h93 h44 hst hw x e hit hj ih
   rw [$tw:ident] at hit
   obtain ⟨hr, hile, heb, hiff⟩ := listOkFacts h ($fs:ident _) hit
   rw [lstN_item_ok _ _ h hws h93 h44 hst hw _ hr (hiff.mp hj), ih]
   exact (liftRes_jump _ hile heb (naiveListLoop_rest_suffix _ _ $fs:ident _ _ _)).symm))

macro "l_item_stuck" tw:ident fs:ident : tactic => `(tactic|
  (rename_i h c hws h93 h44 hst hw x e hit hj
   rw [$tw:ident] at hit
   obtain ⟨hr, hile, heb, hiff⟩ := listOkFacts h ($fs:ident _) hit
   rw [lstN_item_stuck _ _ h hws h93 h44 hst hw _ hr (fun hx => hj (hiff.mpr hx)),
     liftRes_err_self]))

/-- The eleven cases of a list loop. -/
macro "lst_all" tw:ident fs:ident : tactic => `(tactic|
  (case case1 => l_ws $fs:ident
   case case2 => l_close_err
   case case3 => l_close_ok
   case case4 => l_comma_err
   case case5 => l_comma $fs:ident
   case case6 => l_notwant
   case case7 => l_item_err $tw:ident
   case case8 => l_item $tw:ident $fs:ident
   case case9 => l_item_stuck $tw:ident $fs:ident
   case case10 => l_other
   case case11 => l_end))


/-! ### `scanStrName` -/

theorem strNameFields_read_suffix : ∀ k slot, strNameFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [strNameFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveStrName_rest_suffix (l : List UInt8) : (naiveStrName l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ strNameFields_read_suffix _ _ l

theorem scanStrNameLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (pre : Nat) (s : String) :
    scanStrNameLoop b i wantMember seen pre s =
      liftRes b i ((naiveObjLoop strNameFields 3 (tailAt b i) wantMember seen (pre, s)).map
        (fun (p, s) => NameRec.str p s)) := by
  fun_induction scanStrNameLoop b i wantMember seen pre s
  obj_head strNameFields_read_suffix
  obj_num strNameFields_read_suffix case10 case11 case12 case13
  obj_sub strNameFields_read_suffix case14 case15 case16 case17
  case case18 => o_unknown strNameFields x1 x2
  case case19 => o_other
  case case20 => o_end

theorem scanStrName_eq (b : ByteArray) (i : USize) :
    scanStrName b i = liftRes b i (naiveStrName (tailAt b i)) := by
  unfold scanStrName naiveStrName
  exact objWrap strNameFields_read_suffix (scanStrNameLoop_eq b (i + 1) true 0 0 "")

/-! ### `scanNumName` -/

theorem numNameFields_read_suffix : ∀ k slot, numNameFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [numNameFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveNumName_rest_suffix (l : List UInt8) : (naiveNumName l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ numNameFields_read_suffix _ _ l

theorem scanNumNameLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (n pre : Nat) :
    scanNumNameLoop b i wantMember seen n pre =
      liftRes b i ((naiveObjLoop numNameFields 3 (tailAt b i) wantMember seen (n, pre)).map
        (fun (n, p) => NameRec.num p n)) := by
  fun_induction scanNumNameLoop b i wantMember seen n pre
  obj_head numNameFields_read_suffix
  obj_num numNameFields_read_suffix case10 case11 case12 case13
  obj_num numNameFields_read_suffix case14 case15 case16 case17
  case case18 => o_unknown numNameFields x1 x2
  case case19 => o_other
  case case20 => o_end

theorem scanNumName_eq (b : ByteArray) (i : USize) :
    scanNumName b i = liftRes b i (naiveNumName (tailAt b i)) := by
  unfold scanNumName naiveNumName
  exact objWrap numNameFields_read_suffix (scanNumNameLoop_eq b (i + 1) true 0 0 0)

/-! ### `scanAppExpr` -/

theorem appFields_read_suffix : ∀ k slot, appFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [appFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveAppExpr_rest_suffix (l : List UInt8) : (naiveAppExpr l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ appFields_read_suffix _ _ l

theorem scanAppExprLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (arg fn : Nat) :
    scanAppExprLoop b i wantMember seen arg fn =
      liftRes b i ((naiveObjLoop appFields 3 (tailAt b i) wantMember seen (arg, fn)).map
        (fun (a, f) => ExprRec.app f a)) := by
  fun_induction scanAppExprLoop b i wantMember seen arg fn
  obj_head appFields_read_suffix
  obj_num appFields_read_suffix case10 case11 case12 case13
  obj_num appFields_read_suffix case14 case15 case16 case17
  case case18 => o_unknown appFields x1 x2
  case case19 => o_other
  case case20 => o_end

theorem scanAppExpr_eq (b : ByteArray) (i : USize) :
    scanAppExpr b i = liftRes b i (naiveAppExpr (tailAt b i)) := by
  unfold scanAppExpr naiveAppExpr
  exact objWrap appFields_read_suffix (scanAppExprLoop_eq b (i + 1) true 0 0 0)

/-! ### `scanLamExpr` -/

theorem binderFields_read_suffix : ∀ k slot, binderFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [binderFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveLamExpr_rest_suffix (l : List UInt8) : (naiveLamExpr l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ binderFields_read_suffix _ _ l

theorem scanLamExprLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (bd ty : Nat) (pw : PwRec) :
    scanLamExprLoop b i wantMember seen bd ty pw =
      liftRes b i ((naiveObjLoop binderFields 15 (tailAt b i) wantMember seen (bd, ty, pw)).map
        (fun (b, t, p) => ExprRec.lam t b p)) := by
  fun_induction scanLamExprLoop b i wantMember seen bd ty pw
  obj_head binderFields_read_suffix
  obj_bi binderFields_read_suffix case10 case11 case12 case13
  obj_num binderFields_read_suffix case14 case15 case16 case17
  obj_num binderFields_read_suffix case18 case19 case20 case21
  obj_num binderFields_read_suffix case22 case23 case24 case25
  obj_sub binderFields_read_suffix case26 case27 case28 case29
  case case30 => o_unknown binderFields x1 x2 x3 x4 x5
  case case31 => o_other
  case case32 => o_end

theorem scanLamExpr_eq (b : ByteArray) (i : USize) :
    scanLamExpr b i = liftRes b i (naiveLamExpr (tailAt b i)) := by
  unfold scanLamExpr naiveLamExpr
  exact objWrap binderFields_read_suffix (scanLamExprLoop_eq b (i + 1) true 0 0 0 .never)

/-! ### `scanForallExpr` -/

theorem naiveForallExpr_rest_suffix (l : List UInt8) : (naiveForallExpr l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ binderFields_read_suffix _ _ l

theorem scanForallExprLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (bd ty : Nat) (pw : PwRec) :
    scanForallExprLoop b i wantMember seen bd ty pw =
      liftRes b i ((naiveObjLoop binderFields 15 (tailAt b i) wantMember seen (bd, ty, pw)).map
        (fun (b, t, p) => ExprRec.forallE t b p)) := by
  fun_induction scanForallExprLoop b i wantMember seen bd ty pw
  obj_head binderFields_read_suffix
  obj_bi binderFields_read_suffix case10 case11 case12 case13
  obj_num binderFields_read_suffix case14 case15 case16 case17
  obj_num binderFields_read_suffix case18 case19 case20 case21
  obj_num binderFields_read_suffix case22 case23 case24 case25
  obj_sub binderFields_read_suffix case26 case27 case28 case29
  case case30 => o_unknown binderFields x1 x2 x3 x4 x5
  case case31 => o_other
  case case32 => o_end

theorem scanForallExpr_eq (b : ByteArray) (i : USize) :
    scanForallExpr b i = liftRes b i (naiveForallExpr (tailAt b i)) := by
  unfold scanForallExpr naiveForallExpr
  exact objWrap binderFields_read_suffix (scanForallExprLoop_eq b (i + 1) true 0 0 0 .never)

/-! ### `scanLetExpr` -/

theorem letFields_read_suffix : ∀ k slot, letFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [letFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveLetExpr_rest_suffix (l : List UInt8) : (naiveLetExpr l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ letFields_read_suffix _ _ l

theorem scanLetExprLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (bd ty vl : Nat) :
    scanLetExprLoop b i wantMember seen bd ty vl =
      liftRes b i ((naiveObjLoop letFields 27 (tailAt b i) wantMember seen (bd, ty, vl)).map
        (fun (b, t, v) => ExprRec.letE t v b)) := by
  fun_induction scanLetExprLoop b i wantMember seen bd ty vl
  obj_head letFields_read_suffix
  obj_num letFields_read_suffix case10 case11 case12 case13
  obj_num letFields_read_suffix case14 case15 case16 case17
  obj_sub letFields_read_suffix case18 case19 case20 case21
  obj_num letFields_read_suffix case22 case23 case24 case25
  obj_num letFields_read_suffix case26 case27 case28 case29
  case case30 => o_unknown letFields x1 x2 x3 x4 x5
  case case31 => o_other
  case case32 => o_end

theorem scanLetExpr_eq (b : ByteArray) (i : USize) :
    scanLetExpr b i = liftRes b i (naiveLetExpr (tailAt b i)) := by
  unfold scanLetExpr naiveLetExpr
  exact objWrap letFields_read_suffix (scanLetExprLoop_eq b (i + 1) true 0 0 0 0)

/-! ### `scanConstExpr` -/

theorem constFields_read_suffix : ∀ k slot, constFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [constFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveConstExpr_rest_suffix (l : List UInt8) : (naiveConstExpr l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ constFields_read_suffix _ _ l

theorem scanConstExprLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (nm : Nat) (us : List Nat) :
    scanConstExprLoop b i wantMember seen nm us =
      liftRes b i ((naiveObjLoop constFields 3 (tailAt b i) wantMember seen (nm, us)).map
        (fun (n, us) => ExprRec.const n us)) := by
  fun_induction scanConstExprLoop b i wantMember seen nm us
  obj_head constFields_read_suffix
  obj_num constFields_read_suffix case10 case11 case12 case13
  obj_sub constFields_read_suffix case14 case15 case16 case17
  case case18 => o_unknown constFields x1 x2
  case case19 => o_other
  case case20 => o_end

theorem scanConstExpr_eq (b : ByteArray) (i : USize) :
    scanConstExpr b i = liftRes b i (naiveConstExpr (tailAt b i)) := by
  unfold scanConstExpr naiveConstExpr
  exact objWrap constFields_read_suffix (scanConstExprLoop_eq b (i + 1) true 0 0 [])

/-! ### `scanProjExpr` -/

theorem projFields_read_suffix : ∀ k slot, projFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [projFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveProjExpr_rest_suffix (l : List UInt8) : (naiveProjExpr l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ projFields_read_suffix _ _ l

theorem scanProjExprLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (ix st tn : Nat) :
    scanProjExprLoop b i wantMember seen ix st tn =
      liftRes b i ((naiveObjLoop projFields 7 (tailAt b i) wantMember seen (ix, st, tn)).map
        (fun (i, s, t) => ExprRec.proj t i s)) := by
  fun_induction scanProjExprLoop b i wantMember seen ix st tn
  obj_head projFields_read_suffix
  obj_num projFields_read_suffix case10 case11 case12 case13
  obj_num projFields_read_suffix case14 case15 case16 case17
  obj_num projFields_read_suffix case18 case19 case20 case21
  case case22 => o_unknown projFields x1 x2 x3
  case case23 => o_other
  case case24 => o_end

theorem scanProjExpr_eq (b : ByteArray) (i : USize) :
    scanProjExpr b i = liftRes b i (naiveProjExpr (tailAt b i)) := by
  unfold scanProjExpr naiveProjExpr
  exact objWrap projFields_read_suffix (scanProjExprLoop_eq b (i + 1) true 0 0 0 0)

/-! ### `scanRule` -/

theorem ruleFields_read_suffix : ∀ k slot, ruleFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [ruleFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveRule_rest_suffix (l : List UInt8) : (naiveRule l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ ruleFields_read_suffix _ _ l

theorem scanRuleLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (ct nf rhs : Nat) :
    scanRuleLoop b i wantMember seen ct nf rhs =
      liftRes b i ((naiveObjLoop ruleFields 7 (tailAt b i) wantMember seen ⟨ct, nf, rhs⟩).map
        (id)) := by
  fun_induction scanRuleLoop b i wantMember seen ct nf rhs
  obj_head ruleFields_read_suffix
  obj_num ruleFields_read_suffix case10 case11 case12 case13
  obj_num ruleFields_read_suffix case14 case15 case16 case17
  obj_num ruleFields_read_suffix case18 case19 case20 case21
  case case22 => o_unknown ruleFields x1 x2 x3
  case case23 => o_other
  case case24 => o_end

theorem scanRule_eq (b : ByteArray) (i : USize) :
    scanRule b i = liftRes b i (naiveRule (tailAt b i)) := by
  unfold scanRule naiveRule
  exact objWrap ruleFields_read_suffix (scanRuleLoop_eq b (i + 1) true 0 0 0 0)

theorem naiveRules_rest_suffix (l : List UInt8) : (naiveRules l).rest <:+ l := by
  exact naiveList_rest_suffix _ _ naiveRule_rest_suffix l

theorem scanRuleListLoop_eq (b : ByteArray) (i : USize) (acc : List _) (w : Bool) :
    scanRuleListLoop b i acc w = liftRes b i (naiveListLoop (· == 123) naiveRule (tailAt b i) acc w) := by
  fun_induction scanRuleListLoop b i acc w
  lst_all scanRule_eq naiveRule_rest_suffix

theorem scanRules_eq (b : ByteArray) (i : USize) :
    scanRules b i = liftRes b i (naiveRules (tailAt b i)) := by
  unfold scanRules naiveRules
  exact listWrap naiveRule_rest_suffix (scanRuleListLoop_eq b (i + 1) [] true)


/- `Rules` is now a slot scanner of the objects below. -/
macro_rules
  | `(tactic| sub_suffix) => `(tactic| exact naiveRules_rest_suffix _)
macro_rules
  | `(tactic| sub_twin $hs:ident $ht:ident) =>
      `(tactic| rw [scanRules_eq, $ht:ident] at $hs:ident)

/-! ### `scanIndRec` -/

theorem indRecFields_read_suffix : ∀ k slot, indRecFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [indRecFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveIndRec_rest_suffix (l : List UInt8) : (naiveIndRec l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ indRecFields_read_suffix _ _ l

theorem scanIndRecLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (isUns kf : Bool) (lps : List Nat) (nm nIdx nMin nMot nP : Nat) (rules : List RuleRec) (ty : Nat) :
    scanIndRecLoop b i wantMember seen isUns kf lps nm nIdx nMin nMot nP rules ty =
      liftRes b i ((naiveObjLoop indRecFields 2046 (tailAt b i) wantMember seen ⟨⟨nm, lps, ty⟩, isUns, kf, nIdx, nMin, nMot, nP, rules⟩).map
        (id)) := by
  fun_induction scanIndRecLoop b i wantMember seen isUns kf lps nm nIdx nMin nMot nP rules ty
  obj_head indRecFields_read_suffix
  obj_sub indRecFields_read_suffix case10 case11 case12 case13
  obj_sub indRecFields_read_suffix case14 case15 case16 case17
  obj_sub indRecFields_read_suffix case18 case19 case20 case21
  obj_sub indRecFields_read_suffix case22 case23 case24 case25
  obj_num indRecFields_read_suffix case26 case27 case28 case29
  obj_num indRecFields_read_suffix case30 case31 case32 case33
  obj_num indRecFields_read_suffix case34 case35 case36 case37
  obj_num indRecFields_read_suffix case38 case39 case40 case41
  obj_num indRecFields_read_suffix case42 case43 case44 case45
  obj_sub indRecFields_read_suffix case46 case47 case48 case49
  obj_num indRecFields_read_suffix case50 case51 case52 case53
  case case54 => o_unknown indRecFields x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
  case case55 => o_other
  case case56 => o_end

theorem scanIndRec_eq (b : ByteArray) (i : USize) :
    scanIndRec b i = liftRes b i (naiveIndRec (tailAt b i)) := by
  unfold scanIndRec naiveIndRec
  exact objWrap indRecFields_read_suffix (scanIndRecLoop_eq b (i + 1) true 0 false false [] 0 0 0 0 0 [] 0)

theorem naiveIndRecs_rest_suffix (l : List UInt8) : (naiveIndRecs l).rest <:+ l := by
  exact naiveList_rest_suffix _ _ naiveIndRec_rest_suffix l

theorem scanIndRecListLoop_eq (b : ByteArray) (i : USize) (acc : List _) (w : Bool) :
    scanIndRecListLoop b i acc w = liftRes b i (naiveListLoop (· == 123) naiveIndRec (tailAt b i) acc w) := by
  fun_induction scanIndRecListLoop b i acc w
  lst_all scanIndRec_eq naiveIndRec_rest_suffix

theorem scanIndRecs_eq (b : ByteArray) (i : USize) :
    scanIndRecs b i = liftRes b i (naiveIndRecs (tailAt b i)) := by
  unfold scanIndRecs naiveIndRecs
  exact listWrap naiveIndRec_rest_suffix (scanIndRecListLoop_eq b (i + 1) [] true)


/- `IndRecs` is now a slot scanner of the objects below. -/
macro_rules
  | `(tactic| sub_suffix) => `(tactic| exact naiveIndRecs_rest_suffix _)
macro_rules
  | `(tactic| sub_twin $hs:ident $ht:ident) =>
      `(tactic| rw [scanIndRecs_eq, $ht:ident] at $hs:ident)

/-! ### `scanIndType` -/

theorem indTypeFields_read_suffix : ∀ k slot, indTypeFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [indTypeFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveIndType_rest_suffix (l : List UInt8) : (naiveIndType l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ indTypeFields_read_suffix _ _ l

theorem scanIndTypeLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (ctors : List Nat) (isRec isRefl isUns : Bool) (lps : List Nat) (nm nIdx nNest nP ty : Nat) :
    scanIndTypeLoop b i wantMember seen ctors isRec isRefl isUns lps nm nIdx nNest nP ty =
      liftRes b i ((naiveObjLoop indTypeFields 2046 (tailAt b i) wantMember seen ⟨⟨nm, lps, ty⟩, ctors, isRec, isRefl, isUns, nIdx, nNest, nP⟩).map
        (id)) := by
  fun_induction scanIndTypeLoop b i wantMember seen ctors isRec isRefl isUns lps nm nIdx nNest nP ty
  obj_head indTypeFields_read_suffix
  obj_sub indTypeFields_read_suffix case10 case11 case12 case13
  obj_sub indTypeFields_read_suffix case14 case15 case16 case17
  obj_sub indTypeFields_read_suffix case18 case19 case20 case21
  obj_sub indTypeFields_read_suffix case22 case23 case24 case25
  obj_sub indTypeFields_read_suffix case26 case27 case28 case29
  obj_sub indTypeFields_read_suffix case30 case31 case32 case33
  obj_num indTypeFields_read_suffix case34 case35 case36 case37
  obj_num indTypeFields_read_suffix case38 case39 case40 case41
  obj_num indTypeFields_read_suffix case42 case43 case44 case45
  obj_num indTypeFields_read_suffix case46 case47 case48 case49
  obj_num indTypeFields_read_suffix case50 case51 case52 case53
  case case54 => o_unknown indTypeFields x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
  case case55 => o_other
  case case56 => o_end

theorem scanIndType_eq (b : ByteArray) (i : USize) :
    scanIndType b i = liftRes b i (naiveIndType (tailAt b i)) := by
  unfold scanIndType naiveIndType
  exact objWrap indTypeFields_read_suffix (scanIndTypeLoop_eq b (i + 1) true 0 [] false false false [] 0 0 0 0 0)

theorem naiveIndTypes_rest_suffix (l : List UInt8) : (naiveIndTypes l).rest <:+ l := by
  exact naiveList_rest_suffix _ _ naiveIndType_rest_suffix l

theorem scanIndTypeListLoop_eq (b : ByteArray) (i : USize) (acc : List _) (w : Bool) :
    scanIndTypeListLoop b i acc w = liftRes b i (naiveListLoop (· == 123) naiveIndType (tailAt b i) acc w) := by
  fun_induction scanIndTypeListLoop b i acc w
  lst_all scanIndType_eq naiveIndType_rest_suffix

theorem scanIndTypes_eq (b : ByteArray) (i : USize) :
    scanIndTypes b i = liftRes b i (naiveIndTypes (tailAt b i)) := by
  unfold scanIndTypes naiveIndTypes
  exact listWrap naiveIndType_rest_suffix (scanIndTypeListLoop_eq b (i + 1) [] true)


/- `IndTypes` is now a slot scanner of the objects below. -/
macro_rules
  | `(tactic| sub_suffix) => `(tactic| exact naiveIndTypes_rest_suffix _)
macro_rules
  | `(tactic| sub_twin $hs:ident $ht:ident) =>
      `(tactic| rw [scanIndTypes_eq, $ht:ident] at $hs:ident)

/-! ### `scanIndCtor` -/

theorem indCtorFields_read_suffix : ∀ k slot, indCtorFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [indCtorFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveIndCtor_rest_suffix (l : List UInt8) : (naiveIndCtor l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ indCtorFields_read_suffix _ _ l

theorem scanIndCtorLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (isUns : Bool) (lps : List Nat) (nm nF nP ty : Nat) (ci ind : Option Nat) :
    scanIndCtorLoop b i wantMember seen isUns lps nm nF nP ty ci ind =
      liftRes b i ((naiveObjLoop indCtorFields 252 (tailAt b i) wantMember seen
          ⟨⟨nm, lps, ty⟩, isUns, nF, nP, ci, ind⟩).map
        (id)) := by
  fun_induction scanIndCtorLoop b i wantMember seen isUns lps nm nF nP ty ci ind
  obj_head indCtorFields_read_suffix
  obj_num indCtorFields_read_suffix case10 case11 case12 case13
  obj_num indCtorFields_read_suffix case14 case15 case16 case17
  obj_sub indCtorFields_read_suffix case18 case19 case20 case21
  obj_sub indCtorFields_read_suffix case22 case23 case24 case25
  obj_num indCtorFields_read_suffix case26 case27 case28 case29
  obj_num indCtorFields_read_suffix case30 case31 case32 case33
  obj_num indCtorFields_read_suffix case34 case35 case36 case37
  obj_num indCtorFields_read_suffix case38 case39 case40 case41
  case case42 => o_unknown indCtorFields x1 x2 x3 x4 x5 x6 x7 x8
  case case43 => o_other
  case case44 => o_end

theorem scanIndCtor_eq (b : ByteArray) (i : USize) :
    scanIndCtor b i = liftRes b i (naiveIndCtor (tailAt b i)) := by
  unfold scanIndCtor naiveIndCtor
  exact objWrap indCtorFields_read_suffix
    (scanIndCtorLoop_eq b (i + 1) true 0 false [] 0 0 0 0 none none)

theorem naiveIndCtors_rest_suffix (l : List UInt8) : (naiveIndCtors l).rest <:+ l := by
  exact naiveList_rest_suffix _ _ naiveIndCtor_rest_suffix l

theorem scanIndCtorListLoop_eq (b : ByteArray) (i : USize) (acc : List _) (w : Bool) :
    scanIndCtorListLoop b i acc w = liftRes b i (naiveListLoop (· == 123) naiveIndCtor (tailAt b i) acc w) := by
  fun_induction scanIndCtorListLoop b i acc w
  lst_all scanIndCtor_eq naiveIndCtor_rest_suffix

theorem scanIndCtors_eq (b : ByteArray) (i : USize) :
    scanIndCtors b i = liftRes b i (naiveIndCtors (tailAt b i)) := by
  unfold scanIndCtors naiveIndCtors
  exact listWrap naiveIndCtor_rest_suffix (scanIndCtorListLoop_eq b (i + 1) [] true)


/- `IndCtors` is now a slot scanner of the objects below. -/
macro_rules
  | `(tactic| sub_suffix) => `(tactic| exact naiveIndCtors_rest_suffix _)
macro_rules
  | `(tactic| sub_twin $hs:ident $ht:ident) =>
      `(tactic| rw [scanIndCtors_eq, $ht:ident] at $hs:ident)

/-! ### `scanAxiomDecl` -/

theorem axiomFields_read_suffix : ∀ k slot, axiomFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [axiomFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveAxiomDecl_rest_suffix (l : List UInt8) : (naiveAxiomDecl l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ axiomFields_read_suffix _ _ l

theorem scanAxiomDeclLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (isUns : Bool) (lps : List Nat) (nm ty : Nat) :
    scanAxiomDeclLoop b i wantMember seen isUns lps nm ty =
      liftRes b i ((naiveObjLoop axiomFields 15 (tailAt b i) wantMember seen { cv := ⟨nm, lps, ty⟩, isUnsafe := isUns }).map
        (fun d => DeclRec.ax d.cv d.isUnsafe)) := by
  fun_induction scanAxiomDeclLoop b i wantMember seen isUns lps nm ty
  obj_head axiomFields_read_suffix
  obj_sub axiomFields_read_suffix case10 case11 case12 case13
  obj_sub axiomFields_read_suffix case14 case15 case16 case17
  obj_num axiomFields_read_suffix case18 case19 case20 case21
  obj_num axiomFields_read_suffix case22 case23 case24 case25
  case case26 => o_unknown axiomFields x1 x2 x3 x4
  case case27 => o_other
  case case28 => o_end

theorem scanAxiomDecl_eq (b : ByteArray) (i : USize) :
    scanAxiomDecl b i = liftRes b i (naiveAxiomDecl (tailAt b i)) := by
  unfold scanAxiomDecl naiveAxiomDecl
  exact objWrap axiomFields_read_suffix (scanAxiomDeclLoop_eq b (i + 1) true 0 false [] 0 0)

/-! ### `scanDefDecl` -/

theorem defFields_read_suffix : ∀ k slot, defFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [defFields, cvSlots, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveDefDecl_rest_suffix (l : List UInt8) : (naiveDefDecl l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ defFields_read_suffix _ _ l

theorem scanDefDeclLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (hints : HintsRec) (lps : List Nat) (nm : Nat) (safety : String) (ty vl : Nat) :
    scanDefDeclLoop b i wantMember seen hints lps nm safety ty vl =
      liftRes b i ((naiveObjLoop defFields 124 (tailAt b i) wantMember seen { cv := ⟨nm, lps, ty⟩, value := vl, hints := hints, safety := safety }).map
        (fun d => DeclRec.defn d.cv d.value d.hints d.safety)) := by
  fun_induction scanDefDeclLoop b i wantMember seen hints lps nm safety ty vl
  obj_head defFields_read_suffix
  obj_sub defFields_read_suffix case10 case11 case12 case13
  obj_sub defFields_read_suffix case14 case15 case16 case17
  obj_sub defFields_read_suffix case18 case19 case20 case21
  obj_num defFields_read_suffix case22 case23 case24 case25
  obj_sub defFields_read_suffix case26 case27 case28 case29
  obj_num defFields_read_suffix case30 case31 case32 case33
  obj_num defFields_read_suffix case34 case35 case36 case37
  case case38 => o_unknown defFields x1 x2 x3 x4 x5 x6 x7
  case case39 => o_other
  case case40 => o_end

theorem scanDefDecl_eq (b : ByteArray) (i : USize) :
    scanDefDecl b i = liftRes b i (naiveDefDecl (tailAt b i)) := by
  unfold scanDefDecl naiveDefDecl
  exact objWrap defFields_read_suffix (scanDefDeclLoop_eq b (i + 1) true 0 (.regular 0) [] 0 "" 0 0)

/-! ### `scanThmDecl` -/

theorem thmFields_read_suffix : ∀ k slot, thmFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [thmFields, cvSlots, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveThmDecl_rest_suffix (l : List UInt8) : (naiveThmDecl l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ thmFields_read_suffix _ _ l

theorem scanThmDeclLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (lps : List Nat) (nm ty vl : Nat) :
    scanThmDeclLoop b i wantMember seen lps nm ty vl =
      liftRes b i ((naiveObjLoop thmFields 30 (tailAt b i) wantMember seen { cv := ⟨nm, lps, ty⟩, value := vl }).map
        (fun d => DeclRec.thm d.cv d.value)) := by
  fun_induction scanThmDeclLoop b i wantMember seen lps nm ty vl
  obj_head thmFields_read_suffix
  obj_sub thmFields_read_suffix case10 case11 case12 case13
  obj_sub thmFields_read_suffix case14 case15 case16 case17
  obj_num thmFields_read_suffix case18 case19 case20 case21
  obj_num thmFields_read_suffix case22 case23 case24 case25
  obj_num thmFields_read_suffix case26 case27 case28 case29
  case case30 => o_unknown thmFields x1 x2 x3 x4 x5
  case case31 => o_other
  case case32 => o_end

theorem scanThmDecl_eq (b : ByteArray) (i : USize) :
    scanThmDecl b i = liftRes b i (naiveThmDecl (tailAt b i)) := by
  unfold scanThmDecl naiveThmDecl
  exact objWrap thmFields_read_suffix (scanThmDeclLoop_eq b (i + 1) true 0 [] 0 0 0)

/-! ### `scanOpaqueDecl` -/

theorem opaqueFields_read_suffix : ∀ k slot, opaqueFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [opaqueFields, cvSlots, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveOpaqueDecl_rest_suffix (l : List UInt8) : (naiveOpaqueDecl l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ opaqueFields_read_suffix _ _ l

theorem scanOpaqueDeclLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (isUns : Bool) (lps : List Nat) (nm ty vl : Nat) :
    scanOpaqueDeclLoop b i wantMember seen isUns lps nm ty vl =
      liftRes b i ((naiveObjLoop opaqueFields 62 (tailAt b i) wantMember seen { cv := ⟨nm, lps, ty⟩, isUnsafe := isUns, value := vl }).map
        (fun d => DeclRec.opaq d.cv d.value d.isUnsafe)) := by
  fun_induction scanOpaqueDeclLoop b i wantMember seen isUns lps nm ty vl
  obj_head opaqueFields_read_suffix
  obj_sub opaqueFields_read_suffix case10 case11 case12 case13
  obj_sub opaqueFields_read_suffix case14 case15 case16 case17
  obj_sub opaqueFields_read_suffix case18 case19 case20 case21
  obj_num opaqueFields_read_suffix case22 case23 case24 case25
  obj_num opaqueFields_read_suffix case26 case27 case28 case29
  obj_num opaqueFields_read_suffix case30 case31 case32 case33
  case case34 => o_unknown opaqueFields x1 x2 x3 x4 x5 x6
  case case35 => o_other
  case case36 => o_end

theorem scanOpaqueDecl_eq (b : ByteArray) (i : USize) :
    scanOpaqueDecl b i = liftRes b i (naiveOpaqueDecl (tailAt b i)) := by
  unfold scanOpaqueDecl naiveOpaqueDecl
  exact objWrap opaqueFields_read_suffix (scanOpaqueDeclLoop_eq b (i + 1) true 0 false [] 0 0 0)

/-! ### `scanQuotDecl` -/

theorem quotFields_read_suffix : ∀ k slot, quotFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [quotFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveQuotDecl_rest_suffix (l : List UInt8) : (naiveQuotDecl l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ quotFields_read_suffix _ _ l

theorem scanQuotDeclLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (kind : String) (lps : List Nat) (nm ty : Nat) :
    scanQuotDeclLoop b i wantMember seen kind lps nm ty =
      liftRes b i ((naiveObjLoop quotFields 15 (tailAt b i) wantMember seen { cv := ⟨nm, lps, ty⟩, kind := kind }).map
        (fun d => DeclRec.quot d.cv d.kind)) := by
  fun_induction scanQuotDeclLoop b i wantMember seen kind lps nm ty
  obj_head quotFields_read_suffix
  obj_sub quotFields_read_suffix case10 case11 case12 case13
  obj_sub quotFields_read_suffix case14 case15 case16 case17
  obj_num quotFields_read_suffix case18 case19 case20 case21
  obj_num quotFields_read_suffix case22 case23 case24 case25
  case case26 => o_unknown quotFields x1 x2 x3 x4
  case case27 => o_other
  case case28 => o_end

theorem scanQuotDecl_eq (b : ByteArray) (i : USize) :
    scanQuotDecl b i = liftRes b i (naiveQuotDecl (tailAt b i)) := by
  unfold scanQuotDecl naiveQuotDecl
  exact objWrap quotFields_read_suffix (scanQuotDeclLoop_eq b (i + 1) true 0 "" [] 0 0)

/-! ### `scanIndDecl` -/

theorem indFields_read_suffix : ∀ k slot, indFields k = some slot →
    ∀ l st, (slot.read l st).rest <:+ l := by
  intro k slot hf l st
  cases k <;> simp only [indFields, Option.some.injEq] at hf <;>
    first | exact absurd hf (by simp) | (subst hf; slot_rest)

theorem naiveIndDecl_rest_suffix (l : List UInt8) : (naiveIndDecl l).rest <:+ l := by
  exact naiveObject_rest_suffix _ _ indFields_read_suffix _ _ l

theorem scanIndDeclLoop_eq (b : ByteArray) (i : USize) (wantMember : Bool) (seen : UInt32)
    (ctors : List IndCtorRec) (recs : List IndRecRec) (types : List IndTypeRec) :
    scanIndDeclLoop b i wantMember seen ctors recs types =
      liftRes b i ((naiveObjLoop indFields 26 (tailAt b i) wantMember seen (ctors, recs, types)).map
        (fun (cs, rs, ts) => DeclRec.ind ts cs rs)) := by
  fun_induction scanIndDeclLoop b i wantMember seen ctors recs types
  obj_head indFields_read_suffix
  obj_sub indFields_read_suffix case10 case11 case12 case13
  obj_sub indFields_read_suffix case14 case15 case16 case17
  obj_sub indFields_read_suffix case18 case19 case20 case21
  obj_sub indFields_read_suffix case22 case23 case24 case25
  obj_sub indFields_read_suffix case26 case27 case28 case29
  case case30 => o_unknown indFields x1 x2 x3 x4 x5
  case case31 => o_other
  case case32 => o_end

theorem scanIndDecl_eq (b : ByteArray) (i : USize) :
    scanIndDecl b i = liftRes b i (naiveIndDecl (tailAt b i)) := by
  unfold scanIndDecl naiveIndDecl
  exact objWrap indFields_read_suffix (scanIndDeclLoop_eq b (i + 1) true 0 [] [] [])

end ConLeche.Frontend
