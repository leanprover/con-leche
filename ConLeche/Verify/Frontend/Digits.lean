module

public import ConLeche.Frontend.Scan.Naive
/- `import all`: the file-level statement (`ConLeche/Accepts.lean`)
interpolates its indices with `toString`, which on `Nat` is `Nat.repr`,
and `Init/Data/Repr.lean` is a module that does not expose `Nat.repr`,
`Nat.toDigits` or `Nat.toDigitsCore`.  Their computational content is
exactly what this module characterises — once, here, as `IsDec` — so
the private view is needed at this one site of the proof tier (the
other is the test that decides the template on a fixture,
`tests/ConLecheTests/FileTests.lean`). -/
import all Init.Data.Repr

public section

/-!
# The decimal rendering of a stream index

`s!"…{i}…"` writes `i : Nat` as `toString i = Nat.repr i`.  The naive
recogniser reads a number back with `naiveNum` — a digit run, `0`
standing alone, no other run starting with `0`, valued by `digitsVal`.
`IsDec d n` is the contract between the two: `d` is a non-empty run of
digit bytes without a leading zero (unless it is `0`) whose value is
`n`; `repr_isDec` says the rendering satisfies it, and `naiveNum_isDec`
says the recogniser reads such a run followed by a non-digit as `n`
and stops at the non-digit.  Nothing else about `Nat.repr` is used
anywhere.
-/

namespace ConLeche.Frontend

/-- A byte list is the decimal rendering of `n`. -/
structure IsDec (d : List UInt8) (n : Nat) : Prop where
  ne_nil : d ≠ []
  digits : ∀ c ∈ d, isDigit c = true
  no_leading_zero : d.head? = some 48 → d = [48]
  val : digitsVal d = n

/-! ## The rendering -/

/-- The byte of a decimal digit character. -/
theorem digitChar_byte {m : Nat} (hm : m < 10) :
    UInt8.ofNat (Nat.digitChar m).val.toNat = UInt8.ofNat (48 + m) := by
  have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 := by
    omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide

/-- `toDigitsCore` at base 10 with enough fuel: a run of digit
characters in front of the accumulator, with the four facts `IsDec`
needs about it (stated on the characters' bytes). -/
theorem toDigitsCore_spec (fuel : Nat) : ∀ (n : Nat) (acc : List Char), n < fuel →
    ∃ ds : List Char, Nat.toDigitsCore 10 fuel n acc = ds ++ acc ∧ ds ≠ [] ∧
      (∀ c ∈ ds, ∃ m, m < 10 ∧ c = Nat.digitChar m) ∧
      (ds.head? = some (Nat.digitChar 0) → ds = [Nat.digitChar 0]) ∧
      digitsVal (ds.map fun c => UInt8.ofNat c.val.toNat) = n := by
  induction fuel with
  | zero => intro n acc h; exact absurd h (Nat.not_lt_zero _)
  | succ fuel ih =>
    intro n acc hn
    rw [Nat.toDigitsCore.eq_2]
    by_cases h10 : n / 10 = 0
    · rw [if_pos h10]
      have hlt : n < 10 := Nat.div_eq_zero_iff_lt (by omega) |>.mp h10
      refine ⟨[Nat.digitChar (n % 10)], rfl, by simp, ?_, ?_, ?_⟩
      · intro c hc
        simp only [List.mem_singleton] at hc
        exact ⟨n % 10, Nat.mod_lt _ (by omega), hc⟩
      · intro h
        simp only [List.head?_cons, Option.some.injEq] at h
        rw [h]
      · simp only [List.map_cons, List.map_nil, digitsVal, List.foldl_cons, List.foldl_nil]
        rw [Nat.mod_eq_of_lt hlt, digitChar_byte hlt]
        simp only [Nat.zero_mul, Nat.zero_add, UInt8.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (by omega)]
        omega
    · rw [if_neg h10]
      have hge : 10 ≤ n := by omega
      obtain ⟨ds, hds, hne, hdig, hz, hval⟩ :=
        ih (n / 10) (Nat.digitChar (n % 10) :: acc) (by omega)
      refine ⟨ds ++ [Nat.digitChar (n % 10)], by rw [hds, List.append_assoc]; rfl,
        by simp, ?_, ?_, ?_⟩
      · intro c hc
        rw [List.mem_append, List.mem_singleton] at hc
        rcases hc with hc | rfl
        · exact hdig c hc
        · exact ⟨n % 10, Nat.mod_lt _ (by omega), rfl⟩
      · intro h
        exfalso
        cases ds with
        | nil => exact hne rfl
        | cons c ds' =>
          simp only [List.cons_append, List.head?_cons] at h
          have := hz (by rw [List.head?_cons, h])
          simp only [List.cons.injEq] at this
          rw [this.1, this.2] at hval
          simp only [List.map_cons, List.map_nil, digitsVal, List.foldl_cons, List.foldl_nil] at hval
          rw [digitChar_byte (by omega)] at hval
          simp only [Nat.zero_mul, Nat.zero_add, UInt8.toNat_ofNat', Nat.add_zero] at hval
          rw [Nat.mod_eq_of_lt (by omega)] at hval
          omega
      · rw [List.map_append, List.map_cons, List.map_nil]
        simp only [digitsVal, List.foldl_append, List.foldl_cons, List.foldl_nil]
        simp only [digitsVal] at hval
        rw [hval, digitChar_byte (Nat.mod_lt _ (by omega))]
        simp only [UInt8.toNat_ofNat']
        rw [Nat.mod_eq_of_lt (by have := Nat.mod_lt n (show 10 > 0 by omega); omega)]
        omega

/-- The UTF-8 of a run of digit characters is the run of their bytes. -/
theorem utf8Encode_digits (ds : List Char)
    (h : ∀ c ∈ ds, ∃ m, m < 10 ∧ c = Nat.digitChar m) :
    ds.flatMap String.utf8EncodeChar = ds.map fun c => UInt8.ofNat c.val.toNat := by
  induction ds with
  | nil => rfl
  | cons c ds ih =>
    rw [List.flatMap_cons, List.map_cons, ih (fun c hc => h c (List.mem_cons_of_mem _ hc))]
    obtain ⟨m, hm, rfl⟩ := h c (List.mem_cons_self ..)
    have : (Nat.digitChar m).val.toNat ≤ 127 := by
      have : m = 0 ∨ m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ m = 6 ∨ m = 7 ∨ m = 8 ∨ m = 9 := by
        omega
      rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simp only [String.utf8EncodeChar, this, ↓reduceIte, List.singleton_append]

/-- **The rendering is a decimal.** -/
theorem repr_isDec (n : Nat) : IsDec (lit (toString n)) n := by
  obtain ⟨ds, hds, hne, hdig, hz, hval⟩ := toDigitsCore_spec (n + 1) n [] (Nat.lt_succ_self n)
  have hlit : lit (toString n) = ds.map fun c => UInt8.ofNat c.val.toNat := by
    show lit (Nat.repr n) = _
    unfold Nat.repr Nat.toDigits
    rw [hds, List.append_nil]
    simp only [lit, String.toUTF8_eq_toByteArray, String.toByteArray_ofList, List.utf8Encode,
      List.data_toByteArray, List.toList_toArray]
    exact utf8Encode_digits ds hdig
  rw [hlit]
  refine ⟨by simpa using hne, ?_, ?_, hval⟩
  · intro b hb
    rw [List.mem_map] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    obtain ⟨m, hm, rfl⟩ := hdig c hc
    rw [digitChar_byte hm]
    simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt8.le_iff_toNat_le,
      UInt8.toNat_ofNat', UInt8.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega
  · intro h
    cases ds with
    | nil => exact absurd rfl hne
    | cons c ds' =>
      simp only [List.map_cons, List.head?_cons, Option.some.injEq] at h
      obtain ⟨m, hm, rfl⟩ := hdig c (List.mem_cons_self ..)
      rw [digitChar_byte hm] at h
      have hm0 : m = 0 := by
        have : (UInt8.ofNat (48 + m)).toNat = (48 : UInt8).toNat := by rw [h]
        simp only [UInt8.toNat_ofNat'] at this
        rw [Nat.mod_eq_of_lt (by omega)] at this
        simp at this
        omega
      subst hm0
      have := hz (by simp)
      rw [this]
      simp only [List.map_cons, List.map_nil]
      rw [digitChar_byte (by omega)]
      rfl

/-! ## The reading -/

/-- A decimal followed by a non-digit is read as its value, and the
rest is the non-digit on. -/
theorem naiveNum_isDec {d : List UInt8} {n : Nat} (hd : IsDec d n) {c : UInt8}
    (hc : isDigit c = false) (r : List UInt8) :
    naiveNum (d ++ c :: r) = some (n, c :: r) := by
  have htake : (d ++ c :: r).takeWhile isDigit = d := by
    rw [List.takeWhile_append_of_pos hd.digits]
    simp [hc]
  have hdrop : (d ++ c :: r).dropWhile isDigit = c :: r := by
    rw [List.dropWhile_append_of_pos hd.digits]
    simp [hc]
  unfold naiveNum
  rw [htake, hdrop]
  have hne : d.isEmpty = false := by
    cases d with
    | nil => exact absurd rfl hd.ne_nil
    | cons _ _ => rfl
  have hlead : (d.head? == some 48 && d.length != 1) = false := by
    by_cases h48 : d.head? = some 48
    · rw [hd.no_leading_zero h48]; decide
    · simp [h48]
  simp only [hne, hlead, Bool.or_self, Bool.false_eq_true, ↓reduceIte, hd.val]

theorem naiveNat_isDec {d : List UInt8} {n : Nat} (hd : IsDec d n) {c : UInt8}
    (hc : isDigit c = false) (r : List UInt8) :
    naiveNat (d ++ c :: r) = .ok n (c :: r) := by
  unfold naiveNat
  rw [naiveNum_isDec hd hc r]

end ConLeche.Frontend
