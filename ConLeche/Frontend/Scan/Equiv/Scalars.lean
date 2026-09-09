module

public import ConLeche.Frontend.Scan.Equiv.Kit

public section

/-!
# The scalar twins (task #261)

One lemma per primitive of `ConLeche/Frontend/Scan/Fast.lean`, each of
the shape `fastX b i = liftRes b i (naiveX (tailAt b i))` — or, for a
primitive that returns a bare position, `fastX b i = (posAt … rest).toUSize`.
Every proof is the fast function's own induction (`fun_induction`),
with `tailAt_of_lt`/`tailAt_of_not_lt` turning the byte at `i` into the
head of the naive input and `usizeStep` turning `i + 1` into the
tail.
-/

namespace ConLeche.Frontend

/-! ## Whitespace and literals -/

theorem skipWs_eq (b : ByteArray) (i : USize) :
    skipWs b i = (posAt i.toNat (tailAt b i) ((tailAt b i).dropWhile isWs)).toUSize := by
  fun_induction skipWs b i with
  | case1 i h hws ih =>
    rw [tailAt_of_lt h, List.dropWhile_cons_of_pos hws, ih]
    congr 1
    have := (List.dropWhile_suffix (l := tailAt b (i + 1)) isWs).length_le
    simp only [posAt, List.length_cons, usizeStep b i h]
    omega
  | case2 i h hws =>
    rw [tailAt_of_lt h, List.dropWhile_cons_of_neg hws]
    simp [posAt]
  | case3 i h =>
    rw [tailAt_of_not_lt h]
    simp [posAt]

theorem matchLit_eq (b : ByteArray) (i : USize) (lit : ByteArray) (k : USize) :
    matchLit b i lit k = (tailAt lit k).isPrefixOf (tailAt b i) := by
  fun_induction matchLit b i lit k with
  | case1 k i hk h ih =>
    rw [tailAt_of_lt hk, tailAt_of_lt h, List.isPrefixOf_cons_cons, ih, BEq.comm]
  | case2 k i hk h =>
    rw [tailAt_of_lt hk, tailAt_of_not_lt h]; rfl
  | case3 k i hk =>
    rw [tailAt_of_not_lt hk]; rfl

/-- `matchLit` against a string literal is `isPrefixOf` against its
bytes. -/
theorem matchLit_lit (b : ByteArray) (i : USize) (s : String)
    (h : s.toUTF8.size < USize.size) :
    matchLit b i s.toUTF8 0 = (lit s).isPrefixOf (tailAt b i) := by
  rw [matchLit_eq, tailAt_zero_of_size_lt h]; rfl

theorem length_lit_true : (lit "true").length = 4 := by rw [lit_eq_toByteArray]; rfl
theorem length_lit_false : (lit "false").length = 5 := by rw [lit_eq_toByteArray]; rfl

theorem length_lit_default : (lit "default\"").length = 8 := by rw [lit_eq_toByteArray]; rfl
theorem length_lit_implicit : (lit "implicit\"").length = 9 := by rw [lit_eq_toByteArray]; rfl
theorem length_lit_strictImplicit : (lit "strictImplicit\"").length = 15 := by
  rw [lit_eq_toByteArray]; rfl
theorem length_lit_instImplicit : (lit "instImplicit\"").length = 13 := by
  rw [lit_eq_toByteArray]; rfl

/-- A bare position (no `liftRes` wrapper): a rest that dropped `m`
bytes of the tail sits at `i + m`. -/
theorem pos_drop_eq (b : ByteArray) (i : USize) (m : Nat) (hm : m ≤ (tailAt b i).length) :
    (posAt i.toNat (tailAt b i) ((tailAt b i).drop m)).toUSize = i + m.toUSize := by
  have h1 := USize.toNat_lt_size i
  have h2 := USize.toNat_lt_size b.usize
  simp only [length_tailAt] at hm
  rw [posAt_drop (by simp only [length_tailAt]; omega), ← toUSize_toNat_add i m (by omega)]

/-- The same, with the head byte of the tail already consumed. -/
theorem pos_cons_drop {b : ByteArray} {i : USize} {a : UInt8} {l : List UInt8} {n : Nat}
    (hT : tailAt b i = a :: l) (hn : n ≤ l.length) :
    (posAt i.toNat (a :: l) (l.drop n)).toUSize = i + (n + 1).toUSize := by
  have h1 : (tailAt b i).drop (n + 1) = l.drop n := by rw [hT]; rfl
  have h2 : n + 1 ≤ (tailAt b i).length := by
    rw [hT]; simp only [List.length_cons]; omega
  rw [← hT, ← h1, pos_drop_eq b i (n + 1) h2]

theorem scanBool_eq (b : ByteArray) (i : USize) :
    scanBool b i = liftRes b i (naiveBool (tailAt b i)) := by
  unfold scanBool naiveBool naiveLit
  rw [matchLit_lit b i "true" (size_toUTF8_lt "true" 4 rfl (by decide)),
      matchLit_lit b i "false" (size_toUTF8_lt "false" 5 rfl (by decide))]
  by_cases ht : (lit "true").isPrefixOf (tailAt b i)
  · have hlen := (List.isPrefixOf_iff_prefix.mp ht).length_le
    simp only [ht, ↓reduceIte]
    rw [liftRes_ok_drop hlen, length_lit_true]; rfl
  · by_cases hf : (lit "false").isPrefixOf (tailAt b i)
    · have hlen := (List.isPrefixOf_iff_prefix.mp hf).length_le
      simp only [ht, hf, Bool.false_eq_true, ↓reduceIte]
      rw [liftRes_ok_drop hlen, length_lit_false]; rfl
    · simp only [ht, hf, Bool.false_eq_true, ↓reduceIte, liftRes, posAt, Nat.sub_self,
        Nat.add_zero]

/-! ## Digits -/

theorem skipDigits_eq (b : ByteArray) (i : USize) :
    skipDigits b i = (posAt i.toNat (tailAt b i) ((tailAt b i).dropWhile isDigit)).toUSize := by
  fun_induction skipDigits b i with
  | case1 i h hd ih =>
    rw [tailAt_of_lt h, List.dropWhile_cons_of_pos hd, ih]
    congr 1
    have := (List.dropWhile_suffix (l := tailAt b (i + 1)) isDigit).length_le
    simp only [posAt, List.length_cons, usizeStep b i h]
    omega
  | case2 i h hd =>
    rw [tailAt_of_lt h, List.dropWhile_cons_of_neg hd]
    simp [posAt]
  | case3 i h =>
    rw [tailAt_of_not_lt h]
    simp [posAt]

theorem readNat_eq (b : ByteArray) (i : USize) (acc : Nat) :
    readNat b i acc =
      ((tailAt b i).takeWhile isDigit).foldl (fun acc d => acc * 10 + (d.toNat - 48)) acc := by
  fun_induction readNat b i acc with
  | case1 i acc h c hd ih =>
    rw [tailAt_of_lt h, List.takeWhile_cons_of_pos hd, List.foldl_cons, ih]
  | case2 i acc h c hd =>
    rw [tailAt_of_lt h, List.takeWhile_cons_of_neg hd, List.foldl_nil]
  | case3 i acc h =>
    rw [tailAt_of_not_lt h, List.takeWhile_nil, List.foldl_nil]

/-- `Nat.toUSize` is a section of `USize.toNat` below `USize.size`. -/
theorem toNat_toUSize {n : Nat} (h : n < USize.size) : n.toUSize.toNat = n := by
  simp [Nat.toUSize, USize.toNat_ofNat', Nat.mod_eq_of_lt h]

/-- The digit run at `i` ends `ds.length` bytes further on. -/
theorem skipDigits_toNat (b : ByteArray) (i : USize) :
    (skipDigits b i).toNat = i.toNat + ((tailAt b i).takeWhile isDigit).length := by
  have hsplit : ((tailAt b i).takeWhile isDigit).length
      + ((tailAt b i).dropWhile isDigit).length = (tailAt b i).length := by
    rw [← List.length_append, List.takeWhile_append_dropWhile]
  have h1 := USize.toNat_lt_size i
  have h2 := USize.toNat_lt_size b.usize
  have h3 : (tailAt b i).length = b.usize.toNat - i.toNat := length_tailAt b i
  rw [skipDigits_eq, toNat_toUSize (by simp only [posAt]; omega)]
  simp only [posAt]
  omega

theorem le_skipDigits (b : ByteArray) (i : USize) : i ≤ skipDigits b i := by
  rw [USize.le_iff_toNat_le, skipDigits_toNat]; omega

/-- One machine-word accumulation step over a digit, and the bound it
leaves for the rest of the run: `acc * 10 + d` does not wrap while the
whole `k+1`-digit tail still fits. -/
theorem digitStep (acc : UInt64) (c : UInt8) (hdig : isDigit c = true) (k : Nat)
    (hb : acc.toNat * 10 ^ (k + 1) + (10 ^ (k + 1) - 1) < 2 ^ 64) :
    (acc * 10 + (c - 48).toUInt64).toNat = acc.toNat * 10 + (c.toNat - 48) ∧
      (acc * 10 + (c - 48).toUInt64).toNat * 10 ^ k + (10 ^ k - 1) < 2 ^ 64 := by
  simp only [isDigit, Bool.and_eq_true, decide_eq_true_eq] at hdig
  have h48 : (48 : UInt8).toNat = 48 := by decide
  have h57 : (57 : UInt8).toNat = 57 := by decide
  have hlo : 48 ≤ c.toNat := by rw [← h48]; exact UInt8.le_iff_toNat_le.mp hdig.1
  have hhi : c.toNat ≤ 57 := by rw [← h57]; exact UInt8.le_iff_toNat_le.mp hdig.2
  have hd : (c - 48).toUInt64.toNat = c.toNat - 48 := by
    rw [UInt8.toNat_toUInt64, UInt8.toNat_sub_of_le c 48 hdig.1, h48]
  have hP : 1 ≤ (10 : Nat) ^ k := Nat.one_le_pow k 10 (by decide)
  rw [Nat.pow_succ] at hb
  have h10P : (10 : Nat) ≤ 10 ^ k * 10 := by omega
  have hmul : acc.toNat * 10 ≤ acc.toNat * (10 ^ k * 10) := Nat.mul_le_mul (Nat.le_refl _) h10P
  have h10 : (10 : UInt64).toNat = 10 := by decide
  have hb1 : acc.toNat * 10 < 2 ^ 64 := by omega
  have hb2 : acc.toNat * 10 + (c.toNat - 48) < 2 ^ 64 := by omega
  have haccval : (acc * 10 + (c - 48).toUInt64).toNat = acc.toNat * 10 + (c.toNat - 48) := by
    rw [UInt64.toNat_add, UInt64.toNat_mul, hd, h10, Nat.mod_eq_of_lt hb1, Nat.mod_eq_of_lt hb2]
  refine ⟨haccval, ?_⟩
  rw [haccval]
  have hexp : (acc.toNat * 10 + (c.toNat - 48)) * 10 ^ k
      = acc.toNat * (10 ^ k * 10) + (c.toNat - 48) * 10 ^ k := by
    rw [Nat.add_mul, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ k)]
  have hle : (c.toNat - 48) * 10 ^ k ≤ 9 * 10 ^ k := Nat.mul_le_mul (by omega) (Nat.le_refl _)
  omega

/-- The machine-word accumulation over the digit run at `i` is the
naive fold, as long as the run cannot overflow. -/
theorem readNat64_eq (b : ByteArray) (i e : USize) (acc : UInt64) :
    skipDigits b i = e →
    acc.toNat * 10 ^ ((tailAt b i).takeWhile isDigit).length
        + (10 ^ ((tailAt b i).takeWhile isDigit).length - 1) < 2 ^ 64 →
    (readNat64 b i e acc).toNat
      = ((tailAt b i).takeWhile isDigit).foldl (fun a d => a * 10 + (d.toNat - 48)) acc.toNat := by
  fun_induction readNat64 b i e acc with
  | case1 i acc h hie ih =>
    intro he hb
    have hT := tailAt_of_lt h
    have hsd := skipDigits_toNat b i
    have hstep := usizeStep b i h
    have hdig : isDigit (b.uget i (usizeInBounds b i h)) = true := by
      cases hnd : isDigit (b.uget i (usizeInBounds b i h)) with
      | true => rfl
      | false =>
        exfalso
        have hnil : (tailAt b i).takeWhile isDigit = [] := by
          rw [hT, List.takeWhile_cons_of_neg (by simp [hnd])]
        rw [hnil, List.length_nil, Nat.add_zero, he] at hsd
        exact absurd (USize.lt_iff_toNat_lt.mp hie) (by omega)
    have hds : (tailAt b i).takeWhile isDigit
        = b.uget i (usizeInBounds b i h) :: (tailAt b (i + 1)).takeWhile isDigit := by
      rw [hT, List.takeWhile_cons_of_pos hdig]
    have hsd' := skipDigits_toNat b (i + 1)
    have hev : e.toNat = i.toNat + ((tailAt b i).takeWhile isDigit).length := by rw [← he, hsd]
    have he' : skipDigits b (i + 1) = e := by
      apply USize.toNat_inj.mp
      rw [hsd', hev, hds]
      simp only [List.length_cons]
      omega
    rw [hds] at hb
    simp only [List.length_cons] at hb
    obtain ⟨haccval, hb'⟩ := digitStep acc (b.uget i (usizeInBounds b i h)) hdig
      ((tailAt b (i + 1)).takeWhile isDigit).length hb
    rw [ih he' hb', haccval, hds, List.foldl_cons]
  | case2 i acc h hie =>
    intro he _hb
    have hsd := skipDigits_toNat b i
    have hnil : (tailAt b i).takeWhile isDigit = [] := by
      apply List.eq_nil_of_length_eq_zero
      have hev : e.toNat = i.toNat + ((tailAt b i).takeWhile isDigit).length := by rw [← he, hsd]
      have h2 : ¬ i.toNat < e.toNat := fun hx => hie (USize.lt_iff_toNat_lt.mpr hx)
      omega
    rw [hnil, List.foldl_nil]
  | case3 i acc h =>
    intro _he _hb
    rw [tailAt_of_not_lt h, List.takeWhile_nil, List.foldl_nil]

/-- `readNatAt` over the digit run at `i` is its value: the machine-word
path (at most 18 digits, which cannot overflow) and the `Nat` path agree
with the naive fold. -/
theorem readNatAt_eq (b : ByteArray) (i : USize) :
    readNatAt b i (skipDigits b i) = digitsVal ((tailAt b i).takeWhile isDigit) := by
  unfold readNatAt digitsVal
  split
  · rename_i hle
    have hi := le_skipDigits b i
    have hsd := skipDigits_toNat b i
    have h1 : (skipDigits b i - i).toNat = (skipDigits b i).toNat - i.toNat :=
      USize.toNat_sub_of_le _ _ hi
    have h2 : (skipDigits b i - i).toNat ≤ (18 : USize).toNat := USize.le_iff_toNat_le.mp hle
    have h3 : ((18 : USize)).toNat = 18 := by simp
    have hk : ((tailAt b i).takeWhile isDigit).length ≤ 18 := by omega
    have h0 : (0 : UInt64).toNat = 0 := by decide
    have hmono : (10 : Nat) ^ ((tailAt b i).takeWhile isDigit).length ≤ 10 ^ 18 :=
      Nat.pow_le_pow_right (by decide) hk
    have h18 : (10 : Nat) ^ 18 < 2 ^ 64 := by decide
    have hbound : (0 : UInt64).toNat * 10 ^ ((tailAt b i).takeWhile isDigit).length
        + (10 ^ ((tailAt b i).takeWhile isDigit).length - 1) < 2 ^ 64 := by
      rw [h0, Nat.zero_mul]; omega
    rw [readNat64_eq b i (skipDigits b i) 0 rfl hbound, h0]
  · exact readNat_eq b i 0

theorem skipDigits_ne_self (b : ByteArray) (i : USize)
    (h : (tailAt b i).takeWhile isDigit ≠ []) : skipDigits b i ≠ i := by
  intro hx
  have hsd := skipDigits_toNat b i
  rw [hx] at hsd
  exact h (List.eq_nil_of_length_eq_zero (by omega))

/-- `numEnd` is JSON's leading-zero rule read off the digit run: the
run is empty, or it starts with `0` and is longer than one byte. -/
theorem numEnd_eq (b : ByteArray) (i : USize) :
    numEnd b i =
      if ((tailAt b i).takeWhile isDigit).isEmpty
          || (((tailAt b i).takeWhile isDigit).head? == some 48
              && ((tailAt b i).takeWhile isDigit).length != 1) then i
      else skipDigits b i := by
  have hsd := skipDigits_toNat b i
  cases hds : (tailAt b i).takeWhile isDigit with
  | nil =>
    have hei : skipDigits b i = i := by
      apply USize.toNat_inj.mp; rw [hsd, hds]; simp
    unfold numEnd
    simp [hei]
  | cons d ds' =>
    have hne : tailAt b i ≠ [] := by
      intro hnil; rw [hnil] at hds; simp at hds
    have hlt : i < b.usize := by
      rw [USize.lt_iff_toNat_lt]
      have h1 := length_tailAt b i
      have h2 : (tailAt b i).length ≠ 0 := fun hx => hne (List.eq_nil_of_length_eq_zero hx)
      omega
    have hT := tailAt_of_lt hlt
    have hhead : b.uget i (usizeInBounds b i hlt) = d := by
      rw [hT] at hds
      by_cases hdg : isDigit (b.uget i (usizeInBounds b i hlt)) = true
      · rw [List.takeWhile_cons_of_pos hdg] at hds
        simp only [List.cons.injEq] at hds
        exact hds.1
      · rw [List.takeWhile_cons_of_neg hdg] at hds
        simp at hds
    have hstep := usizeStep b i hlt
    have hlen : (skipDigits b i).toNat = i.toNat + (ds'.length + 1) := by
      rw [hsd, hds]; simp
    have hnei : skipDigits b i ≠ i := by
      intro hx; rw [hx] at hlen; omega
    unfold numEnd
    simp only [List.isEmpty_cons, List.head?_cons, Bool.false_or, List.length_cons]
    rw [byteAt_eq, hT, List.headD_cons, hhead]
    by_cases hone : ds'.length = 0
    · have heq1 : skipDigits b i = i + 1 := by
        apply USize.toNat_inj.mp; rw [hlen, hstep]; omega
      simp [heq1, hone]
    · have hne1 : skipDigits b i ≠ i + 1 := by
        intro hx
        have hc := congrArg USize.toNat hx
        rw [hlen, hstep] at hc; omega
      simp [hne1, hone, hnei]

theorem numEnd_eq_self_iff (b : ByteArray) (i : USize) :
    numEnd b i = i ↔ naiveNum (tailAt b i) = none := by
  rw [numEnd_eq]
  unfold naiveNum
  dsimp only
  by_cases hC : (((tailAt b i).takeWhile isDigit).isEmpty
      || (((tailAt b i).takeWhile isDigit).head? == some 48
          && ((tailAt b i).takeWhile isDigit).length != 1)) = true
  · simp only [hC, ↓reduceIte]
  · have hnil : (tailAt b i).takeWhile isDigit ≠ [] := by
      intro hx; rw [hx] at hC; simp at hC
    simp only [hC, Bool.false_eq_true, ↓reduceIte]
    simp [skipDigits_ne_self b i hnil]

theorem numEnd_of_some {b : ByteArray} {i : USize} {n : Nat} {r : List UInt8}
    (h : naiveNum (tailAt b i) = some (n, r)) :
    numEnd b i = (posAt i.toNat (tailAt b i) r).toUSize ∧ readNatAt b i (numEnd b i) = n := by
  unfold naiveNum at h
  dsimp only at h
  split at h
  · exact absurd h (by simp)
  · rename_i hC
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    have hnum : numEnd b i = skipDigits b i := by rw [numEnd_eq, if_neg hC]
    refine ⟨?_, ?_⟩
    · rw [hnum, skipDigits_eq, ← h.2]
    · rw [hnum, readNatAt_eq, h.1]

/-! ## Strings -/

theorem strClose_eq (b : ByteArray) (j : USize) :
    strClose b j = match naiveStrBody (tailAt b j) with
      | none => 0
      | some (body, _) => (j.toNat + body.length).toUSize := by
  fun_induction strClose b j with
  | case1 j h c hc =>
    have hc' : (b.uget j (usizeInBounds b j h) == 34) = true := hc
    rw [tailAt_of_lt h, naiveStrBody.eq_def]
    simp only [hc', ↓reduceIte, List.length_nil, Nat.add_zero]
    exact USize.ofNat_toNat.symm
  | case2 j h c hc hb h2 ih =>
    have hc' : ¬ (b.uget j (usizeInBounds b j h) == 34) = true := hc
    have hb' : (b.uget j (usizeInBounds b j h) == 92) = true := hb
    have hstep := usizeStep b j h
    have hstep2 := usizeStep b (j + 1) h2
    rw [tailAt_of_lt h, tailAt_of_lt h2, naiveStrBody.eq_def]
    simp only [hc', hb', ↓reduceIte, Bool.false_eq_true]
    cases hs : naiveStrBody (tailAt b (j + 1 + 1)) with
    | none => rw [ih, hs]; simp only [Option.map_none]
    | some p =>
      obtain ⟨body, r⟩ := p
      rw [ih, hs]
      simp only [Option.map_some, List.length_cons]
      congr 1
      omega
  | case3 j h c hc hb h2 =>
    have hc' : ¬ (b.uget j (usizeInBounds b j h) == 34) = true := hc
    have hb' : (b.uget j (usizeInBounds b j h) == 92) = true := hb
    rw [tailAt_of_lt h, tailAt_of_not_lt h2, naiveStrBody.eq_def]
    simp only [hc', hb', ↓reduceIte, Bool.false_eq_true]
  | case4 j h c hc hb hlt =>
    have hc' : ¬ (b.uget j (usizeInBounds b j h) == 34) = true := hc
    have hb' : ¬ (b.uget j (usizeInBounds b j h) == 92) = true := hb
    have hlt' : b.uget j (usizeInBounds b j h) < 32 := hlt
    rw [tailAt_of_lt h, naiveStrBody.eq_def]
    simp only [hc', hb', hlt', ↓reduceIte, Bool.false_eq_true]
  | case5 j h c hc hb hlt ih =>
    have hc' : ¬ (b.uget j (usizeInBounds b j h) == 34) = true := hc
    have hb' : ¬ (b.uget j (usizeInBounds b j h) == 92) = true := hb
    have hlt' : ¬ b.uget j (usizeInBounds b j h) < 32 := hlt
    have hstep := usizeStep b j h
    rw [tailAt_of_lt h, naiveStrBody.eq_def]
    simp only [hc', hb', hlt', ↓reduceIte, Bool.false_eq_true]
    cases hs : naiveStrBody (tailAt b (j + 1)) with
    | none => rw [ih, hs]; simp only [Option.map_none]
    | some p =>
      obtain ⟨body, r⟩ := p
      rw [ih, hs]
      simp only [Option.map_some, List.length_cons]
      congr 1
      omega
  | case6 j h =>
    rw [tailAt_of_not_lt h, naiveStrBody.eq_def]

theorem hasEscape_eq (b : ByteArray) (j e : USize) :
    hasEscape b j e = ((tailAt b j).take (e.toNat - j.toNat)).contains 92 := by
  fun_induction hasEscape b j e with
  | case1 j h hje hc =>
    have hc' : b.uget j (usizeInBounds b j h) = 92 := by simpa using hc
    have hlt : j.toNat < e.toNat := USize.lt_iff_toNat_lt.mp hje
    have hs : e.toNat - j.toNat = (e.toNat - j.toNat - 1) + 1 := by omega
    rw [tailAt_of_lt h, hs, List.take_succ_cons, hc']
    simp
  | case2 j h hje hc ih =>
    have hc' : ¬ b.uget j (usizeInBounds b j h) = 92 := by simpa using hc
    have hstep := usizeStep b j h
    have hlt : j.toNat < e.toNat := USize.lt_iff_toNat_lt.mp hje
    have hs : e.toNat - j.toNat = (e.toNat - (j + 1).toNat) + 1 := by omega
    rw [tailAt_of_lt h, hs, List.take_succ_cons, ih]
    simp [Ne.symm hc']
  | case3 j h hje =>
    have : e.toNat ≤ j.toNat := Nat.le_of_not_lt fun h' => hje (USize.lt_iff_toNat_lt.mpr h')
    have : e.toNat - j.toNat = 0 := by omega
    rw [this]
    simp
  | case4 j h =>
    rw [tailAt_of_not_lt h]
    simp

/-- The slice the no-escape path validates is the naive body. -/
theorem extract_eq (b : ByteArray) (s e : USize) (hs : s.toNat ≤ e.toNat)
    (he : e.toNat ≤ (bytes b).length) :
    b.extract s.toNat e.toNat = ⟨⟨(tailAt b s).take (e.toNat - s.toNat)⟩⟩ := by
  apply ByteArray.ext
  apply Array.ext'
  rw [ByteArray.data_extract, Array.toList_extract]
  show (b.data.toList.drop s.toNat).take (e.toNat - s.toNat) = _
  simp only [length_bytes] at he
  simp only [tailAt, bytes, List.drop_take, List.take_take]
  congr 1
  omega

/-! ### Shifting the window to `i` -/

/-- `USize` is a ring: a step commutes with the shift, with no
side condition. -/
theorem usize_sub_add (x y : USize) : (x + 1) - y = (x - y) + 1 := by
  apply USize.toBitVec_inj.mp
  simp only [USize.toBitVec_add, USize.toBitVec_sub, USize.toBitVec_ofNat,
    BitVec.sub_eq_add_neg]
  rw [BitVec.add_assoc, BitVec.add_comm (1#System.Platform.numBits), ← BitVec.add_assoc]

/-- The tail from `i`, seen as an array, has exactly those bytes. -/
theorem bytes_tailAt (b : ByteArray) (i : USize) :
    bytes (⟨⟨tailAt b i⟩⟩ : ByteArray) = tailAt b i := by
  have h2 : (tailAt b i).length ≤ b.usize.toNat := by simp only [length_tailAt]; omega
  have h3 := USize.toNat_lt_size b.usize
  simp only [bytes, toNat_usize]
  show List.take (((tailAt b i).length) % USize.size) (tailAt b i) = tailAt b i
  rw [Nat.mod_eq_of_lt (by omega), List.take_length]

theorem usize_tailAt (b : ByteArray) (i : USize) :
    (⟨⟨tailAt b i⟩⟩ : ByteArray).usize.toNat = b.usize.toNat - i.toNat := by
  have h := length_bytes (⟨⟨tailAt b i⟩⟩ : ByteArray)
  rw [bytes_tailAt] at h
  rw [← h, length_tailAt]

theorem tailAt_shift (b : ByteArray) (i p : USize) (h : i.toNat ≤ p.toNat) :
    tailAt (⟨⟨tailAt b i⟩⟩ : ByteArray) (p - i) = tailAt b p := by
  have hsub : (p - i).toNat = p.toNat - i.toNat :=
    USize.toNat_sub_of_le p i (USize.le_iff_toNat_le.mpr h)
  show (bytes (⟨⟨tailAt b i⟩⟩ : ByteArray)).drop (p - i).toNat = tailAt b p
  rw [bytes_tailAt, hsub]
  show ((bytes b).drop i.toNat).drop (p.toNat - i.toNat) = (bytes b).drop p.toNat
  rw [List.drop_drop]
  congr 1
  omega

theorem byteAt_shift (b : ByteArray) (i p : USize) (h : i.toNat ≤ p.toNat) :
    byteAt (⟨⟨tailAt b i⟩⟩ : ByteArray) (p - i) = byteAt b p := by
  rw [byteAt_eq, byteAt_eq, tailAt_shift b i p h]

theorem lt_usize_shift (b : ByteArray) (i p : USize) (h : i.toNat ≤ p.toNat) :
    (p - i) < (⟨⟨tailAt b i⟩⟩ : ByteArray).usize ↔ p < b.usize := by
  rw [USize.lt_iff_toNat_lt, USize.lt_iff_toNat_lt, usize_tailAt,
      USize.toNat_sub_of_le p i (USize.le_iff_toNat_le.mpr h)]
  omega

theorem lt_shift (i p q : USize) (hp : i.toNat ≤ p.toNat) (hq : i.toNat ≤ q.toNat) :
    (p - i) < (q - i) ↔ p < q := by
  rw [USize.lt_iff_toNat_lt, USize.lt_iff_toNat_lt,
      USize.toNat_sub_of_le p i (USize.le_iff_toNat_le.mpr hp),
      USize.toNat_sub_of_le q i (USize.le_iff_toNat_le.mpr hq)]
  omega

/-- A byte read past the end is `0`, so a non-zero read is in range. -/
theorem lt_usize_of_byteAt_ne_zero {b : ByteArray} {p : USize} (h : byteAt b p ≠ 0) :
    p < b.usize := by
  unfold byteAt at h
  split at h
  · assumption
  · exact absurd rfl h

theorem uget_eq_byteAt {b : ByteArray} {p : USize} (h : p < b.usize) :
    b.uget p (usizeInBounds b p h) = byteAt b p := by
  unfold byteAt
  rw [dif_pos h]

/-- A `USize` step that does not wrap. -/
theorem usize_step_of_lt {p : USize} (h : p.toNat + 1 < USize.size) :
    (p + 1).toNat = p.toNat + 1 := by
  simp [USize.toNat_add, Nat.mod_eq_of_lt h]

theorem hexVal_ne_zero {c : UInt8} {v : UInt32} (h : hexVal c = some v) : c ≠ 0 := by
  intro h0; rw [h0] at h; simp [hexVal] at h

theorem step_of_hexVal {b : ByteArray} {p : USize} {v : UInt32}
    (h : hexVal (byteAt b p) = some v) :
    p.toNat < b.usize.toNat ∧ (p + 1).toNat = p.toNat + 1 := by
  have hlt := lt_usize_of_byteAt_ne_zero (hexVal_ne_zero h)
  exact ⟨USize.lt_iff_toNat_lt.mp hlt, usizeStep b p hlt⟩

/-- Four hexadecimal digits read: the four positions are in range and
none of the steps wraps. -/
theorem hex4_range {b : ByteArray} {p : USize} {v : UInt32} (h : hex4 b p = some v) :
    p.toNat + 3 < b.usize.toNat ∧ (p + 1).toNat = p.toNat + 1 ∧
      (p + 1 + 1).toNat = p.toNat + 2 ∧ (p + 1 + 1 + 1).toNat = p.toNat + 3 := by
  unfold hex4 at h
  cases h1 : hexVal (byteAt b p) with
  | none => rw [h1] at h; simp at h
  | some a =>
    obtain ⟨q1, s1⟩ := step_of_hexVal h1
    cases h2 : hexVal (byteAt b (p + 1)) with
    | none => rw [h1, h2] at h; simp at h
    | some a2 =>
      obtain ⟨q2, s2⟩ := step_of_hexVal h2
      cases h3 : hexVal (byteAt b (p + 1 + 1)) with
      | none => rw [h1, h2, h3] at h; simp at h
      | some a3 =>
        obtain ⟨q3, s3⟩ := step_of_hexVal h3
        cases h4 : hexVal (byteAt b (p + 1 + 1 + 1)) with
        | none => rw [h1, h2, h3, h4] at h; simp at h
        | some a4 =>
          obtain ⟨q4, _⟩ := step_of_hexVal h4
          exact ⟨by omega, s1, by omega, by omega⟩

theorem hex3_range {b : ByteArray} {p : USize} {v : UInt32} (h : hex3 b p = some v) :
    p.toNat + 2 < b.usize.toNat ∧ (p + 1).toNat = p.toNat + 1 ∧
      (p + 1 + 1).toNat = p.toNat + 2 := by
  unfold hex3 at h
  cases h1 : hexVal (byteAt b p) with
  | none => rw [h1] at h; simp at h
  | some a =>
    obtain ⟨q1, s1⟩ := step_of_hexVal h1
    cases h2 : hexVal (byteAt b (p + 1)) with
    | none => rw [h1, h2] at h; simp at h
    | some a2 =>
      obtain ⟨q2, s2⟩ := step_of_hexVal h2
      cases h3 : hexVal (byteAt b (p + 1 + 1)) with
      | none => rw [h1, h2, h3] at h; simp at h
      | some a3 =>
        obtain ⟨q3, _⟩ := step_of_hexVal h3
        exact ⟨by omega, s1, by omega⟩

theorem hex4_shift (b : ByteArray) (i p : USize) (hip : i.toNat ≤ p.toNat) :
    hex4 (⟨⟨tailAt b i⟩⟩ : ByteArray) (p - i) = hex4 b p := by
  unfold hex4
  rw [byteAt_shift b i p hip]
  cases h1 : hexVal (byteAt b p) with
  | none => simp
  | some a =>
    obtain ⟨q1, s1⟩ := step_of_hexVal h1
    rw [← usize_sub_add p i, byteAt_shift b i (p + 1) (by omega)]
    cases h2 : hexVal (byteAt b (p + 1)) with
    | none => simp
    | some a2 =>
      obtain ⟨q2, s2⟩ := step_of_hexVal h2
      rw [← usize_sub_add (p + 1) i, byteAt_shift b i (p + 1 + 1) (by omega)]
      cases h3 : hexVal (byteAt b (p + 1 + 1)) with
      | none => simp
      | some a3 =>
        obtain ⟨q3, s3⟩ := step_of_hexVal h3
        rw [← usize_sub_add (p + 1 + 1) i, byteAt_shift b i (p + 1 + 1 + 1) (by omega)]

theorem hex3_shift (b : ByteArray) (i p : USize) (hip : i.toNat ≤ p.toNat) :
    hex3 (⟨⟨tailAt b i⟩⟩ : ByteArray) (p - i) = hex3 b p := by
  unfold hex3
  rw [byteAt_shift b i p hip]
  cases h1 : hexVal (byteAt b p) with
  | none => simp
  | some a =>
    obtain ⟨q1, s1⟩ := step_of_hexVal h1
    rw [← usize_sub_add p i, byteAt_shift b i (p + 1) (by omega)]
    cases h2 : hexVal (byteAt b (p + 1)) with
    | none => simp
    | some a2 =>
      obtain ⟨q2, s2⟩ := step_of_hexVal h2
      rw [← usize_sub_add (p + 1) i, byteAt_shift b i (p + 1 + 1) (by omega)]

/-- The surrogate-continuation lookahead, and the three hexadecimal
digits behind it, shift together. -/
theorem cont_hex3_shift (b : ByteArray) (i p : USize) (hip : i.toNat ≤ p.toNat) :
    (if (byteAt (⟨⟨tailAt b i⟩⟩ : ByteArray) (p - i) == 92 &&
          byteAt (⟨⟨tailAt b i⟩⟩ : ByteArray) ((p + 1) - i) == 117 &&
          (byteAt (⟨⟨tailAt b i⟩⟩ : ByteArray) ((p + 1 + 1) - i) == 100 ||
            byteAt (⟨⟨tailAt b i⟩⟩ : ByteArray) ((p + 1 + 1) - i) == 68))
        then hex3 (⟨⟨tailAt b i⟩⟩ : ByteArray) ((p + 1 + 1 + 1) - i) else none)
      = (if (byteAt b p == 92 && byteAt b (p + 1) == 117 &&
              (byteAt b (p + 1 + 1) == 100 || byteAt b (p + 1 + 1) == 68))
        then hex3 b (p + 1 + 1 + 1) else none) := by
  rw [byteAt_shift b i p hip]
  by_cases h1 : (byteAt b p == 92) = true
  · have hs1 : (p + 1).toNat = p.toNat + 1 ∧ p.toNat < b.usize.toNat := by
      have hne : byteAt b p ≠ 0 := by
        have : byteAt b p = 92 := by simpa using h1
        rw [this]; decide
      have hlt := lt_usize_of_byteAt_ne_zero hne
      exact ⟨usizeStep b p hlt, USize.lt_iff_toNat_lt.mp hlt⟩
    rw [byteAt_shift b i (p + 1) (by omega)]
    by_cases h2 : (byteAt b (p + 1) == 117) = true
    · have hs2 : (p + 1 + 1).toNat = (p + 1).toNat + 1 := by
        have hne : byteAt b (p + 1) ≠ 0 := by
          have : byteAt b (p + 1) = 117 := by simpa using h2
          rw [this]; decide
        exact usizeStep b (p + 1) (lt_usize_of_byteAt_ne_zero hne)
      rw [byteAt_shift b i (p + 1 + 1) (by omega)]
      by_cases h3 : (byteAt b (p + 1 + 1) == 100 || byteAt b (p + 1 + 1) == 68) = true
      · have hs3 : (p + 1 + 1 + 1).toNat = (p + 1 + 1).toNat + 1 := by
          have hne : byteAt b (p + 1 + 1) ≠ 0 := by
            rcases Bool.or_eq_true_iff.mp h3 with hx | hx
            · have : byteAt b (p + 1 + 1) = 100 := by simpa using hx
              rw [this]; decide
            · have : byteAt b (p + 1 + 1) = 68 := by simpa using hx
              rw [this]; decide
          exact usizeStep b (p + 1 + 1) (lt_usize_of_byteAt_ne_zero hne)
        rw [if_pos (by simp [h1, h2, h3]), if_pos (by simp [h1, h2, h3]),
            hex3_shift b i (p + 1 + 1 + 1) (by omega)]
      · simp [h3]
    · simp [h2]
  · simp [h1]

/-- The position six bytes past a `\uXXXX` escape does not wrap. -/
theorem j6_facts {b : ByteArray} {j : USize} {v : UInt32} (h : j < b.usize)
    (hd : byteAt b (j + 1) = 117) (h4 : hex4 b (j + 1 + 1) = some v) :
    (j + 1 + 1 + 1 + 1 + 1 + 1).toNat = j.toNat + 6 ∧ j.toNat + 5 < b.usize.toNat := by
  have hjs := usizeStep b j h
  have hlt1 : (j + 1) < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hd]; decide)
  have hjs2 := usizeStep b (j + 1) hlt1
  have hbl := USize.toNat_lt_size b.usize
  obtain ⟨q, s1, s2, s3⟩ := hex4_range h4
  have hs6 : (j + 1 + 1 + 1 + 1 + 1 + 1).toNat = (j + 1 + 1 + 1 + 1 + 1).toNat + 1 :=
    usize_step_of_lt (by omega)
  exact ⟨by omega, by omega⟩

/-- Twelve bytes past a surrogate pair: the step does not wrap. -/
theorem j12_facts {b : ByteArray} {p : USize} {v2 : UInt32}
    (hm : (if (byteAt b p == 92 && byteAt b (p + 1) == 117 &&
              (byteAt b (p + 1 + 1) == 100 || byteAt b (p + 1 + 1) == 68))
           then hex3 b (p + 1 + 1 + 1) else none) = some v2) :
    (p + 1 + 1 + 1 + 1 + 1 + 1).toNat = p.toNat + 6 := by
  split at hm
  · rename_i hcont
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hcont
    obtain ⟨⟨h92, h117⟩, h100⟩ := hcont
    have s1 := usizeStep b p (lt_usize_of_byteAt_ne_zero (by rw [h92]; decide))
    have s2 := usizeStep b (p + 1) (lt_usize_of_byteAt_ne_zero (by rw [h117]; decide))
    have s3 := usizeStep b (p + 1 + 1) (lt_usize_of_byteAt_ne_zero (by
      rcases h100 with hx | hx <;> rw [hx] <;> decide))
    obtain ⟨q, t1, t2⟩ := hex3_range hm
    have hbl := USize.toNat_lt_size b.usize
    have s6 : (p + 1 + 1 + 1 + 1 + 1 + 1).toNat = (p + 1 + 1 + 1 + 1 + 1).toNat + 1 :=
      usize_step_of_lt (by omega)
    omega
  · simp at hm

/-- The escape decoder reads only bytes at or after `j ≥ i`, so it
computes the same on the tail from `i` with the positions shifted. -/
theorem unescape_shift (b : ByteArray) (i j e : USize) (acc : ByteArray)
    (hij : i.toNat ≤ j.toNat) (hie : i.toNat ≤ e.toNat) :
    unescape b j e acc = unescape ⟨⟨tailAt b i⟩⟩ (j - i) (e - i) acc := by
  revert hij
  fun_induction unescape b j e acc with
  | case1 j acc h hje cb hc hjj ih =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hD : (j - i) < (j + 1) - i := (lt_shift i j (j + 1) hij hjq).mpr hjj
    simp only [cb, uget_eq_byteAt h] at hc ih ⊢
    rw [ih hjq]
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc,
      ← usize_sub_add j i, dif_pos hD, ↓reduceIte]
  | case2 j acc h hje cb hc hjj =>
    intro hij
    have hjs := usizeStep b j h
    exact absurd (USize.lt_iff_toNat_lt.mpr (by omega)) hjj
  | case17 j acc h hje =>
    intro hij
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB : ¬ ((j - i) < (e - i)) := fun hx => hje ((lt_shift i j e hij hie).mp hx)
    conv => rhs; rw [unescape.eq_def]
    simp only [dif_pos hA, if_neg hB]
  | case18 j acc h =>
    intro hij
    have hA : ¬ ((j - i) < (⟨⟨tailAt b i⟩⟩ : ByteArray).usize) :=
      fun hx => h ((lt_usize_shift b i j hij).mp hx)
    conv => rhs; rw [unescape.eq_def]
    simp only [dif_neg hA]
  | case3 j acc h hje cb hc d simple v2 hs j' hjj ih =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hc2 : (byteAt b j != 92) = false := by
      simp only [cb, uget_eq_byteAt h] at hc; simpa using hc
    have hjj2 : j.toNat < (j + 1 + 1).toNat := USize.lt_iff_toNat_lt.mp hjj
    have hq2 : i.toNat ≤ (j + 1 + 1).toNat := by omega
    have hD : (j - i) < (j + 1 + 1) - i := (lt_shift i j (j + 1 + 1) hij hq2).mpr hjj
    simp only [simple, d, dite_eq_ite] at hs
    simp only [j'] at ih ⊢
    rw [ih hq2]
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc2,
      Bool.false_eq_true, ↓reduceIte, ← usize_sub_add j i, byteAt_shift b i (j + 1) hjq,
      hs, ← usize_sub_add (j + 1) i, dif_pos hD]
  | case4 j acc h hje cb hc d simple v2 hs j' hjj =>
    intro hij
    exfalso
    have hjs := usizeStep b j h
    have hib : j.toNat < b.usize.toNat := USize.lt_iff_toNat_lt.mp h
    have hbl := USize.toNat_lt_size b.usize
    have hj1l := USize.toNat_lt_size (j + 1)
    have hjj' : ¬ j.toNat < (j + 1 + 1).toNat := fun hx => hjj (USize.lt_iff_toNat_lt.mpr hx)
    by_cases hcase : j.toNat + 2 < USize.size
    · have h2 : (j + 1 + 1).toNat = (j + 1).toNat + 1 := usize_step_of_lt (by omega)
      omega
    · have hnlt : ¬ (j + 1) < b.usize := by rw [USize.lt_iff_toNat_lt, hjs]; omega
      have hd0 : byteAt b (j + 1) = 0 := by unfold byteAt; rw [dif_neg hnlt]
      simp [simple, d, hd0] at hs
  | case5 j acc h hje cb hc d simple hs hd117 =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hc2 : (byteAt b j != 92) = false := by
      simp only [cb, uget_eq_byteAt h] at hc; simpa using hc
    simp only [simple, d, dite_eq_ite] at hs
    simp only [d] at hd117
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc2,
      Bool.false_eq_true, ↓reduceIte, ← usize_sub_add j i, byteAt_shift b i (j + 1) hjq,
      hs, hd117]
  | case6 j acc h hje cb hc d simple hs hd117 h4 =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hc2 : (byteAt b j != 92) = false := by
      simp only [cb, uget_eq_byteAt h] at hc; simpa using hc
    simp only [simple, d, dite_eq_ite] at hs
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    have hlt1 : (j + 1) < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hd]; decide)
    have hjs2 : (j + 1 + 1).toNat = (j + 1).toNat + 1 := usizeStep b (j + 1) hlt1
    have hq2 : i.toNat ≤ (j + 1 + 1).toNat := by omega
    have hd2 : (byteAt b (j + 1) != 117) = false := by simp [hd]
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc2,
      Bool.false_eq_true, ↓reduceIte, ← usize_sub_add j i, byteAt_shift b i (j + 1) hjq,
      hs, hd2, ← usize_sub_add (j + 1) i, hex4_shift b i (j + 1 + 1) hq2, h4]
  | case7 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hjj ih =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hc2 : (byteAt b j != 92) = false := by
      simp only [cb, uget_eq_byteAt h] at hc; simpa using hc
    simp only [simple, d, dite_eq_ite] at hs
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    have hd2 : (byteAt b (j + 1) != 117) = false := by simp [hd]
    have hlt1 : (j + 1) < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hd]; decide)
    have hjs2 : (j + 1 + 1).toNat = (j + 1).toNat + 1 := usizeStep b (j + 1) hlt1
    have hq2 : i.toNat ≤ (j + 1 + 1).toNat := by omega
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hq6 : i.toNat ≤ (j + 1 + 1 + 1 + 1 + 1 + 1).toNat := by omega
    have hD : (j - i) < (j + 1 + 1 + 1 + 1 + 1 + 1) - i :=
      (lt_shift i j (j + 1 + 1 + 1 + 1 + 1 + 1) hij hq6).mpr hjj
    simp only [j6] at ih ⊢
    rw [ih hq6]
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc2,
      Bool.false_eq_true, ↓reduceIte, ← usize_sub_add, byteAt_shift b i (j + 1) hjq,
      hs, hd2, hex4_shift b i (j + 1 + 1) hq2, h4, hcond, dif_pos hD]
  | case8 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hjj =>
    intro hij
    exfalso
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hlt6 : j < (j + 1 + 1 + 1 + 1 + 1 + 1) := USize.lt_iff_toNat_lt.mpr (by omega)
    exact hjj hlt6
  | case9 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hdc hjj ih =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hc2 : (byteAt b j != 92) = false := by
      simp only [cb, uget_eq_byteAt h] at hc; simpa using hc
    simp only [simple, d, dite_eq_ite] at hs
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    have hd2 : (byteAt b (j + 1) != 117) = false := by simp [hd]
    have hlt1 : (j + 1) < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hd]; decide)
    have hjs2 : (j + 1 + 1).toNat = (j + 1).toNat + 1 := usizeStep b (j + 1) hlt1
    have hq2 : i.toNat ≤ (j + 1 + 1).toNat := by omega
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hq6 : i.toNat ≤ (j + 1 + 1 + 1 + 1 + 1 + 1).toNat := by omega
    have hD : (j - i) < (j + 1 + 1 + 1 + 1 + 1 + 1) - i :=
      (lt_shift i j (j + 1 + 1 + 1 + 1 + 1 + 1) hij hq6).mpr hjj
    simp only [j6] at ih ⊢
    rw [ih hq6]
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc2,
      Bool.false_eq_true, ↓reduceIte, ← usize_sub_add, byteAt_shift b i (j + 1) hjq,
      hs, hd2, hex4_shift b i (j + 1 + 1) hq2, h4, hcond, hdc, dif_pos hD]
  | case10 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hdc hjj =>
    intro hij
    exfalso
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hlt6 : j < (j + 1 + 1 + 1 + 1 + 1 + 1) := USize.lt_iff_toNat_lt.mpr (by omega)
    exact hjj hlt6
  | case11 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hdc cont v2 hm hv2 hjj ih =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hc2 : (byteAt b j != 92) = false := by
      simp only [cb, uget_eq_byteAt h] at hc; simpa using hc
    simp only [simple, d, dite_eq_ite] at hs
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    have hd2 : (byteAt b (j + 1) != 117) = false := by simp [hd]
    have hlt1 : (j + 1) < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hd]; decide)
    have hjs2 : (j + 1 + 1).toNat = (j + 1).toNat + 1 := usizeStep b (j + 1) hlt1
    have hq2 : i.toNat ≤ (j + 1 + 1).toNat := by omega
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hq6 : i.toNat ≤ (j + 1 + 1 + 1 + 1 + 1 + 1).toNat := by omega
    have hD : (j - i) < (j + 1 + 1 + 1 + 1 + 1 + 1) - i :=
      (lt_shift i j (j + 1 + 1 + 1 + 1 + 1 + 1) hij hq6).mpr hjj
    simp only [cont, j6, dite_eq_ite] at hm
    simp only [j6] at ih ⊢
    rw [ih hq6]
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc2,
      Bool.false_eq_true, ↓reduceIte, ← usize_sub_add, byteAt_shift b i (j + 1) hjq,
      hs, hd2, hex4_shift b i (j + 1 + 1) hq2, h4, hcond, hdc,
      cont_hex3_shift b i (j + 1 + 1 + 1 + 1 + 1 + 1) hq6, hm, hv2, dif_pos hD]
  | case12 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hdc cont v2 hm hv2 hjj =>
    intro hij
    exfalso
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hlt6 : j < (j + 1 + 1 + 1 + 1 + 1 + 1) := USize.lt_iff_toNat_lt.mpr (by omega)
    exact hjj hlt6
  | case13 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hdc cont v2 hm hv2 j12 cv hjj ih =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hc2 : (byteAt b j != 92) = false := by
      simp only [cb, uget_eq_byteAt h] at hc; simpa using hc
    simp only [simple, d, dite_eq_ite] at hs
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    have hd2 : (byteAt b (j + 1) != 117) = false := by simp [hd]
    have hlt1 : (j + 1) < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hd]; decide)
    have hjs2 : (j + 1 + 1).toNat = (j + 1).toNat + 1 := usizeStep b (j + 1) hlt1
    have hq2 : i.toNat ≤ (j + 1 + 1).toNat := by omega
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hq6 : i.toNat ≤ (j + 1 + 1 + 1 + 1 + 1 + 1).toNat := by omega
    simp only [cont, j6, dite_eq_ite] at hm
    simp only [j12, j6] at hjj ih ⊢
    have hjj2 : j.toNat < (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat :=
      USize.lt_iff_toNat_lt.mp hjj
    have hq12 : i.toNat ≤ (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1).toNat := by omega
    have hD12 : (j - i) < (j + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) - i :=
      (lt_shift i j _ hij hq12).mpr hjj
    rw [ih hq12]
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc2,
      Bool.false_eq_true, ↓reduceIte, ← usize_sub_add, byteAt_shift b i (j + 1) hjq,
      hs, hd2, hex4_shift b i (j + 1 + 1) hq2, h4, hcond, hdc,
      cont_hex3_shift b i (j + 1 + 1 + 1 + 1 + 1 + 1) hq6, hm, hv2, dif_pos hD12, cv]
  | case14 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hdc cont v2 hm hv2 j12 hjj =>
    intro hij
    exfalso
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    simp only [cont, j6, dite_eq_ite] at hm
    have h12 := j12_facts hm
    simp only [j12, j6] at hjj
    exact hjj (USize.lt_iff_toNat_lt.mpr (by omega))
  | case15 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hdc cont hm hjj ih =>
    intro hij
    have hjs := usizeStep b j h
    have hA := (lt_usize_shift b i j hij).mpr h
    have hB := (lt_shift i j e hij hie).mpr hje
    have hjq : i.toNat ≤ (j + 1).toNat := by omega
    have hc2 : (byteAt b j != 92) = false := by
      simp only [cb, uget_eq_byteAt h] at hc; simpa using hc
    simp only [simple, d, dite_eq_ite] at hs
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    have hd2 : (byteAt b (j + 1) != 117) = false := by simp [hd]
    have hlt1 : (j + 1) < b.usize := lt_usize_of_byteAt_ne_zero (by rw [hd]; decide)
    have hjs2 : (j + 1 + 1).toNat = (j + 1).toNat + 1 := usizeStep b (j + 1) hlt1
    have hq2 : i.toNat ≤ (j + 1 + 1).toNat := by omega
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hq6 : i.toNat ≤ (j + 1 + 1 + 1 + 1 + 1 + 1).toNat := by omega
    have hD : (j - i) < (j + 1 + 1 + 1 + 1 + 1 + 1) - i :=
      (lt_shift i j (j + 1 + 1 + 1 + 1 + 1 + 1) hij hq6).mpr hjj
    simp only [cont, j6, dite_eq_ite] at hm
    simp only [j6] at ih ⊢
    rw [ih hq6]
    conv => rhs; rw [unescape.eq_def]
    simp only [uget_eq_byteAt hA, byteAt_shift b i j hij, dif_pos hA, if_pos hB, hc2,
      Bool.false_eq_true, ↓reduceIte, ← usize_sub_add, byteAt_shift b i (j + 1) hjq,
      hs, hd2, hex4_shift b i (j + 1 + 1) hq2, h4, hcond, hdc,
      cont_hex3_shift b i (j + 1 + 1 + 1 + 1 + 1 + 1) hq6, hm, dif_pos hD]
  | case16 j acc h hje cb hc d simple hs hd117 v h4 j6 hcond hdc cont hm hjj =>
    intro hij
    exfalso
    simp only [d] at hd117
    have hd : byteAt b (j + 1) = 117 := by simpa using hd117
    obtain ⟨hj6, hj6b⟩ := j6_facts h hd h4
    have hlt6 : j < (j + 1 + 1 + 1 + 1 + 1 + 1) := USize.lt_iff_toNat_lt.mpr (by omega)
    exact hjj hlt6

/-- The naive body is the input up to (and excluding) its closing quote. -/
theorem naiveStrBody_append {l body r : List UInt8} (h : naiveStrBody l = some (body, r)) :
    l = body ++ 34 :: r := by
  induction l using naiveStrBody.induct generalizing body r with
  | case1 => simp [naiveStrBody] at h
  | case2 c l' hc =>
    rw [naiveStrBody.eq_def] at h
    simp only [hc, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    have hc34 : c = 34 := by simpa using hc
    rw [← h.1, ← h.2, hc34]
    rfl
  | case3 c hc hb => simp [naiveStrBody, hc, hb] at h
  | case4 c hc hb d l' ih =>
    rw [naiveStrBody.eq_def] at h
    simp only [hc, hb, ↓reduceIte, Bool.false_eq_true] at h
    cases hs : naiveStrBody l' with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨body', r'⟩ := p
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      simp only [List.cons_append]
      rw [← ih hs]
  | case5 c l' hc hb hlt => rw [naiveStrBody.eq_def] at h; simp [hc, hb, hlt] at h
  | case6 c l' hc hb hlt ih =>
    rw [naiveStrBody.eq_def] at h
    simp only [hc, hb, hlt, ↓reduceIte, Bool.false_eq_true] at h
    cases hs : naiveStrBody l' with
    | none => simp [hs] at h
    | some p =>
      obtain ⟨body', r'⟩ := p
      simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      rw [← h.1, ← h.2]
      simp only [List.cons_append]
      rw [← ih hs]

theorem naiveStr_cons (l l' : List UInt8) (h : l = 34 :: l') :
    naiveStr l =
      (match naiveStrBody l' with
        | none => .err .expectedString l
        | some (body, rest) =>
          if body.contains 92 then
            match unescape ⟨⟨l⟩⟩ 1 (1 + body.length).toUSize .empty with
            | some s => .ok s rest
            | none => .err .badEscape l
          else
            match String.fromUTF8? ⟨⟨body⟩⟩ with
            | some s => .ok s rest
            | none => .err .badUtf8 l) := by
  subst h; rfl

theorem naiveStr_err {l : List UInt8} (h : ¬ l.headD 0 = 34) :
    naiveStr l = .err .expectedString l := by
  unfold naiveStr
  split
  · simp at h
  · rfl

theorem scanString_eq (b : ByteArray) (i : USize) :
    scanString b i = liftRes b i (naiveStr (tailAt b i)) := by
  unfold scanString
  simp only [byteAt_eq]
  by_cases hlt : i < b.usize
  · have hT := tailAt_of_lt hlt
    by_cases hc : b.uget i (usizeInBounds b i hlt) = 34
    · rw [hc] at hT
      have hbyte : ((tailAt b i).headD 0 != 34) = false := by rw [hT]; simp
      simp only [hbyte, Bool.false_eq_true, ↓reduceIte]
      rw [naiveStr_cons (tailAt b i) (tailAt b (i + 1)) hT]
      have hstep := usizeStep b i hlt
      have hbl := USize.toNat_lt_size b.usize
      have hib : i.toNat < b.usize.toNat := USize.lt_iff_toNat_lt.mp hlt
      have hsc := strClose_eq b (i + 1)
      have hlenT := length_tailAt b (i + 1)
      cases hb : naiveStrBody (tailAt b (i + 1)) with
      | none =>
        simp only [hb] at hsc
        simp only [hsc, beq_self_eq_true, ↓reduceIte]
        exact (liftRes_err_self b i .expectedString).symm
      | some pr =>
        obtain ⟨body, rest⟩ := pr
        simp only [hb] at hsc
        have happ := naiveStrBody_append hb
        have hlen2 : (tailAt b (i + 1)).length = body.length + 1 + rest.length := by
          rw [happ]; simp only [List.length_append, List.length_cons]; omega
        have hEnat : (strClose b (i + 1)).toNat = i.toNat + 1 + body.length := by
          rw [hsc, toNat_toUSize (by omega)]; omega
        have hElt : (strClose b (i + 1)) < b.usize := by
          rw [USize.lt_iff_toNat_lt, hEnat]; omega
        have hEstep := usizeStep b (strClose b (i + 1)) hElt
        have hEne0' : strClose b (i + 1) ≠ 0 := by
          intro hx
          have hz := congrArg USize.toNat hx
          rw [hEnat] at hz
          have h0 : (0 : USize).toNat = 0 := by simp
          omega
        have hEne0 : (strClose b (i + 1) == 0) = false := by simp [hEne0']
        have htake : (tailAt b (i + 1)).take ((strClose b (i + 1)).toNat - (i + 1).toNat)
            = body := by
          rw [hEnat, happ, show i.toNat + 1 + body.length - (i + 1).toNat = body.length by omega,
            List.take_left]
        have hesc : hasEscape b (i + 1) (strClose b (i + 1)) = body.contains 92 := by
          rw [hasEscape_eq, htake]
        have hex : b.extract (i + 1).toNat (strClose b (i + 1)).toNat = ⟨⟨body⟩⟩ := by
          rw [extract_eq b (i + 1) _ (by omega) (by simp only [length_bytes]; omega), htake]
        have hsub1 : (i + 1) - i = 1 := by
          apply USize.toNat_inj.mp
          rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega))]
          have h1 : (1 : USize).toNat = 1 := by simp
          omega
        have hsub2 : (strClose b (i + 1)) - i = (1 + body.length).toUSize := by
          apply USize.toNat_inj.mp
          rw [USize.toNat_sub_of_le _ _ (USize.le_iff_toNat_le.mpr (by omega)), hEnat,
            toNat_toUSize (by omega)]
          omega
        have hunesc : unescape b (i + 1) (strClose b (i + 1)) ByteArray.empty
            = unescape ⟨⟨tailAt b i⟩⟩ 1 (1 + body.length).toUSize ByteArray.empty := by
          rw [unescape_shift b i (i + 1) (strClose b (i + 1)) ByteArray.empty (by omega)
            (by omega), hsub1, hsub2]
        have hcat : tailAt b i = 34 :: (body ++ 34 :: rest) := by rw [hT, happ]
        have hdrop : rest = (tailAt b i).drop (body.length + 2) := by
          rw [hcat]
          simp only [List.drop_succ_cons]
          rw [← List.drop_drop, List.drop_left]
          rfl
        have hlenc : body.length + 2 ≤ (tailAt b i).length := by
          rw [hcat]; simp only [List.length_cons, List.length_append]; omega
        have hpos : (posAt i.toNat (tailAt b i) rest).toUSize = strClose b (i + 1) + 1 := by
          rw [hdrop, pos_drop_eq b i _ hlenc]
          apply USize.toNat_inj.mp
          rw [toUSize_toNat_add i _ (by omega), toNat_toUSize (by omega), hEstep, hEnat]
          omega
        simp only [hEne0, Bool.false_eq_true, ↓reduceIte, hesc, hex, hunesc]
        by_cases hcon : body.contains 92 = true
        · simp only [hcon, ↓reduceIte]
          cases hu : unescape (⟨⟨tailAt b i⟩⟩ : ByteArray) 1 (1 + body.length).toUSize
              ByteArray.empty with
          | none => exact (liftRes_err_self b i .badEscape).symm
          | some s => simp only [liftRes, hpos]
        · simp only [hcon, Bool.false_eq_true, ↓reduceIte]
          cases hf : String.fromUTF8? (⟨⟨body⟩⟩ : ByteArray) with
          | none => exact (liftRes_err_self b i .badUtf8).symm
          | some s => simp only [liftRes, hpos]
    · have hbyte : ((tailAt b i).headD 0 != 34) = true := by rw [hT]; simpa using hc
      rw [naiveStr_err (by rw [hT]; simpa using hc), liftRes_err_self]
      simp only [hbyte, ↓reduceIte]
  · have hT := tailAt_of_not_lt hlt
    have hbyte : ((tailAt b i).headD 0 != 34) = true := by rw [hT]; rfl
    rw [naiveStr_err (by rw [hT]; simp), liftRes_err_self]
    simp only [hbyte, ↓reduceIte]

/-- The naive quoted decimal on an input that opens with a quote. -/
theorem naiveQuotedNat_cons (l l' : List UInt8) (h : l = 34 :: l') :
    naiveQuotedNat l =
      (match l'.takeWhile isDigit, l'.dropWhile isDigit with
        | [], _ => .err .badNatVal l
        | ds, 34 :: rest => .ok (digitsVal ds) rest
        | _, _ => .err .badNatVal l) := by
  subst h; rfl

theorem naiveQuotedNat_err {l : List UInt8} (h : ¬ l.headD 0 = 34) :
    naiveQuotedNat l = .err .badNatVal l := by
  unfold naiveQuotedNat
  split
  · simp at h
  · rfl

/-- A digit run followed by something other than the closing quote. -/
theorem naiveQuotedNat_bad {l l' : List UInt8} {d c : UInt8} {ds rest : List UInt8}
    (h : l = 34 :: l') (hds : l'.takeWhile isDigit = d :: ds)
    (hrest : l'.dropWhile isDigit = c :: rest) (hc : ¬ c = 34) :
    naiveQuotedNat l = .err .badNatVal l := by
  rw [naiveQuotedNat_cons l l' h, hds, hrest]
  split
  · rfl
  · rename_i heq _
    simp only [List.cons.injEq] at heq
    exact absurd heq.1 hc
  · rfl

theorem scanQuotedNat_eq (b : ByteArray) (i : USize) :
    scanQuotedNat b i = liftRes b i (naiveQuotedNat (tailAt b i)) := by
  unfold scanQuotedNat
  simp only [byteAt_eq]
  by_cases hlt : i < b.usize
  · have hT := tailAt_of_lt hlt
    by_cases hc : b.uget i (usizeInBounds b i hlt) = 34
    · rw [hc] at hT
      have hbyte : ((tailAt b i).headD 0 != 34) = false := by rw [hT]; simp
      simp only [hbyte, Bool.false_eq_true, ↓reduceIte]
      have hstep := usizeStep b i hlt
      have hbl := USize.toNat_lt_size b.usize
      have hil := USize.toNat_lt_size i
      have hib : i.toNat < b.usize.toNat := USize.lt_iff_toNat_lt.mp hlt
      have hsd := skipDigits_toNat b (i + 1)
      have hsplit := List.takeWhile_append_dropWhile (p := isDigit) (l := tailAt b (i + 1))
      have hi1 : (i + 1).toNat ≤ (bytes b).length := by simp only [length_bytes]; omega
      have hsuf : (tailAt b (i + 1)).dropWhile isDigit <:+ tailAt b (i + 1) :=
        List.dropWhile_suffix _
      have hte : tailAt b (skipDigits b (i + 1)) = (tailAt b (i + 1)).dropWhile isDigit := by
        rw [skipDigits_eq]; exact tailAt_posAt hi1 hsuf
      cases hds : (tailAt b (i + 1)).takeWhile isDigit with
      | nil =>
        have hnq : naiveQuotedNat (tailAt b i) = .err .badNatVal (tailAt b i) := by
          rw [naiveQuotedNat_cons _ _ hT, hds]
        have heq : skipDigits b (i + 1) = i + 1 := by
          apply USize.toNat_inj.mp; rw [hsd, hds]; simp
        rw [hnq, liftRes_err_self]
        simp only [heq, beq_self_eq_true, Bool.true_or, ↓reduceIte]
      | cons d ds' =>
        have hh : (d :: ds').length = ds'.length + 1 := rfl
        have hlend : (skipDigits b (i + 1)).toNat = i.toNat + 1 + (ds'.length + 1) := by
          rw [hsd, hds]; simp only [List.length_cons]; omega
        have hne1' : skipDigits b (i + 1) ≠ i + 1 := by
          intro hx; rw [hx, hstep] at hlend; omega
        have hne1 : (skipDigits b (i + 1) == i + 1) = false := by simp [hne1']
        cases hrest : (tailAt b (i + 1)).dropWhile isDigit with
        | nil =>
          have hnq : naiveQuotedNat (tailAt b i) = .err .badNatVal (tailAt b i) := by
            rw [naiveQuotedNat_cons _ _ hT, hds, hrest]
          have hb0 : ((tailAt b (skipDigits b (i + 1))).headD 0 != 34) = true := by
            rw [hte, hrest]; rfl
          rw [hnq, liftRes_err_self]
          simp only [hne1, hb0, Bool.false_or, ↓reduceIte]
        | cons c rest' =>
          have hbc : (tailAt b (skipDigits b (i + 1))).headD 0 = c := by rw [hte, hrest]; rfl
          by_cases hc34 : c = 34
          · subst hc34
            have hnq : naiveQuotedNat (tailAt b i) = .ok (digitsVal (d :: ds')) rest' := by
              rw [naiveQuotedNat_cons _ _ hT, hds, hrest]
              rfl
            have hqlt : skipDigits b (i + 1) < b.usize := by
              rw [USize.lt_iff_toNat_lt]
              have h1 := length_tailAt b (skipDigits b (i + 1))
              rw [hte, hrest] at h1
              simp only [List.length_cons] at h1
              omega
            have hqstep := usizeStep b (skipDigits b (i + 1)) hqlt
            have hcat : tailAt b i = 34 :: ((d :: ds') ++ 34 :: rest') := by
              rw [hT]; congr 1; rw [← hds, ← hrest, hsplit]
            have hdrop : rest' = (tailAt b i).drop ((d :: ds').length + 2) := by
              rw [hcat]
              simp only [List.drop_succ_cons]
              rw [← List.drop_drop, List.drop_left]
              rfl
            have hlenT : (tailAt b i).length = b.usize.toNat - i.toNat := length_tailAt b i
            have hlenc : (d :: ds').length + 2 ≤ (tailAt b i).length := by
              rw [hcat]
              simp only [List.length_cons, List.length_append]
              omega
            have hbnd : i.toNat + ((d :: ds').length + 2) < USize.size := by omega
            have hposu : (posAt i.toNat (tailAt b i) rest').toUSize = skipDigits b (i + 1) + 1 := by
              rw [hdrop, pos_drop_eq b i _ hlenc]
              apply USize.toNat_inj.mp
              rw [toUSize_toNat_add i _ hbnd, toNat_toUSize hbnd, hqstep]
              omega
            rw [hnq]
            simp only [hne1, hbc, bne_self_eq_false, Bool.or_self, Bool.false_eq_true,
              ↓reduceIte]
            rw [readNatAt_eq, hds]
            simp only [liftRes, hposu]
          · have hnq := naiveQuotedNat_bad hT hds hrest hc34
            have hbc' : ((tailAt b (skipDigits b (i + 1))).headD 0 != 34) = true := by
              rw [hbc]; simpa using hc34
            rw [hnq, liftRes_err_self]
            simp only [hne1, hbc', Bool.or_true, ↓reduceIte]
    · have hnq : naiveQuotedNat (tailAt b i) = .err .badNatVal (tailAt b i) :=
        naiveQuotedNat_err (by rw [hT]; simpa using hc)
      have hbyte : ((tailAt b i).headD 0 != 34) = true := by rw [hT]; simpa using hc
      rw [hnq, liftRes_err_self]
      simp only [hbyte, ↓reduceIte]
  · have hT := tailAt_of_not_lt hlt
    have hnq : naiveQuotedNat (tailAt b i) = .err .badNatVal (tailAt b i) :=
      naiveQuotedNat_err (by rw [hT]; simp)
    have hbyte : ((tailAt b i).headD 0 != 34) = true := by rw [hT]; rfl
    rw [hnq, liftRes_err_self]
    simp only [hbyte, ↓reduceIte]

/-- The naive reader of a `binderInfo` fails on any input that does
not open with a quote. -/
theorem naiveBinderInfo_err {l : List UInt8} (h : ¬ l.headD 0 = 34) :
    naiveBinderInfo l = .err .badBinderInfo l := by
  unfold naiveBinderInfo
  split
  · simp at h
  · rfl

/-- …and on a quoted input it is the four literal tries. -/
theorem naiveBinderInfo_cons (t : List UInt8) :
    naiveBinderInfo (34 :: t) =
      match naiveLit "default\"" t with
      | some r => .ok () r
      | none =>
        match naiveLit "implicit\"" t with
        | some r => .ok () r
        | none =>
          match naiveLit "strictImplicit\"" t with
          | some r => .ok () r
          | none =>
            match naiveLit "instImplicit\"" t with
            | some r => .ok () r
            | none => .err .badBinderInfo (34 :: t) := by
  unfold naiveBinderInfo
  split
  · rename_i heq
    simp only [List.cons.injEq, true_and] at heq
    subst heq
    rfl
  · rename_i hno
    exact absurd rfl (hno t)

theorem scanBinderInfo_eq (b : ByteArray) (i : USize) :
    scanBinderInfo b i = match naiveBinderInfo (tailAt b i) with
      | .ok _ r => (posAt i.toNat (tailAt b i) r).toUSize
      | .err _ _ => 0 := by
  unfold scanBinderInfo
  rw [byteAt_eq,
      matchLit_lit b (i + 1) "default\"" (size_toUTF8_lt "default\"" 8 rfl (by decide)),
      matchLit_lit b (i + 1) "implicit\"" (size_toUTF8_lt "implicit\"" 9 rfl (by decide)),
      matchLit_lit b (i + 1) "strictImplicit\""
        (size_toUTF8_lt "strictImplicit\"" 15 rfl (by decide)),
      matchLit_lit b (i + 1) "instImplicit\"" (size_toUTF8_lt "instImplicit\"" 13 rfl (by decide))]
  by_cases hlt : i < b.usize
  · have hT := tailAt_of_lt hlt
    by_cases hc : b.uget i (usizeInBounds b i hlt) = 34
    · rw [hc] at hT
      rw [hT, naiveBinderInfo_cons]
      unfold naiveLit
      simp only [List.headD_cons, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte]
      by_cases h1 : (lit "default\"").isPrefixOf (tailAt b (i + 1))
      · have hl1 := (List.isPrefixOf_iff_prefix.mp h1).length_le
        rw [length_lit_default] at hl1
        simp only [h1, ↓reduceIte, length_lit_default]
        rw [pos_cons_drop hT hl1]
        rfl
      · by_cases h2 : (lit "implicit\"").isPrefixOf (tailAt b (i + 1))
        · have hl2 := (List.isPrefixOf_iff_prefix.mp h2).length_le
          rw [length_lit_implicit] at hl2
          simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, length_lit_implicit]
          rw [pos_cons_drop hT hl2]
          rfl
        · by_cases h3 : (lit "strictImplicit\"").isPrefixOf (tailAt b (i + 1))
          · have hl3 := (List.isPrefixOf_iff_prefix.mp h3).length_le
            rw [length_lit_strictImplicit] at hl3
            simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte, length_lit_strictImplicit]
            rw [pos_cons_drop hT hl3]
            rfl
          · by_cases h4 : (lit "instImplicit\"").isPrefixOf (tailAt b (i + 1))
            · have hl4 := (List.isPrefixOf_iff_prefix.mp h4).length_le
              rw [length_lit_instImplicit] at hl4
              simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte, length_lit_instImplicit]
              rw [pos_cons_drop hT hl4]
              rfl
            · simp only [h1, h2, h3, h4, Bool.false_eq_true, ↓reduceIte]
    · have hc2 : (b.uget i (usizeInBounds b i hlt) != 34) = true := by simpa using hc
      rw [naiveBinderInfo_err (by rw [hT]; simpa using hc), hT]
      simp only [List.headD_cons, hc2, ↓reduceIte]
  · have hT := tailAt_of_not_lt hlt
    rw [naiveBinderInfo_err (by rw [hT]; simp), hT]
    simp

end ConLeche.Frontend
