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

end ConLeche.Frontend
