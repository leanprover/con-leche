/- End-to-end test source: the official kernel's numeral budget
   (lean4#14849) at its default, 128 MiB.  The committed fixtures are
   derived from this export by `scripts/mk_nat_size_fixtures.py`, which
   replaces the placeholder exponents 201..205 (the elaborator would not
   compute the real ones) by the values the fixtures are about:

   * `nat_size_ok`: `1 ^ 4000000000`, `0 ^ 4000000000`,
     `1 ^ 4294967295` (the largest 32-bit exponent), `2 ^ 16777216`
     (the largest power of two within the budget: 8 bytes per unit of
     the exponent), `1 <<< 100000000` (12.5 MB) — accepted;
   * `nat_pow_over_budget`: `2 ^ 16777217` — rejected before computing;
   * `nat_pow_exp_32bit`: `1 ^ 4294967296` — rejected, base 1 or not;
   * `nat_shift_over_budget`: `1 <<< 1073741760` — rejected before
     computing;
   * `nat_shift_exp_32bit`: `1 <<< 4294967296` — rejected.

   This export itself (small exponents) is accepted.  `subHelper`
   pulls `Nat.sub` into the export, ground of `Nat.shiftLeft`'s pinned
   certificate. -/

--#export onePow zeroPow onePowMax powEdge shiftOk subHelper

theorem onePow : Eq (Nat.pow 1 201) 1 := Eq.refl 1
theorem zeroPow : Eq (Nat.pow 0 202) 0 := Eq.refl 0
theorem onePowMax : Eq (Nat.pow 1 203) 1 := Eq.refl 1
theorem powEdge : Eq (Nat.ble (Nat.pow 2 204) 0) Bool.false := Eq.refl Bool.false
theorem shiftOk : Eq (Nat.ble (Nat.shiftLeft 1 205) 0) Bool.false := Eq.refl Bool.false
theorem subHelper : Eq (Nat.sub 9 4) 5 := Eq.refl 5
