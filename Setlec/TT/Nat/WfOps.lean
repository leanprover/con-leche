import Setlec.TT.Nat.Ops

/-!
# The pin-certified WF-recursive `Nat` operations on numerals

One lemma family per operation of `natDivModNames`
(`div`, `mod`, `gcd`, `land`, `lor`, `xor`, `shiftLeft`, `shiftRight`,
`log2`).  As in `Setlec/TT/Nat/Ops.lean`, each is hypothetical over an
arbitrary term, and the hypotheses are the checker's own certified
clauses instantiated at numerals — here the `Nat.ble`-guarded
recurrences of `DivModClauses` (`Setlec/Model/Interp.lean`), whose
pinned statements live in `Setlec/PinGen/Certs.lean`.

Three differences from the structural family, all inherited from the
model-side proof (`natOpVal_divmod`, `natOpVal_gcd`, …):

* the induction is a **meta-level strong induction**, not structural;
* the clauses are **guarded**, so each case first computes the guard —
  which is `numeral_ble`, applied at `1`, `2` or the two arguments.
  The guard values `tv`/`fv` are opaque terms and are never required to
  be distinct: each branch proves the guard equation it needs and
  applies the matching clause;
* the bit operations need a meta-level recurrence for Lean's own
  `Nat.land`/`Nat.lor`/`Nat.xor` (`nat_land_rec_two` and friends
  below).  `Setlec/PinGen/Certs.lean` proves the same three facts, but
  under a self-imposed austerity (no `simp`, no `decide`, only
  stream-prefix lemmas) that does not apply here, so they are re-proved
  from the public `Nat.bitwise` API rather than imported — the layer
  must not depend on the checker's build.
-/

namespace Setlec.TT

/-! ## Meta-level recurrences for the bit operations

`Nat.bitwise f` commutes with `/2` and `%2` (`bitwise_div_two_pow`,
`bitwise_mod_two_pow` at `n = 1`), and `x = 2 * (x / 2) + x % 2`; the
low bit is then computed by the four cases of `x % 2`, `y % 2`. -/

private theorem bitwise_rec_two (f : Bool → Bool → Bool)
    (hff : f false false = false) (x y : Nat) :
    Nat.bitwise f x y =
      2 * Nat.bitwise f (x / 2) (y / 2) + Nat.bitwise f (x % 2) (y % 2) := by
  have hd : Nat.bitwise f x y / 2 = Nat.bitwise f (x / 2) (y / 2) := by
    have := Nat.bitwise_div_two_pow (f := f) (x := x) (y := y) (n := 1) hff
    simpa using this
  have hm : Nat.bitwise f x y % 2 = Nat.bitwise f (x % 2) (y % 2) := by
    have := Nat.bitwise_mod_two_pow (f := f) (x := x) (y := y) (n := 1) hff
    simpa using this
  calc Nat.bitwise f x y
      = 2 * (Nat.bitwise f x y / 2) + Nat.bitwise f x y % 2 :=
        (Nat.div_add_mod _ 2).symm
    _ = 2 * Nat.bitwise f (x / 2) (y / 2) + Nat.bitwise f (x % 2) (y % 2) := by
        rw [hd, hm]

theorem nat_land_rec_two (x y : Nat) :
    Nat.land x y = 2 * Nat.land (x / 2) (y / 2) + x % 2 * (y % 2) := by
  have h := bitwise_rec_two and rfl x y
  show Nat.bitwise and x y = 2 * Nat.bitwise and (x / 2) (y / 2) + x % 2 * (y % 2)
  rw [h]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
    rw [hx, hy] <;> simp [Nat.bitwise]

theorem nat_lor_rec_two (x y : Nat) :
    Nat.lor x y =
      2 * Nat.lor (x / 2) (y / 2) + (x % 2 + y % 2 - x % 2 * (y % 2)) := by
  have h := bitwise_rec_two or rfl x y
  show Nat.bitwise or x y = _
  rw [h]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
    rw [hx, hy] <;> simp [Nat.bitwise]

theorem nat_xor_rec_two (x y : Nat) :
    Nat.xor x y = 2 * Nat.xor (x / 2) (y / 2) + (x % 2 + y % 2) % 2 := by
  have h := bitwise_rec_two bne rfl x y
  show Nat.bitwise bne x y = _
  rw [h]
  congr 1
  rcases Nat.mod_two_eq_zero_or_one x with hx | hx <;>
    rcases Nat.mod_two_eq_zero_or_one y with hy | hy <;>
    rw [hx, hy] <;> simp [Nat.bitwise]

/-! ## The operations -/

variable {Γ : List VExpr} {bl tv fv : VExpr}

/-- `Nat.div` on numerals. -/
theorem numeral_div {dv sb : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hsub : ∀ a b, Deq Γ (ap2 sb (numeral a) (numeral b)) (numeral (a - b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral b) (numeral a)) tv →
      Deq Γ (ap2 bl (numeral 1) (numeral b)) tv →
      Deq Γ (ap2 dv (numeral a) (numeral b))
        (natSuccT (ap2 dv (ap2 sb (numeral a) (numeral b)) (numeral b))))
    (hgt : ∀ a b, Deq Γ (ap2 bl (numeral b) (numeral a)) fv →
      Deq Γ (ap2 dv (numeral a) (numeral b)) natZeroT)
    (hzero : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral b)) fv →
      Deq Γ (ap2 dv (numeral a) (numeral b)) natZeroT) :
    ∀ a b, Deq Γ (ap2 dv (numeral a) (numeral b)) (numeral (a / b)) := by
  intro a b
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases hb0 : b = 0
    · subst hb0
      rw [Nat.div_zero]
      exact hzero a 0 (by have := hble 1 0; rwa [if_neg (by omega)] at this)
    · by_cases hba : b ≤ a
      · have h1 : Deq Γ (ap2 bl (numeral b) (numeral a)) tv := by
          have := hble b a; rwa [if_pos hba] at this
        have h2 : Deq Γ (ap2 bl (numeral 1) (numeral b)) tv := by
          have := hble 1 b; rwa [if_pos (by omega)] at this
        rw [show a / b = (a - b) / b + 1 from by
          rw [Nat.div_eq a b, if_pos ⟨by omega, hba⟩]]
        exact (hrec a b h1 h2).trans (Deq.appArg
          ((Deq.ap2 (hsub a b) Deq.refl).trans
            (ih (a - b) (Nat.sub_lt (by omega) (by omega)))))
      · rw [Nat.div_eq_of_lt (by omega)]
        exact hgt a b (by have := hble b a; rwa [if_neg hba] at this)

/-- `Nat.mod` on numerals. -/
theorem numeral_mod {md sb : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hsub : ∀ a b, Deq Γ (ap2 sb (numeral a) (numeral b)) (numeral (a - b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral b) (numeral a)) tv →
      Deq Γ (ap2 bl (numeral 1) (numeral b)) tv →
      Deq Γ (ap2 md (numeral a) (numeral b))
        (ap2 md (ap2 sb (numeral a) (numeral b)) (numeral b)))
    (hgt : ∀ a b, Deq Γ (ap2 bl (numeral b) (numeral a)) fv →
      Deq Γ (ap2 md (numeral a) (numeral b)) (numeral a))
    (hzero : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral b)) fv →
      Deq Γ (ap2 md (numeral a) (numeral b)) (numeral a)) :
    ∀ a b, Deq Γ (ap2 md (numeral a) (numeral b)) (numeral (a % b)) := by
  intro a b
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases hb0 : b = 0
    · subst hb0
      rw [Nat.mod_zero]
      exact hzero a 0 (by have := hble 1 0; rwa [if_neg (by omega)] at this)
    · by_cases hba : b ≤ a
      · have h1 : Deq Γ (ap2 bl (numeral b) (numeral a)) tv := by
          have := hble b a; rwa [if_pos hba] at this
        have h2 : Deq Γ (ap2 bl (numeral 1) (numeral b)) tv := by
          have := hble 1 b; rwa [if_pos (by omega)] at this
        rw [show a % b = (a - b) % b from Nat.mod_eq_sub_mod hba]
        exact (hrec a b h1 h2).trans
          ((Deq.ap2 (hsub a b) Deq.refl).trans
            (ih (a - b) (Nat.sub_lt (by omega) (by omega))))
      · rw [Nat.mod_eq_of_lt (by omega)]
        exact hgt a b (by have := hble b a; rwa [if_neg hba] at this)

/-- `Nat.gcd` on numerals. -/
theorem numeral_gcd {gc md : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hmod : ∀ a b, Deq Γ (ap2 md (numeral a) (numeral b)) (numeral (a % b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral a)) tv →
      Deq Γ (ap2 gc (numeral a) (numeral b))
        (ap2 gc (ap2 md (numeral b) (numeral a)) (numeral a)))
    (hbase : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral a)) fv →
      Deq Γ (ap2 gc (numeral a) (numeral b)) (numeral b)) :
    ∀ a b, Deq Γ (ap2 gc (numeral a) (numeral b)) (numeral (Nat.gcd a b)) := by
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha0 : a = 0
    · subst ha0
      rw [Nat.gcd_zero_left]
      exact hbase 0 b (by have := hble 1 0; rwa [if_neg (by omega)] at this)
    · have h1 : Deq Γ (ap2 bl (numeral 1) (numeral a)) tv := by
        have := hble 1 a; rwa [if_pos (by omega)] at this
      rw [Nat.gcd_rec a b]
      exact (hrec a b h1).trans
        ((Deq.ap2 (hmod b a) Deq.refl).trans
          (ih (b % a) (Nat.mod_lt _ (by omega)) a))

/-- `Nat.shiftLeft` on numerals. -/
theorem numeral_shiftLeft {sl mu sb : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hmul : ∀ a b, Deq Γ (ap2 mu (numeral a) (numeral b)) (numeral (a * b)))
    (hsub : ∀ a b, Deq Γ (ap2 sb (numeral a) (numeral b)) (numeral (a - b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral b)) tv →
      Deq Γ (ap2 sl (numeral a) (numeral b))
        (ap2 sl (ap2 mu (numeral 2) (numeral a))
          (ap2 sb (numeral b) (numeral 1))))
    (hbase : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral b)) fv →
      Deq Γ (ap2 sl (numeral a) (numeral b)) (numeral a)) :
    ∀ a b, Deq Γ (ap2 sl (numeral a) (numeral b))
      (numeral (Nat.shiftLeft a b)) := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases hb0 : b = 0
    · subst hb0
      exact hbase a 0 (by have := hble 1 0; rwa [if_neg (by omega)] at this)
    · have h1 : Deq Γ (ap2 bl (numeral 1) (numeral b)) tv := by
        have := hble 1 b; rwa [if_pos (by omega)] at this
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      rw [show Nat.shiftLeft a (k + 1) = Nat.shiftLeft (2 * a) k from rfl]
      exact (hrec a (k + 1) h1).trans
        ((Deq.ap2 (hmul 2 a) (hsub (k + 1) 1)).trans
          (ih k (by omega) (2 * a)))

/-- `Nat.shiftRight` on numerals. -/
theorem numeral_shiftRight {sr dv sb : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hdiv : ∀ a b, Deq Γ (ap2 dv (numeral a) (numeral b)) (numeral (a / b)))
    (hsub : ∀ a b, Deq Γ (ap2 sb (numeral a) (numeral b)) (numeral (a - b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral b)) tv →
      Deq Γ (ap2 sr (numeral a) (numeral b))
        (ap2 dv (ap2 sr (numeral a) (ap2 sb (numeral b) (numeral 1)))
          (numeral 2)))
    (hbase : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral b)) fv →
      Deq Γ (ap2 sr (numeral a) (numeral b)) (numeral a)) :
    ∀ a b, Deq Γ (ap2 sr (numeral a) (numeral b))
      (numeral (Nat.shiftRight a b)) := by
  intro a b
  induction b using Nat.strongRecOn generalizing a with
  | ind b ih =>
    by_cases hb0 : b = 0
    · subst hb0
      exact hbase a 0 (by have := hble 1 0; rwa [if_neg (by omega)] at this)
    · have h1 : Deq Γ (ap2 bl (numeral 1) (numeral b)) tv := by
        have := hble 1 b; rwa [if_pos (by omega)] at this
      obtain ⟨k, rfl⟩ : ∃ k, b = k + 1 := ⟨b - 1, by omega⟩
      rw [show Nat.shiftRight a (k + 1) = Nat.shiftRight a k / 2 from rfl]
      exact (hrec a (k + 1) h1).trans
        ((Deq.ap2 (Deq.appArg (hsub (k + 1) 1)) Deq.refl).trans
          ((Deq.ap2 (ih k (by omega) a) Deq.refl).trans
            (hdiv (Nat.shiftRight a k) 2)))

/-- `Nat.log2` on numerals.  The only unary operation of the family. -/
theorem numeral_log2 {lg dv : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hdiv : ∀ a b, Deq Γ (ap2 dv (numeral a) (numeral b)) (numeral (a / b)))
    (hrec : ∀ a, Deq Γ (ap2 bl (numeral 2) (numeral a)) tv →
      Deq Γ (.app lg (numeral a))
        (natSuccT (.app lg (ap2 dv (numeral a) (numeral 2)))))
    (hbase : ∀ a, Deq Γ (ap2 bl (numeral 2) (numeral a)) fv →
      Deq Γ (.app lg (numeral a)) natZeroT) :
    ∀ a, Deq Γ (.app lg (numeral a)) (numeral (Nat.log2 a)) := by
  intro a
  induction a using Nat.strongRecOn with
  | ind a ih =>
    by_cases ha2 : 2 ≤ a
    · have h1 : Deq Γ (ap2 bl (numeral 2) (numeral a)) tv := by
        have := hble 2 a; rwa [if_pos ha2] at this
      rw [show Nat.log2 a = Nat.log2 (a / 2) + 1 from by
        rw [Nat.log2_def]; exact if_pos ha2]
      exact (hrec a h1).trans (Deq.appArg
        ((Deq.appArg (hdiv a 2)).trans
          (ih (a / 2) (Nat.div_lt_self (by omega) (by omega)))))
    · have h1 : Deq Γ (ap2 bl (numeral 2) (numeral a)) fv := by
        have := hble 2 a; rwa [if_neg ha2] at this
      rw [Nat.log2_def, if_neg ha2]
      exact hbase a h1

/-! ### The bit operations

All three share the recurrence shape "twice the operation on the
halves, plus a low-bit correction"; only the correction differs
(`Setlec/Model/Interp.lean`, `DivModClauses`). -/

/-- `Nat.land` on numerals. -/
theorem numeral_land {la ad mu dv md : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hadd : ∀ a b, Deq Γ (ap2 ad (numeral a) (numeral b)) (numeral (a + b)))
    (hmul : ∀ a b, Deq Γ (ap2 mu (numeral a) (numeral b)) (numeral (a * b)))
    (hdiv : ∀ a b, Deq Γ (ap2 dv (numeral a) (numeral b)) (numeral (a / b)))
    (hmod : ∀ a b, Deq Γ (ap2 md (numeral a) (numeral b)) (numeral (a % b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral a)) tv →
      Deq Γ (ap2 la (numeral a) (numeral b))
        (ap2 ad
          (ap2 mu (numeral 2)
            (ap2 la (ap2 dv (numeral a) (numeral 2))
              (ap2 dv (numeral b) (numeral 2))))
          (ap2 mu (ap2 md (numeral a) (numeral 2))
            (ap2 md (numeral b) (numeral 2)))))
    (hbase : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral a)) fv →
      Deq Γ (ap2 la (numeral a) (numeral b)) natZeroT) :
    ∀ a b, Deq Γ (ap2 la (numeral a) (numeral b))
      (numeral (Nat.land a b)) := by
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha0 : a = 0
    · subst ha0
      rw [show Nat.land 0 b = 0 from Nat.zero_and b]
      exact hbase 0 b (by have := hble 1 0; rwa [if_neg (by omega)] at this)
    · have h1 : Deq Γ (ap2 bl (numeral 1) (numeral a)) tv := by
        have := hble 1 a; rwa [if_pos (by omega)] at this
      have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by omega)
      have e1 : Deq Γ (ap2 la (ap2 dv (numeral a) (numeral 2))
          (ap2 dv (numeral b) (numeral 2)))
          (numeral (Nat.land (a / 2) (b / 2))) :=
        (Deq.ap2 (hdiv a 2) (hdiv b 2)).trans (ih (a / 2) hlt (b / 2))
      have e2 := (Deq.ap2 Deq.refl e1).trans
        (hmul 2 (Nat.land (a / 2) (b / 2)))
      have e3 := (Deq.ap2 (hmod a 2) (hmod b 2)).trans (hmul (a % 2) (b % 2))
      rw [nat_land_rec_two a b]
      exact (hrec a b h1).trans ((Deq.ap2 e2 e3).trans
        (hadd (2 * Nat.land (a / 2) (b / 2)) (a % 2 * (b % 2))))

/-- `Nat.lor` on numerals. -/
theorem numeral_lor {lo ad sb mu dv md : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hadd : ∀ a b, Deq Γ (ap2 ad (numeral a) (numeral b)) (numeral (a + b)))
    (hsub : ∀ a b, Deq Γ (ap2 sb (numeral a) (numeral b)) (numeral (a - b)))
    (hmul : ∀ a b, Deq Γ (ap2 mu (numeral a) (numeral b)) (numeral (a * b)))
    (hdiv : ∀ a b, Deq Γ (ap2 dv (numeral a) (numeral b)) (numeral (a / b)))
    (hmod : ∀ a b, Deq Γ (ap2 md (numeral a) (numeral b)) (numeral (a % b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral a)) tv →
      Deq Γ (ap2 lo (numeral a) (numeral b))
        (ap2 ad
          (ap2 mu (numeral 2)
            (ap2 lo (ap2 dv (numeral a) (numeral 2))
              (ap2 dv (numeral b) (numeral 2))))
          (ap2 sb
            (ap2 ad (ap2 md (numeral a) (numeral 2))
              (ap2 md (numeral b) (numeral 2)))
            (ap2 mu (ap2 md (numeral a) (numeral 2))
              (ap2 md (numeral b) (numeral 2))))))
    (hbase : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral a)) fv →
      Deq Γ (ap2 lo (numeral a) (numeral b)) (numeral b)) :
    ∀ a b, Deq Γ (ap2 lo (numeral a) (numeral b))
      (numeral (Nat.lor a b)) := by
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha0 : a = 0
    · subst ha0
      rw [show Nat.lor 0 b = b from Nat.zero_or b]
      exact hbase 0 b (by have := hble 1 0; rwa [if_neg (by omega)] at this)
    · have h1 : Deq Γ (ap2 bl (numeral 1) (numeral a)) tv := by
        have := hble 1 a; rwa [if_pos (by omega)] at this
      have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by omega)
      have e1 : Deq Γ (ap2 lo (ap2 dv (numeral a) (numeral 2))
          (ap2 dv (numeral b) (numeral 2)))
          (numeral (Nat.lor (a / 2) (b / 2))) :=
        (Deq.ap2 (hdiv a 2) (hdiv b 2)).trans (ih (a / 2) hlt (b / 2))
      have e2 := (Deq.ap2 Deq.refl e1).trans
        (hmul 2 (Nat.lor (a / 2) (b / 2)))
      have e3 := ((Deq.ap2 (Deq.ap2 (hmod a 2) (hmod b 2))
        (Deq.ap2 (hmod a 2) (hmod b 2))).trans
        (Deq.ap2 (hadd (a % 2) (b % 2)) (hmul (a % 2) (b % 2)))).trans
        (hsub (a % 2 + b % 2) (a % 2 * (b % 2)))
      rw [nat_lor_rec_two a b]
      exact (hrec a b h1).trans ((Deq.ap2 e2 e3).trans
        (hadd (2 * Nat.lor (a / 2) (b / 2))
          (a % 2 + b % 2 - a % 2 * (b % 2))))

/-- `Nat.xor` on numerals. -/
theorem numeral_xor {xo ad mu dv md : VExpr}
    (hble : ∀ a b, Deq Γ (ap2 bl (numeral a) (numeral b))
      (if a ≤ b then tv else fv))
    (hadd : ∀ a b, Deq Γ (ap2 ad (numeral a) (numeral b)) (numeral (a + b)))
    (hmul : ∀ a b, Deq Γ (ap2 mu (numeral a) (numeral b)) (numeral (a * b)))
    (hdiv : ∀ a b, Deq Γ (ap2 dv (numeral a) (numeral b)) (numeral (a / b)))
    (hmod : ∀ a b, Deq Γ (ap2 md (numeral a) (numeral b)) (numeral (a % b)))
    (hrec : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral a)) tv →
      Deq Γ (ap2 xo (numeral a) (numeral b))
        (ap2 ad
          (ap2 mu (numeral 2)
            (ap2 xo (ap2 dv (numeral a) (numeral 2))
              (ap2 dv (numeral b) (numeral 2))))
          (ap2 md
            (ap2 ad (ap2 md (numeral a) (numeral 2))
              (ap2 md (numeral b) (numeral 2)))
            (numeral 2))))
    (hbase : ∀ a b, Deq Γ (ap2 bl (numeral 1) (numeral a)) fv →
      Deq Γ (ap2 xo (numeral a) (numeral b)) (numeral b)) :
    ∀ a b, Deq Γ (ap2 xo (numeral a) (numeral b))
      (numeral (Nat.xor a b)) := by
  intro a b
  induction a using Nat.strongRecOn generalizing b with
  | ind a ih =>
    by_cases ha0 : a = 0
    · subst ha0
      rw [show Nat.xor 0 b = b from Nat.zero_xor b]
      exact hbase 0 b (by have := hble 1 0; rwa [if_neg (by omega)] at this)
    · have h1 : Deq Γ (ap2 bl (numeral 1) (numeral a)) tv := by
        have := hble 1 a; rwa [if_pos (by omega)] at this
      have hlt : a / 2 < a := Nat.div_lt_self (by omega) (by omega)
      have e1 : Deq Γ (ap2 xo (ap2 dv (numeral a) (numeral 2))
          (ap2 dv (numeral b) (numeral 2)))
          (numeral (Nat.xor (a / 2) (b / 2))) :=
        (Deq.ap2 (hdiv a 2) (hdiv b 2)).trans (ih (a / 2) hlt (b / 2))
      have e2 := (Deq.ap2 Deq.refl e1).trans
        (hmul 2 (Nat.xor (a / 2) (b / 2)))
      have e3 := ((Deq.ap2 (Deq.ap2 (hmod a 2) (hmod b 2)) Deq.refl).trans
        (Deq.ap2 (hadd (a % 2) (b % 2)) Deq.refl)).trans
        (hmod (a % 2 + b % 2) 2)
      rw [nat_xor_rec_two a b]
      exact (hrec a b h1).trans ((Deq.ap2 e2 e3).trans
        (hadd (2 * Nat.xor (a / 2) (b / 2)) ((a % 2 + b % 2) % 2)))

end Setlec.TT
