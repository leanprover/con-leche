/- End-to-end test: edge cases of the certified structural-Nat fast
   path — zero operands, truncated subtraction, `pred 0`, `0 ^ 0`,
   nested operator chains, and non-`.lit` argument forms (a `succ`
   application and the `Nat.zero` constant both whnf to literals
   before the fast path fires). -/

--#export addZero zeroAdd subZero subUnderflow predZero powZero
--#export zeroPow mulZero nested ctorArg zeroConstArg beqFalse bleFalse

theorem addZero : Eq (Nat.add 0 0) 0 := Eq.refl 0
theorem zeroAdd : Eq (Nat.add 0 37) 37 := Eq.refl 37
theorem subZero : Eq (Nat.sub 41 0) 41 := Eq.refl 41
theorem subUnderflow : Eq (Nat.sub 3 5) 0 := Eq.refl 0
theorem predZero : Eq (Nat.pred 0) 0 := Eq.refl 0
theorem powZero : Eq (Nat.pow 7 0) 1 := Eq.refl 1
theorem zeroPow : Eq (Nat.pow 0 0) 1 := Eq.refl 1
theorem mulZero : Eq (Nat.mul 29 0) 0 := Eq.refl 0
theorem nested :
    Eq (Nat.sub (Nat.mul (Nat.add 2 3) 4) 1) 19 := Eq.refl 19
theorem ctorArg : Eq (Nat.add (Nat.succ 4) 2) 7 := Eq.refl 7
theorem zeroConstArg : Eq (Nat.add Nat.zero 3) 3 := Eq.refl 3
theorem beqFalse : Eq (Nat.beq 7 8) Bool.false := Eq.refl Bool.false
theorem bleFalse : Eq (Nat.ble 9 5) Bool.false := Eq.refl Bool.false
