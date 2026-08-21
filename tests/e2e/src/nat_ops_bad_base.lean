/- Base export for the per-op rejection tests: each theorem's result
   literal is unique in the file, so a patch script can perturb one
   op's stated result independently (see tests/e2e-expected.txt). -/

--#export addOk subOk mulOk powOk predOk

theorem addOk : Eq (Nat.add 11 12) 23 := Eq.refl 23
theorem subOk : Eq (Nat.sub 30 12) 18 := Eq.refl 18
theorem mulOk : Eq (Nat.mul 5 13) 65 := Eq.refl 65
theorem powOk : Eq (Nat.pow 3 4) 81 := Eq.refl 81
theorem predOk : Eq (Nat.pred 44) 43 := Eq.refl 43
