/- End-to-end test: the certified structural-Nat literal fast path.

   Each theorem is an `Eq.refl` at big literals, so acceptance forces
   the checker to decide the arithmetic by definitional equality —
   unary expansion would be astronomically infeasible, so these pass
   only through the certified add/sub/mul/pow/beq/ble reductions. -/

--#export addBig subBig mulBig powBig beqBig bleBig predBig

theorem addBig :
    Eq (Nat.add 18446744073709551616 18446744073709551616)
      36893488147419103232 :=
  Eq.refl 36893488147419103232

theorem subBig :
    Eq (Nat.sub 36893488147419103232 18446744073709551615)
      18446744073709551617 :=
  Eq.refl 18446744073709551617

theorem mulBig :
    Eq (Nat.mul 4294967296 4294967296) 18446744073709551616 :=
  Eq.refl 18446744073709551616

theorem powBig : Eq (Nat.pow 2 64) 18446744073709551616 :=
  Eq.refl 18446744073709551616

theorem beqBig :
    Eq (Nat.beq 18446744073709551616 18446744073709551616) Bool.true :=
  Eq.refl Bool.true

theorem bleBig :
    Eq (Nat.ble 18446744073709551615 18446744073709551616) Bool.true :=
  Eq.refl Bool.true

theorem predBig :
    Eq (Nat.pred 18446744073709551616) 18446744073709551615 :=
  Eq.refl 18446744073709551615
