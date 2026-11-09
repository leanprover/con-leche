/- End-to-end test, ported from lean4's
   `tests/elab/nat_size_limit.lean` (lean4#14849), run at
   `--nat-max-size=16` as that test runs at `LEAN_NAT_MAX_SIZE=16` (arena.sh's
   E2E_FLAGS): a three-limb product (2^128) of two-limb operands:
   rejected after computing. -/

--#export mulBig

theorem mulBig : Eq (Nat.ble (Nat.mul 18446744073709551616 18446744073709551616) 0) Bool.false := Eq.refl Bool.false
