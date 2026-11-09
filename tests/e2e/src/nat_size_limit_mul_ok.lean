/- End-to-end test, ported from lean4's
   `tests/elab/nat_size_limit.lean` (lean4#14849), run at
   `--nat-max-size=16` as that test runs at `LEAN_NAT_MAX_SIZE=16` (arena.sh's
   E2E_FLAGS): two-limb operands, a two-limb product (2^64): accepted. -/

--#export mulOk

theorem mulOk : Eq (Nat.ble (Nat.mul 4294967296 4294967296) 0) Bool.false := Eq.refl Bool.false
