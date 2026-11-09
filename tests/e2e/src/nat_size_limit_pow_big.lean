/- End-to-end test, ported from lean4's
   `tests/elab/nat_size_limit.lean` (lean4#14849), run at
   `--nat-max-size=16` as that test runs at `LEAN_NAT_MAX_SIZE=16` (arena.sh's
   E2E_FLAGS): `2 ^ 100` would exceed the budget: rejected before
   computing. -/

--#export powBig

theorem powBig : Eq (Nat.ble (Nat.pow 2 100) 0) Bool.false := Eq.refl Bool.false
