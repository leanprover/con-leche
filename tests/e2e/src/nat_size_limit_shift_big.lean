/- End-to-end test, ported from lean4's
   `tests/elab/nat_size_limit.lean` (lean4#14849), run at
   `--max-nat-size=16` as that test runs at `LEAN_NAT_MAX_SIZE=16` (arena.sh's
   E2E_FLAGS): `1 <<< 200` would exceed the maximum size: rejected before
   computing. -/

--#export shiftBig subHelper

theorem shiftBig : Eq (Nat.ble (Nat.shiftLeft 1 200) 0) Bool.false := Eq.refl Bool.false
theorem subHelper : Eq (Nat.sub 9 4) 5 := Eq.refl 5
