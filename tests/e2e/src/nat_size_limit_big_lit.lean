/- End-to-end test, ported from lean4's
   `tests/elab/nat_size_limit.lean` (lean4#14849), run at
   `--max-nat-size=16` as that test runs at `LEAN_NAT_MAX_SIZE=16` (arena.sh's
   E2E_FLAGS): a literal of the input above the maximum size (2^128):
   rejected where it is inferred. -/

--#export bigLit

theorem bigLit : Eq (Nat.ble 340282366920938463463374607431768211456 0) Bool.false := Eq.refl Bool.false
