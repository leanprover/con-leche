/- End-to-end fixture (task #423 soundness): the maximum `Nat` size before
   computing, `Nat.pow` by size (not by its 32-bit exponent bound, which
   `ground_nat_pow_refused` covers), at the ground site, run at
   `--max-nat-size=16` (arena.sh's E2E_FLAGS): `2 ^ 200` would exceed it,
   rejected (official under `LEAN_NAT_MAX_SIZE=16` too).

   Engine on: the engine's refusal before computing raises the cached
   core's own error (`natOpRefusal`): rejected.  Today 1; target 1. -/

--#export t_pow_size_refused

theorem t_pow_size_refused : Eq (Nat.ble 0 (Nat.pow 2 200)) Bool.true := Eq.refl Bool.true
