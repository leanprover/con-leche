/- End-to-end fixture (task #423 soundness): the maximum `Nat` size after
   computing, at the ground site, run at `--max-nat-size=16` (arena.sh's
   E2E_FLAGS, as `nat_size_limit_*`): `2^64 * 2^64` has three limbs, so
   official's `reduce_bin_nat_op` refuses it after computing (`check_size`)
   and the declaration is rejected (official under `LEAN_NAT_MAX_SIZE=16`
   too).  The comparison is with `Bool.true`, so the engine sees it.

   The engine computes the product, finds its size over the
   bound and raises the cached core's own error (`natNumeralTooBig`):
   rejected.  Target 1. -/

--#export t_mul_refused

theorem t_mul_refused :
    Eq (Nat.ble 0 (Nat.mul 18446744073709551616 18446744073709551616)) Bool.true :=
  Eq.refl Bool.true
