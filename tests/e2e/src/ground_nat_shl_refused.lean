/- End-to-end fixture (task #423 soundness): the maximum `Nat` size before
   computing, `Nat.shiftLeft`, at the ground site, run at
   `--max-nat-size=16` (arena.sh's E2E_FLAGS): `1 <<< 200` would exceed
   it, so official's `reduce_shiftLeft` refuses before computing, rejected
   (official under `LEAN_NAT_MAX_SIZE=16` too).

   The engine's refusal before computing raises the cached
   core's own error (`natOpRefusal`): rejected.  Target 1.
   (`subHelper` pulls in `Nat.sub`, which `Nat.shiftLeft`'s pinned
   environment needs, as in `nat_size_limit_shift_big`.) -/

--#export t_shl_refused subHelper

theorem t_shl_refused : Eq (Nat.ble 0 (Nat.shiftLeft 1 200)) Bool.true := Eq.refl Bool.true
theorem subHelper : Eq (Nat.sub 9 4) 5 := Eq.refl 5
