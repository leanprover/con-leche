/- End-to-end test source for the built-in prelude (task #191): a
   pin-certified `Nat` operation whose certificate ground is NOT in its
   own dependency closure.

   `Nat.shiftLeft`'s pinned characterization statements are spelled
   over `Nat.ble`, `Nat.sub`, the `Bool` values and `Eq`; its value
   reaches none of them (`x <<< 0 = x`, `x <<< (n+1) = (2*x) <<< n`).
   The two extra theorems pull `Nat.ble`/`Nat.sub` (and, through
   `Nat.ble`'s type, `Bool`) into the export; `Eq` is pulled in only by
   the theorem statements.  The committed fixture
   `tests/e2e/natop_before_eq.ndjson` is this raw export REORDERED by
   `scripts/mk_reorder_fixture.py Nat.shiftLeft Nat.ble Nat.sub`: the
   operation and its ground come first and `Eq` after — a valid stream
   (everything follows what it references) that the install-time
   guard `divModEnvGuard` used to decline (`unsupported Nat.div/mod
   environment (Nat.shiftLeft)`: no pinned `Eq` yet).  With the
   prelude, `Eq` (and `Bool`) are installed first, unconditionally:
   accepted, and the `rfl` exercises the certified literal fast
   path. -/

--#export shlEx bleEx subEx

theorem shlEx : Eq (Nat.shiftLeft 3 4) 48 := Eq.refl 48

theorem bleEx : Eq (Nat.ble 1 2) Bool.true := Eq.refl Bool.true

theorem subEx : Eq (Nat.sub 5 3) 2 := Eq.refl 2
