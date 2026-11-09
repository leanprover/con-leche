/- End-to-end test, ported from lean4's
   `tests/elab/nat_size_limit.lean` (lean4#14849), run at
   `--max-nat-size=16` as that test runs at `LEAN_NAT_MAX_SIZE=16` (arena.sh's
   E2E_FLAGS): `2 ^ 4294967296`: the exponent does not fit in 32 bits,
   rejected. The export itself, at the placeholder exponent 206 (the
   elaborator would not compute the real one), is rejected as over
   maxNatSize; `scripts/mk_nat_size_fixtures.py` derives
   `nat_size_limit_pow_32bit.ndjson` from it, the exponent replaced. -/

--#export powHugeExp

theorem powHugeExp : Eq (Nat.ble (Nat.pow 2 206) 0) Bool.false := Eq.refl Bool.false
