--#export LocT.rec

/- Corner case, the GOOD half (lane NESTPOS, positivity through
   containers): the block `LocT` with its would-be nested occurrence
   pointed at the unrelated type `LPin` — an ordinary, non-nested
   block every checker accepts.  The forged twin
   `corner_nestpos_local_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `LPin` to `LocT` inside `LocT`'s block, giving
   a container PARAMETER that mentions a field: `Prod LocT (Fin n)` with `n` the constructor's own field.
   Official (Lean v4.29.1 and v4.34.0, the block written in Lean)
   REJECTS it: "(kernel) invalid nested inductive datatype 'Prod', nested inductive datatypes parameters cannot contain local variables.". -/

inductive LPin where
  | pin : LPin
inductive LocT where
  | leaf : LocT
  | mk : (n : Nat) → Prod LPin (Fin n) → LocT
