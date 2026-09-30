--#export UT.rec

/- Corner case, the GOOD half (the closure witness (W) for nested
   blocks): the block `UT` with its would-be nested occurrence
   pointed at the unrelated type `UPin` — an ordinary, non-nested block
   every checker accepts.  The forged twin `corner_nestw_u4_bad`
   (`scripts/mk_nestw_bad.py`) writes the field's `a.2` as the raw
   projection `.proj Prod 1 a` (Lean elaborates `Prod.snd a`, which no
   later field could read without naming the member) and repoints `UPin`
   to `UT` inside `UT`'s block, giving a LATER FIELD THAT READS A NESTED
   FIELD'S VALUE: `mk (a : Prod UT Nat) (b : Fin a.2)`.
   Official (Lean v4.33.0, the declaration added through the kernel)
   REJECTS it: "(kernel) invalid projection a.2" — its auxiliary type
   replaces `Prod UT Nat`, so `a.2` projects `Prod` out of it. -/

inductive UPin where
  | pin : UPin
inductive UT where
  | mk : (a : Prod UPin Nat) → Fin a.2 → UT
