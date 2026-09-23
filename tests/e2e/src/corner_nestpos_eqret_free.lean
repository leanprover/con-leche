--#export PEq.rec

/- Corner case, the GOOD half (lane NESTPOS, positivity through a
   BASIS container): the block `PEq` with its would-be nested occurrence
   pointed at the unrelated type `EPin`.  The forged twin
   `corner_nestpos_eqret_bad` (`scripts/mk_nestpos_bad.py`) repoints
   `EPin` to `PEq` inside `PEq`'s block, giving
   `PEq p | mk : @Eq Prop (PEq p) True → PEq p` — nesting through the PINNED basis `Eq` (two parameters, `α` and `a`): the instantiated `Eq.refl`'s result index is `PEq p`.
   Official (Lean v4.29.1, the block written in Lean) REJECTS it:
   "(kernel) invalid return type for '_nested.Eq_1.refl'".  The positivity function reads `Eq` from the
   environment like any stored inductive (no basis exclusion) and
   reaches the same verdict. -/

inductive EPin (p : Prop) : Prop where
  | pin : EPin p
inductive PEq (p : Prop) : Prop where
  | base : PEq p
  | mk : @Eq Prop (EPin p) True → PEq p
