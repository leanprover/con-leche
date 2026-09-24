--#export V.rec
/- RESTRICT a10: DEPENDENT index telescope (`Fin n` depends on `n`) at a
   recursive block — the recursor's index domains vs the member's
   (`openPisParamsIdx`, SEC2). -/
inductive V : (n : Nat) → Fin n → Type where
  | leaf : (n : Nat) → (i : Fin n) → V n i
  | node : (n : Nat) → (i : Fin n) → V n i → V n i
