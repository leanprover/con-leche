--#export T.rec
/- RESTRICT a11: `let` in field domains — one hiding the block (normalised
   by whnf) and one not (kept as declared). -/
inductive T where
  | mk : (let X := T; X) → (let n := 1; Fin n) → T
  | leaf : T
