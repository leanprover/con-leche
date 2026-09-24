--#export T.rec T.rec_1
/- RESTRICT a25: a `let` inside the container's parameter. -/
inductive T where
  | mk : List (let X := T; X) → T
