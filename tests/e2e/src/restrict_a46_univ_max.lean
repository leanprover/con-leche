--#export T.rec T.rec_1
/- RESTRICT a46: the container at a LEVEL EXPRESSION (`List.{max u v}`). -/
universe u v
inductive T : Type (max u v) where
  | mk : List T → T
