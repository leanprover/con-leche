--#export T.rec T.rec_1 T.rec_2
/- RESTRICT a09: one container at TWO instantiations (`List T`, `List (List T)`). -/
inductive T where
  | mk : List T → List (List T) → T
