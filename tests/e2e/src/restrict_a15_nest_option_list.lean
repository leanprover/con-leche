--#export T.rec T.rec_1 T.rec_2
/- RESTRICT a15: a container inside a container's parameter (`Option (List T)`). -/
inductive T where
  | mk : Option (List T) → T
