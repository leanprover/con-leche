--#export T.rec T.rec_1
/- RESTRICT a14: universe-polymorphic block nested through `List.{u}`. -/
universe u
inductive T : Type u where
  | mk : List T → T
