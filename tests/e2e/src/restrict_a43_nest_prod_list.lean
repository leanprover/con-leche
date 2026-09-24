--#export T.rec T.rec_1 T.rec_2
/- RESTRICT a43: two containers, `List (α × T α)`, at a parameterised block. -/
inductive T (α : Type) where
  | mk : List (α × T α) → T α
