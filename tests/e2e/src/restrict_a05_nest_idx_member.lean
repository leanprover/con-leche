--#export T.rec T.rec_1
/- RESTRICT a05: the member applied to an INDEX inside the container's
   parameter (`List (T 0)`), the key's ds = the hole applied. -/
inductive T : Nat → Type where
  | base : T 0
  | mk : List (T 0) → T 1
