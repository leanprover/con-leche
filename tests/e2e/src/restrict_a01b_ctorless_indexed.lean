--#export T.rec T.rec_1
/- RESTRICT a01b: the same with an INDEXED constructor-less container. -/
inductive E2 (α : Type) : Nat → Type
inductive T where
  | mk : E2 T 3 → T
