--#export T.rec T.rec_1
/- RESTRICT a04: the block's PARAMETER as a container index; key ds mentions
   the parameter variable. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n+1)
inductive T (m : Nat) where
  | mk : Vec (T m) m → T m
