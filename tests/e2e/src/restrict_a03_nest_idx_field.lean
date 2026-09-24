--#export T.rec T.rec_1
/- RESTRICT a03: container index is an EARLIER FIELD (`Vec T n`, `n` a field):
   K5 (call index args) and `nestCont`'s local-variable check on params only. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n+1)
inductive T where
  | mk : (n : Nat) → Vec T n → T
