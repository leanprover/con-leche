--#export T.rec T.rec_1 T.rec_2
/- RESTRICT a32: a PARTIALLY applied container inside a parameter (`F (Vec T)`,
   `Vec T : Nat → Type`); the instance itself is fully applied. -/
inductive Vec (α : Type) : Nat → Type where
  | nil : Vec α 0
  | cons : {n : Nat} → α → Vec α n → Vec α (n+1)
inductive F (G : Nat → Type) : Type where
  | mk : G 0 → F G
inductive T where
  | mk : F (Vec T) → T
