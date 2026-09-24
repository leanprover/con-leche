--#export T.rec T.rec_1
/- RESTRICT a08: a REFLEXIVE container (`W`), nested. -/
inductive W (α : Type) where
  | sup : α → (Nat → W α) → W α
inductive T where
  | mk : W T → T
