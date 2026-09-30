--#export T.rec T.rec_1
/- RESTRICT a06: a REFLEXIVE nested field `Nat → List T`. -/
inductive T where
  | mk : (Nat → List T) → T
