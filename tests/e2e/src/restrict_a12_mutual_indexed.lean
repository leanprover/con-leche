--#export A.rec B.rec
/- RESTRICT a12: a MUTUAL block with different index counts and a reflexive
   cross-member field. -/
mutual
inductive A : Nat → Type where
  | mk : (Nat → B) → A 0
inductive B : Type where
  | mk : A 1 → B
  | leaf : B
end
