--#export Q.rec
/- RESTRICT a16: a `Prop` family whose one constructor has a non-Prop field
   occurring in the result index — official's subsingleton criterion grants
   a LARGE eliminator. -/
inductive Q : Nat → Prop where
  | mk : (n : Nat) → True → Q n
