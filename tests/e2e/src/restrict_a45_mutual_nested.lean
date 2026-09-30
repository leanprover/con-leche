--#export A.rec B.rec A.rec_1 A.rec_2
/- RESTRICT a45: a MUTUAL block that is also NESTED — the auxiliary recursors
   are named after the FIRST member (`A.rec_1`, `A.rec_2`). -/
mutual
inductive A where
  | mk : List B → A
inductive B where
  | mk : List A → B
  | leaf : B
end
