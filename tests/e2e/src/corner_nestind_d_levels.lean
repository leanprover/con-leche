--#export TR.rec TR.rec_1 TR.rec_2 TR.rec_3

/- Corner case (lane NESTIND, ruling (D), item-9 adversarial pass): two
   nesting levels (`RR TR`, `List (RR TR)`) and a container nested in
   itself (`List (List TR)`, whose parameter is another class of the family).
   Official 0.  Target 0. -/

inductive RR (α : Type) : Type where
  | node (a : α) (cs : List (RR α)) : RR α
inductive TR : Type where
  | leaf : TR
  | mk (r : RR TR) (l : List (List TR)) : TR
