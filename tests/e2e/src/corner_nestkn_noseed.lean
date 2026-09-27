--#export T.rec T.rec_1 T.rec_2

/- Corner case (lane PRIMREC/NESTKN-R): a nested cycle that does NOT run
   through the block's members.  `T | mk : A (B T) → T` nests through
   `A α | mk : B (A α) → A α`; official's auxiliary types are `A (B T)` and
   `B (A (B T))`, whose recursors call EACH OTHER and never `T` — so their
   component of the call graph holds no member class, and each class's
   parameters name the other's inductive.  The recursor check's nested
   route must reach them from `T`'s call (an edge INTO the component), not
   from a member of the component.  Official 0. -/
inductive B (β : Type) where
  | mk : β → B β

inductive A (α : Type) where
  | mk : B (A α) → A α

inductive T where
  | mk : A (B T) → T
