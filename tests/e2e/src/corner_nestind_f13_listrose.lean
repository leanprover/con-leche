--#export TL.rec TL.rec_1 TL.rec_2

/- Corner case (DESIGN F13): a block entering a nested
   container through ANOTHER container — `TL ::= node (List (RL TL))`
   with `RL α ::= node α (List (RL α))`.  The class `List (RL TL)` is
   reached twice at different nesting depths: first at the block's field
   (its parameter position holding `RL`'s carrier at the block's
   separated tuple), then again under `RL TL` (its parameter position
   holding `RL`'s own separated tuple).  A nested kit whose depth is one
   number PER CLASS cannot order these visits.  Official 0.  Target 0. -/

inductive RL (α : Type) : Type where
  | node (a : α) (cs : List (RL α)) : RL α
inductive TL : Type where
  | node (l : List (RL TL)) : TL
