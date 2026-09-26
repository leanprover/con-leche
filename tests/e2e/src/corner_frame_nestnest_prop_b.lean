--#export T.rec T.rec_1 T.rec_2

/- Corner case (lane FRAME, PRIMREC S4): nested-in-nested at `Prop` with a
   depth-2 frame whose field needs the SECOND stage of the rec check's
   field normal form: `C`'s field `Bool.rec True α b` is stuck on the
   parameter `b` at `C`'s canonical reading and reduces to `α` only at
   the instance `b := true`, where `α` is `W T` — `W`'s frame hole in the
   walk's representation.  Official 0.  Target 0. -/

inductive C (b : Bool) (α : Prop) : Prop where
  | mk : Bool.rec True α b → C b α
inductive W (β : Prop) : Prop where
  | w : C true (W β) → β → W β
inductive T : Prop where
  | mk : W T → T
