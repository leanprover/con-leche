--#export T.rec T.rec_1

/- Corner case (lane FRAME, PRIMREC): a container's field whose whnf at
   the container's CANONICAL reading goes through the structure-η rescue
   of `PProd.rec` at the parameter `p` (index `p.2`, a projection of the
   parameter), while at the instance `p := ⟨T, 4⟩` it takes the natural
   ι step (index `4`).  Official's auxiliary recursor calls the class
   `C ⟨T, 4⟩` at index `4` (one-stage whnf at the instance).  A two-stage
   field normal form (whnf at the canonical reading, then instantiate)
   yields index `⟨T, 4⟩.2`; a syntactic K.53 at the index would reject
   official's recursor.  Official 0.  Target 0. -/

inductive C (p : PProd Prop Nat) : Nat → Prop where
  | mk : PProd.rec (motive := fun _ => Prop) (fun _ b => C p b) p → C p 0
inductive T : Prop where
  | mk : C ⟨T, 4⟩ 0 → T
