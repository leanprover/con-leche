--#export UT.rec UT.rec_1 UT.rec_2 UT.rec_3

/- Corner case (lane NESTIND, session 15, the class induction's UNREACHED
   phase — coordinator's ruling (a)): nesting through ONE member `UC1` of a
   mutual container group whose other members `UC2`/`UC3` the block never
   reaches, and which CALL EACH OTHER (`UC2.mk : UC3 α → UC2 α`,
   `UC3.mk : UC2 α → UC3 α`).  Official copies the whole group and
   generates `UT.rec_2`/`UT.rec_3` on `UC2 UT`/`UC3 UT`; their rules call
   one another, never a reached class, so the unreached phase's induction
   must be JOINT over the group mates (the recorded clause's own
   induction at the true frame).  Official 0. -/
mutual
inductive UC1 (α : Type) where
  | mk : α → UC1 α
inductive UC2 (α : Type) where
  | nil : UC2 α
  | mk : UC3 α → UC2 α
inductive UC3 (α : Type) where
  | mk : UC2 α → UC3 α
end
inductive UT where
  | leaf : UT
  | mk : UC1 UT → UT
