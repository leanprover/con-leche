--#export T.rec T.rec_1 T.rec_2
/- RESTRICT a07: nesting through a MUTUAL container group (a cycle Ev→Od→Ev
   in `nestPos`; official copies both via `get_all`). -/
mutual
inductive Ev (α : Type) where
  | z : Ev α
  | s : Od α → Ev α
inductive Od (α : Type) where
  | s : Ev α → Od α
end
inductive T where
  | mk : Ev T → T
