/- Task #480: the guard of a `Prop` structure's projection, at a field whose
   type's sort is only visible after unfolding a definition.  `P : MyProp`,
   and `MyProp` unfolds to `Prop`: official's `is_prop` runs `whnf` on the
   inferred type, and so does the guard at the use (`checkGuardRows`). -/

--#export useP

def MyProp : Type := Prop

structure S (P : MyProp) : Prop where
  p : P

theorem useP (P : MyProp) (h : S P) : P := h.p
