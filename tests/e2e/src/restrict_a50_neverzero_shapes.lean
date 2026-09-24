--#export A.rec B.rec C.rec
/- RESTRICT a50: two-constructor blocks whose result sort is never zero by
   official's `is_not_zero` (`max (u+1) v`, `max u (v+1)`, `imax u (v+1)`):
   official generates LARGE eliminators; `checkBlockTail` rejects a large
   eliminator unless `Level.isNeverZero` agrees. -/
universe u v
inductive A (α : Sort u) (β : Sort v) : Sort (max (u+1) v) where
  | a : A α β
  | b : α → A α β
inductive B (α : Sort u) (β : Sort v) : Sort (max u (v+1)) where
  | a : B α β
  | b : β → B α β
inductive C (α : Sort u) (β : Sort v) : Sort (imax u (v+1)) where
  | a : C α β
  | b : β → C α β
