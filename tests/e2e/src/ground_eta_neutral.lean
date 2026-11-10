--#export t_prod t_wrap
/- End-to-end fixture (task #423 completeness): structure η in ι at a
   closed neutral major.  `Classical.choice` gives closed terms of a
   structure type that no reduction opens; official's
   `to_cnstr_when_structure` (the incumbent's η rescue) expands the
   major into its projections, so `Prod.rec`/`Wrap.rec` with a constant
   minor reduce to `true`.

   Accepted (official too).  With the ground engine on (`groundMode =
   10`), the engine does the η step itself: the constructor on the
   recursor's parameters and the major's (stuck) projections; before,
   it aborted with "struct-eta major" and the incumbent did the work. -/

noncomputable def p : Nat × Nat := Classical.choice ⟨(0, 0)⟩
noncomputable def kProd : Bool := Prod.rec (motive := fun _ => Bool) (fun _ _ => true) p

structure Wrap where
  n : Nat
  b : Bool

noncomputable def w : Wrap := Classical.choice ⟨⟨0, true⟩⟩
noncomputable def kWrap : Bool := Wrap.rec (motive := fun _ => Bool) (fun _ _ => true) w

theorem t_prod : kProd = true := rfl
theorem t_wrap : kWrap = true := rfl
