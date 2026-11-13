--#export t_prod t_wrap
/- End-to-end fixture (task #423 completeness): structure η in ι at a
   closed neutral major.  `Classical.choice` gives closed terms of a
   structure type that no reduction opens; official's
   `to_cnstr_when_structure` (the incumbent's η rescue) expands the
   major into its projections, so `Prod.rec`/`Wrap.rec` with a constant
   minor reduce to `true`.

   Official accepts.  The ground engine evaluates the comparison, with no
   fallback to the incumbent.  Task #423 soundness (ruling 4): structure
   η on a stuck major needs the major's type (`Red.rescueEta`), which the
   engine does not compute, so this is a decline (2), naming `Prod.rec`.
   Target 0. -/

noncomputable def p : Nat × Nat := Classical.choice ⟨(0, 0)⟩
noncomputable def kProd : Bool := Prod.rec (motive := fun _ => Bool) (fun _ _ => true) p

structure Wrap where
  n : Nat
  b : Bool

noncomputable def w : Wrap := Classical.choice ⟨⟨0, true⟩⟩
noncomputable def kWrap : Bool := Wrap.rec (motive := fun _ => Bool) (fun _ _ => true) w

theorem t_prod : kProd = true := rfl
theorem t_wrap : kWrap = true := rfl
