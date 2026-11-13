--#export t_punit0
/- End-to-end fixture (task #423 soundness): ι at `PUnit.rec` on
   `PUnit.{0}` (a proposition there), at the ground site, with the
   constructor written in the theorem's type.

   Official accepts.  Con-leche: the ground engine evaluates the term;
   `PUnit.rec` is not K-flagged (`PUnit` is not always a proposition), so
   at `PUnit.{0}` the rule is case 3 of the ι split: **decline (2)** (no
   proved rule without the constructor certificates).  Target 0; after the
   kernel renovation a may-be-`Prop` family with one field-less
   constructor large-eliminates by the K-like path, which needs no
   certificate. -/

theorem t_punit0 : @PUnit.rec.{1, 0} (fun _ => Bool) true PUnit.unit = true := rfl
