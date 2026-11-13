--#export t_acc_ctor
/- End-to-end fixture (task #423 soundness): `Acc.rec` on an explicit
   `Acc.intro` at the ground site, the constructor written in the
   theorem's type (so the elaborator does not abstract it into a theorem,
   as it does in `ground_case3`).

   Official v4.35 accepts; the nightly too (the major is a constructor).
   Con-leche: the ground engine evaluates the term: **decline (2)**, ι
   case 3 (`Acc` may be a proposition).
   Target 0; after the renovation `Acc` has no large elimination, so no
   `Bool`-valued `Acc.rec` reaches the site. -/

theorem t_acc_ctor :
    @Acc.rec Nat (fun _ _ => False) (fun _ _ => Bool) (fun _ _ _ => true) 0
      (Acc.intro 0 (fun _ h => h.elim)) = true := rfl
