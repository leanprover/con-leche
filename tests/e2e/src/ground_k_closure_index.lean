--#export t_fun
/- End-to-end fixture (task #423 K): a K major whose indices are equal only
   up to a closure.  `fun_eq : (fun x => x + 0) = (fun x => x)` holds by
   `rfl`; the K rule's index check compares two lambdas of different code.

   Accepted (official too: its index check compares the two lambdas by
   defeq).  The ground engine's K step does not look
   at the indices and accepts. -/

theorem fun_eq : (fun x : Nat => x + 0) = (fun x => x) := rfl

noncomputable def kFun : Bool :=
  @Eq.rec (Nat → Nat) (fun x => x + 0) (fun _ _ => Bool) true (fun x => x) fun_eq

theorem t_fun : kFun = true := rfl
