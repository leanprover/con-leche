--#export t_fun
/- End-to-end fixture (task #423 K): a K major whose indices are equal only
   up to a closure.  `fun_eq : (fun x => x + 0) = (fun x => x)` holds by
   `rfl`; the K rule's index check compares two lambdas of different code.

   Accepted (official too).  With the ground engine on, the engine's index
   comparison answers "don't know" for closures of different code ("K
   indices unknown", a completeness gap only), aborts, and the incumbent
   accepts by its own K rescue. -/

theorem fun_eq : (fun x : Nat => x + 0) = (fun x => x) := rfl

noncomputable def kFun : Bool :=
  @Eq.rec (Nat → Nat) (fun x => x + 0) (fun _ _ => Bool) true (fun x => x) fun_eq

theorem t_fun : kFun = true := rfl
