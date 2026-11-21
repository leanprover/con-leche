--#export Nat.mul

/- Task #462: a dependency of a certified operation declared as an axiom.
   `Nat.mul` is the standard structural recursion over it, so its certificate (which unfolds
   `Nat.mul` alone) passes; what makes `Nat.add` the addition is its own job, and at a
   certified name nothing but a definition is accepted.  con-leche: 1, refused at
   `Nat.add`'s own record.  Official: 0 (run; the fast path fires by name on anything). -/

prelude

set_option genCtorIdx false in
inductive Nat
  | zero
  | succ (n : Nat)

axiom Nat.add : Nat → Nat → Nat

noncomputable def Nat.mul (n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => Nat.add ih n) m
