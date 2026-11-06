--#export Nat.mul usesAdd

/- Task #462: a dependency of a certified operation declared as a theorem.  A theorem
   cannot be `Nat.mul`'s addition (its type is a proposition), so `Nat.mul` is defined over
   an addition of its own and its recurrences, stated over `Nat.add`, do not hold.
   con-leche: 1, refused at the theorem `Nat.add`'s own record (and `Nat.mul`'s certificate
   fails).  Official: 0 (run). -/

prelude

set_option genCtorIdx false in
inductive Nat
  | zero
  | succ (n : Nat)

inductive P : Prop
  | i

theorem Nat.add : P := P.i

noncomputable def myadd (n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) n (fun _ ih => Nat.succ ih) m

noncomputable def Nat.mul (n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => myadd ih n) m

theorem usesAdd : P := Nat.add
