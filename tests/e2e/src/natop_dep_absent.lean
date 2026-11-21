--#export Nat.mul

/- Task #462: a certified operation whose dependency is absent.  `Nat.mul` is defined over
   an addition of its own, and `Nat.add`, which `Nat.mul`'s recurrences are stated over, is
   not stored.  The install requires every dependency stored (an absent `Nat.add` would let
   the certificate pass with nothing behind it): con-leche 2, declined at `Nat.mul`'s
   install.  Official: 0 (it certifies nothing; the fast path fires by name). -/

prelude

set_option genCtorIdx false in
inductive Nat
  | zero
  | succ (n : Nat)

noncomputable def myadd (n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) n (fun _ ih => Nat.succ ih) m

noncomputable def Nat.mul (n m : Nat) : Nat :=
  Nat.rec (motive := fun _ => Nat) Nat.zero (fun _ ih => myadd ih n) m
