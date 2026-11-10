--#export t_direct t_arg t_quot
/- End-to-end fixture (task #423 K): a K-like recursor on a theorem major
   whose indices are equal, at the ground site (`t =?= Bool.true`, `t`
   closed).

   * `t_direct`: `Eq.rec` on the theorem `two_add_two : 2 + 2 = 4` itself;
   * `t_arg`: the theorem application `add_comm' n 3` passed as the proof
     argument of a definition (`castB`), whose body is the `Eq.rec`;
   * `t_quot`: `Quot.recOnSubsingleton` on `Quot.mk _ 3`, whose `Quot.rec`
     is `Eq.ndrecOn (Quot.liftIndepPr1 f h q) …` (the shape of CFSG's
     `Multiset.decidableForallMultiset`).

   The K rule needs the major's type: official `to_cnstr_when_K` infers
   it, whnfs it to `@Eq α a b` and checks `a ≡ b`.  All three are
   accepted (official too).  With the ground engine on (`groundMode = 10`),
   the engine does the K step itself (the major's declared type evaluated
   on the machine, the indices compared as values) and accepts; before
   the K step it aborted with "K major" and left the comparison to the
   incumbent. -/

theorem two_add_two : 2 + 2 = 4 := rfl
theorem add_comm' (a b : Nat) : a + b = b + a := Nat.add_comm a b

noncomputable def kDirect : Bool := @Eq.rec Nat (2 + 2) (fun _ _ => Bool) true 4 two_add_two

noncomputable def castB {a b : Nat} (h : a = b) (x : Bool) : Bool :=
  @Eq.rec Nat a (fun _ _ => Bool) x b h

noncomputable def kArg (n : Nat) : Bool := castB (add_comm' n 3) (n == 2)

def qd (q : Quot (fun _ _ : Nat => True)) : Bool :=
  @decide True (Quot.recOnSubsingleton (motive := fun _ => Decidable True) q
    (fun _ => instDecidableTrue))

theorem t_direct : kDirect = true := rfl
theorem t_arg : kArg 2 = true := rfl
theorem t_quot : qd (Quot.mk _ 3) = true := rfl
