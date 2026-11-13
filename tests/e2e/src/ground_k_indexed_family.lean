--#export t_double t_pair t_heq
/- End-to-end fixture (task #423 K): K-like families with indices beyond
   `Eq`'s.

   * `IsDouble n : Nat → Prop`, one constructor `mk : IsDouble n (n + n)`,
     at `3, 6`;
   * `PairSwap p : Nat × Nat → Prop`, `mk : PairSwap p (p.2, p.1)`: the
     index is a constructor value;
   * `HEq`: the indices are a type and a value of that type.

   All accepted (official too).  With the ground engine, all three are
   decided by the engine's K step, which reads neither the major nor the
   indices. -/

inductive IsDouble (n : Nat) : Nat → Prop
  | mk : IsDouble n (n + n)

theorem d3 : IsDouble 3 6 := IsDouble.mk

noncomputable def kDouble : Bool := @IsDouble.rec 3 (fun _ _ => Bool) true 6 d3

inductive PairSwap (p : Nat × Nat) : Nat × Nat → Prop
  | mk : PairSwap p (p.2, p.1)

theorem ps : PairSwap (1, 2) (2, 1) := PairSwap.mk

noncomputable def kPair : Bool := @PairSwap.rec (1, 2) (fun _ _ => Bool) true (2, 1) ps

theorem heq1 : HEq (1 : Nat) (1 : Nat) := HEq.rfl

noncomputable def kHEq : Bool := @HEq.rec Nat 1 (fun {_} _ _ => Bool) true Nat 1 heq1

theorem t_double : kDouble = true := rfl
theorem t_pair : kPair = true := rfl
theorem t_heq : kHEq = true := rfl
