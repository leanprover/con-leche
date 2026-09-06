--#export Up.pred_mk

/- End-to-end test (task #188 indexed): an INDEXED recursive `Prop`
   with ONE constructor — `Up n (n+1)` from `Up (n+1) n`, the data
   field `n` an index of the result, the recursive field a proof —
   gets the LARGE eliminator from the official kernel
   (`elim_only_at_universe_zero`).  The direct fixed-point route
   declines it positively: the squash-regime fixed point (the recursor
   at a `Prop` block eliminating into `Type`) is not modeled yet
   (DESIGN.md, task #188), as at the index-free
   `direct_fix_prop_large.lean`.  (The recursive occurrence swaps the
   indices so that the `inductive` command promotes neither to a
   parameter.) -/

inductive Up : Nat → Nat → Prop where
  | mk (n : Nat) (h : Up (Nat.succ n) n) : Up n (Nat.succ n)

noncomputable def Up.pred {a b : Nat} (h : Up a b) : Nat :=
  Up.rec (motive := fun _ _ _ => Nat) (fun n _ _ => n) h

theorem Up.pred_mk (n : Nat) (h : Up (Nat.succ n) n) : Eq (Up.pred (Up.mk n h)) n := rfl
