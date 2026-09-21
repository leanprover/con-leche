--#export RRefl.big

/- Corner case: LARGE elimination from a `Prop` block IS allowed by the
   official kernel when the block has one member, one constructor and
   every field is a proposition — here the REFLEXIVE field
   `Nat → RRefl`, whose sort `imax 1 0` normalises to zero, so
   `elim_only_at_universe_zero` puts nothing in `to_check` and returns
   false.  `RRefl.rec` therefore eliminates into `Sort u` and
   `RRefl.big` uses it at `Type`.  Official ACCEPTS.  (The index-free
   non-reflexive twin of this shape is `direct_fix_prop_large`
   (`Loop | mk (h : Loop)`), the indexed one `direct_fix_acc_large`;
   this one adds the reflexive field, i.e. the squash regime with an
   inductive hypothesis that is a FUNCTION.) -/

inductive RRefl : Prop where
  | mk : (Nat → RRefl) → RRefl

noncomputable def RRefl.big (h : RRefl) : Type :=
  RRefl.rec (motive := fun _ => Type) (fun _ ih => ih Nat.zero) h
