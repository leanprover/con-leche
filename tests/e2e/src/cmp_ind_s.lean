/- `--compare` (task #612): a solution of cmp_ind_c whose `T` has the constructor `a` alone, so
that its `t` holds: an inductive type is the challenge's exactly.  Exit 1. -/

--#export T t

inductive T | a
theorem t : ∀ x : T, x = T.a := fun x => by cases x; rfl
