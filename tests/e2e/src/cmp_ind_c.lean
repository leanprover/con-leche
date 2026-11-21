/- `--compare` on two exports (task #612): a challenge with an inductive type of two
constructors and a hole that is false of it.  Paired with cmp_ind_s (1): the solution's type has
one constructor. -/

--#export T t

set_option warn.sorry false

inductive T | a | b
theorem t : ∀ x : T, x = T.a := sorry
