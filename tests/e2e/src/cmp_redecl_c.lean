/- `--compare` on two exports (task #612): a challenge with a definition `f := 3` and a theorem
hole about it.  Paired with cmp_redecl_s (0: the solution declares `f` itself, with the same
content) and cmp_attack_s (1: the solution's `f := 5`). -/

--#export f t

set_option warn.sorry false

def f : Nat := 3
theorem t : f = 3 := sorry
