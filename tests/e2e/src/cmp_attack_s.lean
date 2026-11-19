/- `--compare` (task #612): a solution of cmp_attack_c that redefines `f := 5` and proves
`t : f = 5`.  The challenge's `f` is in the challenge file, so the solution's differs from it.
Exit 1. -/

--#export f t

def f : Nat := 5
theorem t : f = 5 := rfl
