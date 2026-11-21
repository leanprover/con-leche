/- `--compare` (task #612): a solution of cmp_redecl_c that declares `f` itself, identically:
identical content is the same constant.  Exit 0. -/

--#export f t

def f : Nat := 3
theorem t : f = 3 := rfl
