/- `--compare` (task #612): a solution of cmp_def_c whose `g` is another definition: a
declaration that is no hole is the solution's, value and all.  Exit 1. -/

--#export g g_pos

def g (n : Nat) : Nat := n + 2
theorem g_pos : 0 < g 0 := by decide
