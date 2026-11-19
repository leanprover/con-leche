/- `--compare` on two exports (task #612): a challenge with a definition compared as it is and
a theorem hole about it.  Paired with cmp_def_s (1): the solution's definition differs. -/

--#export g g_pos

set_option warn.sorry false

def g (n : Nat) : Nat := n + 1
theorem g_pos : 0 < g 0 := sorry
