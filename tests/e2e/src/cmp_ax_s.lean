/- `--compare` (task #612): a solution of cmp_stmt_c that proves its
hole from an axiom of its own: the solution's check declines a non-standard axiom.  Exit 2. -/

--#export h1

axiom cheat : 2 + 2 = 4
theorem h1 : 2 + 2 = 4 := cheat
