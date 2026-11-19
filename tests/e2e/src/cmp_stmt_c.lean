/- `--compare` on two exports (task #612): a challenge with one theorem hole.  Paired with
cmp_stmt_s (1): the solution proves another statement under the hole's name. -/

--#export h1

set_option warn.sorry false

theorem h1 : 2 + 2 = 4 := sorry
