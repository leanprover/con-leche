/- `--compare` on two exports (task #612): a challenge with a hole and a definition the
solution leaves out.  Paired with cmp_missing_s (1): a missing constant. -/

--#export m extra

set_option warn.sorry false

theorem m : 1 = 1 := sorry
def extra : Nat := 7
