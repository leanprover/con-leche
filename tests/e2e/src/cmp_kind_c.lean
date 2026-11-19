/- `--compare` on two exports (task #612): a challenge with a definition hole, a theorem hole
and a theorem compared as it is.  Paired with cmp_kind_s (0) and cmp_kind_bad_s (1). -/

--#export k k_pos triv

set_option warn.sorry false

def k : Nat := sorry
theorem k_pos : 0 < k + 1 := sorry
theorem triv : 1 = 1 := rfl
