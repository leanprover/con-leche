/- `--compare` (task #612): a solution of cmp_hole_c: the holes filled, by a definition, a
theorem and a theorem for the axiom; `twice` as the challenge has it.  Exit 0. -/

--#export big big_lt ax twice

def big : Nat := 38
theorem big_lt : 37 < big := by decide
theorem ax : 1 + 1 = 2 := rfl
def twice (n : Nat) : Nat := n + n
