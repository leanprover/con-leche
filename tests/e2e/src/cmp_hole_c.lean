/- `--compare` on two exports (task #612): the challenge.  Three holes — a definition and a
theorem whose values are `sorry`, and an axiom — and one definition compared as it is.
Paired with cmp_hole_s (0). -/

--#export big big_lt ax twice

set_option warn.sorry false

def big : Nat := sorry
theorem big_lt : 37 < big := sorry
axiom ax : 1 + 1 = 2
def twice (n : Nat) : Nat := n + n
