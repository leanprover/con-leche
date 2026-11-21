/- `--compare` (task #612): a solution of cmp_kind_c that declares the challenge's theorem
`triv`, no hole, as a definition: a declaration that is no hole is the solution's of the same
kind.  Exit 1. -/

--#export k k_pos triv

def k : Nat := 5
theorem k_pos : 0 < k + 1 := Nat.succ_pos k
def triv : 1 = 1 := rfl
