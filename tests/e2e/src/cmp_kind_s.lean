/- `--compare` (task #612): a solution of cmp_kind_c whose holes are filled by other kinds: the
definition hole by an opaque constant, the theorem hole by a definition.  A hole is filled by
any constant of its name and type.  Exit 0. -/

--#export k k_pos triv

opaque k : Nat := 5
def k_pos : 0 < k + 1 := Nat.succ_pos k
theorem triv : 1 = 1 := rfl
