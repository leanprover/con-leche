/- `--compare` (task #612): a solution of cmp_lv_c at other level-parameter names: the
comparison is up to a renaming of level parameters.  Exit 0. -/

--#export idd idd_eq

universe w x

def idd {α : Sort w} (a : α) : α := a
theorem idd_eq {α : Sort x} (a : α) : idd a = a := rfl
