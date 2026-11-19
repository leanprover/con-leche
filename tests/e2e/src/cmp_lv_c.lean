/- `--compare` on two exports (task #612): a challenge with universe-polymorphic declarations, a
definition compared as it is and a theorem hole.  Paired with cmp_lv_s (0): the solution names
the level parameters differently. -/

--#export idd idd_eq

set_option warn.sorry false

universe u v

def idd {α : Sort u} (a : α) : α := a
theorem idd_eq {α : Sort v} (a : α) : idd a = a := sorry
