/- `--compare` on two exports (task #612): the attack on the home rule, in an export.  The
challenge holds `f := 3` itself and asks for `t : f = 5`, which is false.  Paired with
cmp_attack_s (1): a solution with its own `f := 5` differs from the challenge's `f` in content. -/

--#export f t

set_option warn.sorry false

def f : Nat := 3
theorem t : f = 5 := sorry
