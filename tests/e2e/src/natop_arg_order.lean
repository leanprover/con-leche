--#export w1
/-! Witness D15 (reduce_nat argument order): official `reduce_bin_nat_op`
whnf's the FIRST argument and bails when it is not a literal, never
touching the second; lech's `reduceNat` whnf's both before matching.
`o` is opaque so the first argument never becomes a literal; the second is
an expensive closed computation that only lech evaluates on this defeq. -/
opaque o : Nat
def loop : Nat → Nat → Nat
  | 0, acc => acc
  | n+1, acc => loop n (acc + 1)
def slow (n : Nat) : Nat := loop n 0
theorem w1 : Nat.add o (slow 80000) = Nat.add (id o) (slow 80000) := rfl
