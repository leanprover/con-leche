--#export squash_rfl

/-! The released form of `Quot` (`Sort u`): a quotient of a proposition is a proposition, so
two of its elements are equal by `rfl` (proof irrelevance).  ACCEPT (exit 0), as official.
Its lifted counterpart (lean4#15023), `quot_lifted_rfl_bad`, is rejected. -/

theorem squash_rfl (s : Squash True) : s = Squash.mk True.intro := rfl
