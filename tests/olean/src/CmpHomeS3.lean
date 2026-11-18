-- Task #607: a solution to CmpHomeC3 that imports CmpHomeA, `f`'s home, and unfolds `f` (a
-- module outside the module system sees every body): accepted.
prelude
import Init.Prelude
import CmpHomeA
theorem t : Eq f 3 := rfl
