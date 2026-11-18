-- Task #607: a solution to CmpHomeC3 that imports CmpHomeA, `f`'s home, and proves the hole
-- through `f`'s body (`import all`): accepted.  An exported theorem may not be a term `rfl`
-- unfolding the unexposed `f` (an rfl-theorem), but `(rfl)` is no rfl-theorem.
module
prelude
public import Init.Prelude
public import CmpHomeA
import all CmpHomeA
public theorem t : Eq f 3 := (rfl)
