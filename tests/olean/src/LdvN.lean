module

-- (task #465) reads LdvA's group and not `ldvW`, the definition its
-- constructor's type reads.  With LdvA's import of LdvQ made private
-- (tests/olean.sh), the reach completes `ldvW` as the axiom of its statement:
-- the group is presented whole, never checked here, so nothing unfolds it.
import LdvA

theorem ldvN (x : LdvB) : x = x := rfl
