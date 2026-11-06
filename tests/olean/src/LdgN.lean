module

-- (task #465) reads LdgA's group and not `ldgT`, which its constructor's type
-- reads.  With LdgA's import of LdgQ made private (tests/olean.sh patches the
-- header), N's view lacks `ldgT`: the reach completes it, located in LdgA's
-- view and read from LdgQ's private part as its statement; with the import
-- dropped, it is located nowhere, a reject.
import LdgA

theorem ldgN (x : LdgB) : x = x := rfl
