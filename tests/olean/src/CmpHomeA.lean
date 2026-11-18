-- Task #607: a definition whose body its importers do not see (not exposed), the home of `f`
-- for the CmpHome* comparisons.
module
prelude
public import Init.Prelude
public section
def f : Nat := 3
end
