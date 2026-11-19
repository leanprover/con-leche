-- Task #611: a solution to CmpUnC that does not import CmpBase (`f` is no constant of its
-- closure).  Every mode compares the challenge's own records and what they read, and `easy`
-- reads nothing of CmpBase (task #614): exit 0, in the merged mode as in the modular ones
-- (task #611 found the merged comparison rejecting it, "f: no constant of this name").
module
prelude
public import Init.Prelude
public section
theorem easy : True := True.intro
end
