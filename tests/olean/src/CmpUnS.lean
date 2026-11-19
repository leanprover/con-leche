-- Task #611: a solution to CmpUnC that does not import CmpBase (`f` is no constant of its
-- closure).  The merged comparison compares every record of the challenge's closure: exit 1
-- ("f: the solution has no constant of this name").  The modular one compares the records the
-- challenge's own records read: exit 0.
module
prelude
public import Init.Prelude
public section
theorem easy : True := True.intro
end
