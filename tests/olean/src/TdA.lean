module
prelude
-- Guards task #506: a definition of `id True`, a proposition `isPropCheap` does not see as
-- one; TdM reads it, and a record TdM reads reads TdB's theorem of its name and statement.
public import Init.Prelude
public section
set_option linter.defProp false in
def td : id True := True.intro
end
