-- Task #607: a "solution" to CmpHomeC that declares an `f` of its own instead of importing
-- CmpHomeA's: rejected, `f`'s home differs.
module
prelude
public import Init.Prelude
public section
@[expose] def f : Nat := 5
theorem t : Eq f 5 := rfl
end
