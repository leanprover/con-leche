-- Task #607: a "solution" to CmpHomeC3 that declares CmpHomeA's `f`, body and all, itself:
-- rejected, an imported name is its home's constant, whatever its body.
module
prelude
public import Init.Prelude
public section
@[expose] def f : Nat := 3
theorem t : Eq f 3 := rfl
end
