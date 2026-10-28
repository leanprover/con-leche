module
prelude

public import Init.Prelude

public section

private def p : Nat := 4

theorem p_self : Eq (0 : Nat) 0 := let _x := p; rfl

end
