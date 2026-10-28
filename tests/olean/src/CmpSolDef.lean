module
prelude

public import CmpBase

public section

@[expose] def g (n : Nat) : Nat := n

theorem g_eq (n : Nat) : Eq (g n) n := rfl

theorem easy : True := True.intro

end
