module
prelude

public import CmpBase

public section

@[expose] def g (n : Nat) : Nat := f n

theorem g_eq (n : Nat) : Eq (g n) n := rfl

end
