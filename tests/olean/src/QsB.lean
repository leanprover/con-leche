module
prelude
-- Guards task #501: QsA's `Quot.sound` in another module, and a theorem reading it.
public import QsP
public section
universe u
axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Eq (Quot.mk r a) (Quot.mk r b)
theorem qsB {α : Sort u} {r : α → α → Prop} {a b : α} (h : r a b) : Eq (Quot.mk r a) (Quot.mk r b) :=
  Quot.sound h
end
