module
prelude
-- Guards task #501: `Quot.sound` declared again over QsP's quotient (QsB declares it too).
public import QsP
public section
universe u
axiom Quot.sound : ∀ {α : Sort u} {r : α → α → Prop} {a b : α}, r a b → Eq (Quot.mk r a) (Quot.mk r b)
end
