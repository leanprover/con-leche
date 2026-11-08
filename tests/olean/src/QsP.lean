module
prelude
-- Guards task #501: `Eq` and the quotient, without `Quot.sound`.
public section
universe u
inductive Eq : {α : Sort u} → α → α → Prop where
  | refl (a : α) : Eq a a
init_quot
end
