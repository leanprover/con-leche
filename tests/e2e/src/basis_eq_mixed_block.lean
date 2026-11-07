prelude
/-! A mutual block that declares `Eq` (with the toolchain's shape) together with a second type.
Its members' names are not the pinned `Eq` block's, so a reserved name sits in a block that is
not the pinned one: REJECT (exit 1), at the reserved names' check after the block's own checks.
Official accepts it (in a `prelude` file nothing reserves `Eq`); the reserved names are this
checker's, which reads `Eq` by its fixed meaning. -/
universe u

mutual
inductive Eq {α : Sort u} (a : α) : α → Prop where
  | refl : Eq a a
inductive EqTwin {α : Sort u} (a : α) : α → Prop where
  | refl : EqTwin a a
end
