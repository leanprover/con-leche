/- `--compare` (task #619): a hole whose type reads a universe-polymorphic inductive type.
Paired with cmp_lvind_s (1): the solution declares the block at other level-parameter names;
a constructor or recursor is matched only at its own names (ι reads them so), so the block is
not the challenge's. -/

--#export Box box_self

set_option warn.sorry false

universe u

inductive Box (α : Sort u) where
  | mk : α → Box α

theorem box_self (b : Box Nat) : b = b := sorry
