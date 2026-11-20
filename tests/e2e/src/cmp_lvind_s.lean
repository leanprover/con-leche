/- `--compare` (task #619): cmp_lvind_c's block at other level-parameter names (1). -/

--#export Box box_self

universe w

inductive Box (α : Sort w) where
  | mk : α → Box α

theorem box_self (b : Box Nat) : b = b := rfl
