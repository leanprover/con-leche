--#export WT.rec WT.rec_1 WT.rec_2 WT.rec_3
-- K.53's good twin (F16): a field whose container
-- instance is a β-REDEX inside its argument.  Official's auxiliary
-- recursor for `l` is on `List ((fun _ => WR WT) Nat)` exactly (the
-- occurrence `replace_all_nested` replaced, no β-step), a DIFFERENT class
-- from `List (WR WT)` (reached through `WR`'s own field).  Official 0.
inductive WR (α : Type) : Type where
  | leaf : WR α
  | node (a : α) (cs : List (WR α)) : WR α
set_option genSizeOfSpec false in
inductive WT : Type where
  | node (r : WR WT) (l : List ((fun (_ : Type) => WR WT) Nat)) : WT
