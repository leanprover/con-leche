--#export XW.rec XW.rec_1 XW.rec_2 XW.rec_3 XW.rec_4

/- Corner case (classes UNREACHED from the block, F13's shape): the block `XW` nests through `XF`, a member of a
   mutual group whose other member `XT` is itself nested exactly as F13's
   `TL` (`XT.node : List (XR (XT α)) → XT α`, `XR β ::= node β (List (XR β))`).
   Official copies `XF`'s whole group and every nested occurrence inside
   the copies, generating recursors on `XT XW`, `List (XR (XT XW))` and
   `XR (XT XW)` — unreached from `XW`'s members, and `List (XR (XT XW))`
   is entered both from `XT XW` (outside its ancestor `XR (XT XW)`) and
   from `XR (XT XW)`: the unreached classes need the nesting ORDER of a
   visit structure (F13).  Official 0. -/
inductive XR (β : Type) where
  | node : β → List (XR β) → XR β
mutual
inductive XT (α : Type) where
  | node : List (XR (XT α)) → XT α
inductive XF (α : Type) where
  | mk : α → XF α
end
inductive XW where
  | leaf : XW
  | mk : XF XW → XW
