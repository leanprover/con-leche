--#export QFree.rec

/- Corner case, the GOOD half: a field whose type is a `Quot`
   application that does NOT mention the block.  `Quot` is not an
   `inductive` in the official kernel (`is_nested_inductive_app`
   requires `is_inductive()`), so this is an ordinary opaque field and
   official ACCEPTS.  The forged twin `corner_pin_quot_bad` repoints
   the pin `Nat` to the member `QFree` itself, which official REJECTS
   ("non valid occurrence") — the ruling of 2026-09-21: nesting
   through a basis block is a REJECT, not a decline. -/

inductive QFree where
  | mk : Quot (fun (_ _ : Nat) => True) → QFree
