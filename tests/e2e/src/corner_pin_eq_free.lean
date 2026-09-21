--#export EFree.rec

/- Corner case, the GOOD half: a field whose type is an `Eq`
   application that does NOT mention the block.  `Eq`'s only parameter
   is `α`; both sides are INDEX arguments, so even when they mention
   the member there is no nested occurrence for official to find — the
   field whnf's to `Eq …`, which is not a member application, and the
   block is rejected ("non valid occurrence").  That is what the forged
   twin `corner_pin_eq_bad` does, by repointing `False` to the member
   `EFree`. -/

inductive EFree : Prop where
  | mk : @Eq Prop False False → EFree
