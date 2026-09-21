--#export NOr.rec NOr.rec_1

/- Corner case for the uniform route's ELIMINATION GUARD (DESIGN.md,
   amendment 2026-09-21 "the recursor check knows no motives"): a
   `Prop` block with ONE member and ONE constructor that NESTS through
   a `Prop` container.  Un-nested, `elim_only_at_universe_zero` would
   give it the large eliminator (its only field is a proposition);
   nested, official evaluates the guard on the AUX block, whose size is
   2, so `NOr` is SMALL-eliminating — `motive_1`/`motive_2` land in
   `Prop`.  Official (Lean) ACCEPTS this stream.  The forged twin
   `corner_nest_or_prop_large_bad` patches the motives to `Type` and
   must be REJECTED: at `w = 0` the `Or`-component's element is both
   `inl trivial` and `inr p`, so a large `rec_1` would have to equal
   two different minors. -/

inductive NOr : Prop where
  | mk : Or True NOr → NOr
