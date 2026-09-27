--#export AT.rec AT.rec_1

/- PRIMREC/NESTHOME: a `Prop` block nested in `And` — official's
   auxiliary recursor for `And AT AT` beside `AT.rec`, a cycle through the
   member (the hot layer `{AT.rec, AT.rec_1}`).  Official 0.  Target 0:
   checked off the walk against the home table. -/

inductive AT : Prop where
  | leaf : AT
  | node (h : And AT AT) : AT
