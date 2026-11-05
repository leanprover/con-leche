--#export Char.rec
/- A family a literal's meaning reads, stored at a definition: its declared type is not the shape
   `litShapeOk` reads, so this declines at the declaration.  `Bool` no longer does
   (`ind_defhead_lit_family`).  Reading the shape off the reduct would need the literal's proofs to read
   the family through its declared former; nothing else stops it.
   official: 0.  con-leche: 2. -/
prelude

def T := Type

inductive Char : T
  | mk
