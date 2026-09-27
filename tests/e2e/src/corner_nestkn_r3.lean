--#export T.rec T.rec_1 T.rec_2
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named positivity, R3 (lane PRIMREC/NESTKN, PROOFPLAN §3.3): a
   contained key that NESTS the using node's own key below the outermost
   key, at a position whose container's INDICES depend on it.  `C' α` is
   indexed by `List α`; the older nested type `G α` mentions `C' (G α)`
   only at a PHANTOM value parameter of `Ph` (official creates no auxiliary type
   for it: `Ph.mk` has no field).  The new block nests `T` in `G`; node
   `G T`'s crest has the child `Ph (C' (G T))`, whose contained key
   `C' (G T)` is flexible by typing and never met.  At the site the
   family's binding `C' (y_G T)` has type `List (y_G T) → Type`, not the
   family's declared `List (G T) → Type` — unless the inner key `G T` is
   itself a (flexible) family and the outer family's type is stated over
   it (the "all depths, inner-first" contained keys).  Official 0.  Today 0.
   Target 0. -/

inductive C' (α : Type) : List α → Type where
  | mk : C' α []
inductive Ph (γ : Type 1) (b : γ) : Type where
  | mk : Ph γ b
inductive G (α : Type) : Type where
  | leaf : G α
  | node (p : Ph (List (G α) → Type) (C' (G α))) : G α
inductive T : Type where
  | leaf : T
  | mk (g : G T) : T
