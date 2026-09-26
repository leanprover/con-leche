--#export TLP.rec TLP.rec_1 TLP.rec_2

/- Corner case (DESIGN F13), the `Prop` twin of
   `corner_nestind_f13_listrose` (`w = 0`: every value is the point, so
   no ∈-rank can order the visits either).  Official 0.  Target 0. -/

inductive PLF (α : Prop) : Prop where
  | cons (h : α) (t : PLF α) : PLF α
  | nil : PLF α
inductive RLP (α : Prop) : Prop where
  | node (a : α) (cs : PLF (RLP α)) : RLP α
inductive TLP : Prop where
  | node (l : PLF (RLP TLP)) : TLP
