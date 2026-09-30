--#export SD.rec

/- Corner case (U4 on a CONTAINER constructor at the instantiation): `Subtype.mk (val : SD)
   (property : PD val)` at `Subtype (@PD SD)`, with `PD` a DEFINITION
   (`fun _ => True`).  The declared later field reads the recursive field
   `val`; its whnf (δ) does not.  Official (v4.34.0) ACCEPTS; U4 reads the frame's whnf'd telescope and accepts too (target 0).  (With
   an OPAQUE predicate official rejects — "non valid occurrence" — and so
   does the positivity walk, before U4.) -/

def PD {α : Type} (_ : α) : Prop := True

inductive SD where
  | mk (x : Subtype (@PD SD)) : SD
