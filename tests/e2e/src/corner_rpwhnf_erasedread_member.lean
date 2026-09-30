--#export T.rec
/- Corner case (lane RP-ANNOT, finding F-RPW-1 of RPWHNF): a recursive
   field whose type δ/β-erases a read of an EARLIER recursive field,
   `K2 T x` with `x : T`, whnf `T`.  Official 0.  The recursor check types
   the call on field 2 at the abstract frame, where the earlier field's
   annotation is abstracted too (`x' : X`, `K2 X x'` well-typed), as the
   positivity check reads the constructor; with the annotation left
   concrete (`K2 X (x : T)`) it rejected ("application type mismatch").
   Ours 0 (was 1). -/
set_option genSizeOf false
set_option genInjectivity false
def K2 (β : Type) (_ : β) : Type := β
inductive T : Type where
  | leaf : T
  | mk : (x : T) → K2 T x → T
