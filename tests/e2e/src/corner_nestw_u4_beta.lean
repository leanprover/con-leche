--#export UB.rec

/- Corner case (U4 at NESTED fields): a later field whose DECLARED type mentions the nested
   field `xs : List UB`, but only inside a β-redex that whnf drops —
   `(fun _ : List UB => Nat) xs` is `Nat`.  Official (v4.34.0) ACCEPTS:
   its auxiliary type replaces `List UB` inside the λ's domain too, so the
   redex type-checks at the auxiliary type.  U4 reads the
   positivity function's NORMAL FORM (whnf'd fields), where no field reads
   `xs`, so it accepts too (target 0). -/

inductive UB where
  | mk (xs : List UB) (h : (fun (_ : List UB) => Nat) xs) : UB
