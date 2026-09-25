--#export TB.rec TB.rec_1

/- Corner case (lane NESTIND, ruling (D), item-9 adversarial pass): the
   container's own class occurs in a TYPE-DEPENDENT position of a called
   field, `(fun (β : Type) (_ : β) => CB α) (CB α) x`.  Official 0 (its
   auxiliary type replaces `CB TB` there too).  The class abstraction replaces
   both occurrences; the call typing (infer-only inference, then whnf) sees the
   hole.  Target 0. -/

inductive CB (α : Type) : Type where
  | nil : CB α
  | mk (x : CB α) (z : (fun (β : Type) (_ : β) => CB α) (CB α) x) : CB α
inductive TB : Type where
  | node (c : CB TB) : TB
