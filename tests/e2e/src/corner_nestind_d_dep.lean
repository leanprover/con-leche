--#export TB.rec TB.rec_1

/- Corner case: the container's own class occurs in a TYPE-DEPENDENT
   position of a called field, `(fun (β : Type) (_ : β) => CB α) (CB α) x`.
   Official 0 (its auxiliary type replaces `CB TB` there too).  Target 0. -/

inductive CB (α : Type) : Type where
  | nil : CB α
  | mk (x : CB α) (z : (fun (β : Type) (_ : β) => CB α) (CB α) x) : CB α
inductive TB : Type where
  | node (c : CB TB) : TB
