--#export R.rec R.rec_1 R.rec_2
set_option genSizeOfSpec false
set_option genInjectivity false

/- Corner case: `corner_checkdel_d_anc` with the container
   field that reads the phantom parameter `a` NON-recursive
   (`y : F α a Nat`); the recursive field is `x : β`.  Official 0.
   Target 0.  The forged twin `corner_checkdel_d_anc_nocall_bad` spells the
   binder `List ((fun x => x) R)`: official rejects it (two auxiliary
   types, an ill-typed auxiliary constructor); we accept it (charter
   item 8, D3). -/

def F (α : Type) (a : α) (β : Type) : Type := β
inductive C (α : Type) (a : α) (β : Type) : Type where
  | mk (y : F α a Nat) (x : β) : C α a β
inductive R : Type where
  | leaf : R
  | mk (l : List R) (c : C (List R → Nat) (fun _ : List R => 0) R) : R
