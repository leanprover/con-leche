--#export R.rec R.rec_1 R.rec_2
set_option genSizeOfSpec false
set_option genInjectivity false

/- Corner case D3 of charter item 8: a phantom container
   parameter `a : List R → Nat` whose value's binder names the class
   `List R` of the family, and a recursive field reached through a
   definition `F` that reads that parameter.  Official 0.  Target 0.
   The forged twin `corner_checkdel_d_anc_bad` spells the binder
   `List ((fun x => x) R)`: official then creates two auxiliary types
   and rejects the auxiliary constructor as ill-typed; we accept it
   (an accepted superset, sound). -/

def F (α : Type) (a : α) (β : Type) : Type := β
inductive C (α : Type) (a : α) (β : Type) : Type where
  | mk (x : F α a β) : C α a β
inductive R : Type where
  | leaf : R
  | mk (l : List R) (c : C (List R → Nat) (fun _ : List R => 0) R) : R
