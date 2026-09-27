--#export R.rec R.rec_1 R.rec_2
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named frame holes (lane PRIMREC/KEYNAMED): the class `List R`
   occurs in the container key's PARAMETERS (the binder of the value
   `a := fun _ : List R => 0`, a contained key) AND is built by the
   container's CONSTRUCTOR from its parameter (`F (List β) a β` at
   `β := R`), and the constructor's typing needs the two to be one.
   Official 0: `replace_all_nested` replaces both occurrences in the
   instantiated auxiliary constructor by the one auxiliary type.  Today 0.
   A key-named frame must abstract the contained key at EVERY occurrence
   of the instantiated constructor, not only inside the parameters (the
   first KEYNAMED prototype did the latter: 1, a false reject).  The forged
   twin `corner_keynamed_ctor_occ_bad` spells the binder
   `List ((fun x => x) R)`: official 1 (two auxiliary types, the
   auxiliary constructor ill-typed), today 0 (D3). -/

def F (X : Type) (g : X → Nat) (β : Type) : Type := β
inductive C (β : Type) (a : List β → Nat) : Type where
  | mk (x : F (List β) a β) : C β a
inductive R : Type where
  | leaf : R
  | mk (c : C R (fun _ : List R => 0)) : R
