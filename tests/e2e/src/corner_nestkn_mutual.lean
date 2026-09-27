--#export T.rec T.rec_1 T.rec_2 T.rec_3 T.rec_4 T.rec_5
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named positivity, adversarial (lane PRIMREC/NESTKN-K2): a MUTUAL container whose
   parameters carry a typing link (`a : List β → Nat`), nested at the using node's own
   key; the node is reached at the SECOND mate `B`, its canonical head is `A`. -/

mutual
inductive A (β : Type) (a : List β → Nat) : Type where
  | nil : A β a
  | mk (b : B β a) : A β a
inductive B (β : Type) (a : List β → Nat) : Type where
  | mk (x : A β a) (y : β) : B β a
end
inductive G (α : Type) : Type where
  | leaf : G α
  | node (c : B (G α) (fun _ : List (G α) => 0)) : G α
inductive T : Type where
  | leaf : T
  | mk (g : G T) : T
