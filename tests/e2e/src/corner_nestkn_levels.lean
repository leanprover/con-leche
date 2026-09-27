--#export T.rec T.rec_1 T.rec_2 T.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named positivity, adversarial (lane PRIMREC/NESTKN-K2): LEVEL-POLYMORPHIC
   containers with a typing link, the using node at a level instantiation. -/

universe u
def F (X : Type u) (g : X → Nat) (β : Type u) : Type u := β
inductive C (β : Type u) (a : List β → Nat) : Type u where
  | mk (x : F (List β) a β) : C β a
inductive G (α : Type u) : Type u where
  | leaf : G α
  | node (c : C (G α) (fun _ : List (G α) => 0)) : G α
inductive T : Type where
  | leaf : T
  | mk (g : G.{0} T) : T
