--#export T.rec T.rec_1 T.rec_2 T.rec_3 T.rec_4
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named positivity, adversarial (lane PRIMREC/NESTKN-K2): a RIGID key that contains
   a FLEXIBLE key that contains the using node's own key, rigid keys at two depths.
   Node `G T`'s child `C (List (G T)) (fun _ : List (List (G T)) => 0)`: `List (List (G T))`
   rigid, `List (G T)` and `G T` flexible; `G T` occurs in the layout only inside the
   family `z_{List (G T)}`'s type, so its binding at the use comes from the outer
   family's binding. -/

def F (X : Type) (g : X → Nat) (β : Type) : Type := β
inductive C (β : Type) (a : List β → Nat) : Type where
  | mk (x : F (List β) a β) : C β a
inductive G (α : Type) : Type where
  | leaf : G α
  | node (c : C (List (G α)) (fun _ : List (List (G α)) => 0)) : G α
inductive T : Type where
  | leaf : T
  | mk (g : G T) : T
