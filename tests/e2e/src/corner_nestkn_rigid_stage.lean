--#export T.rec T.rec_1 T.rec_2 T.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named positivity, adversarial (lane PRIMREC/NESTKN-K2): a RIGID key that contains
   the using node's own key.  Node `G T`'s child `C (G T) (fun _ : List (G T) => 0)`:
   `List (G T)` is rigid (the value `a` is typed by it), `G T` is flexible.  With
   outermost contained keys the rigid `List (G T)` would hold the site's own hole
   at stage; all-depth keys abstract the inner `G T` inside it. -/

def F (X : Type) (g : X → Nat) (β : Type) : Type := β
inductive C (β : Type) (a : List β → Nat) : Type where
  | mk (x : F (List β) a β) : C β a
inductive G (α : Type) : Type where
  | leaf : G α
  | node (c : C (G α) (fun _ : List (G α) => 0)) : G α
inductive T : Type where
  | leaf : T
  | mk (g : G T) : T
