--#export T.rec T.rec_1 T.rec_2 T.rec_3 T.rec_4
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named positivity, adversarial (lane PRIMREC/NESTKN-K2): the stage is the using
   node's FLEXIBLE family, not its own hole.  Node `W (List T)` abstracts `List T` to a
   family `z`; its child `C (List T) (fun _ : List (List T) => 0)` keeps the rigid
   `List (List T)` (the value `a` is typed by it) with the flexible `List T` inside it,
   and MEETS `List T` (`C.mk`'s field reads `β`); the met family propagates to
   `W (List T)` and from there, as a concrete key at the root, to a pending use of
   `List T`. -/

def F (X : Type) (g : X → Nat) (β : Type) : Type := β
inductive C (β : Type) (a : List β → Nat) : Type where
  | mk (x : F (List β) a β) : C β a
inductive W (β : Type) : Type where
  | mk (c : C β (fun _ : List β => 0)) : W β
inductive T : Type where
  | leaf : T
  | mk (w : W (List T)) : T
