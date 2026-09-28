--#export TLI.rec TLI.rec_1 TLI.rec_2 TLI.rec_3

/- CLASSCHECK (PROOFPLAN experiment E3, risk X5): a container nested over
   `List` through a DEFINITION, `RLI α ::= node α (List (Idd (RLI α)))`,
   entered by `TLI ::= node (List (RLI TLI))`.  The class
   `List (Idd (RLI TLI))`'s constructor field `Idd (RLI TLI)` is a class
   occurrence (`RLI TLI`) under a δ-redex: abstracted to its hole BEFORE
   whnf, then whnf exposes the hole.  Official 0; the class checker 0;
   the default route 0. -/

set_option genSizeOfSpec false
set_option genInjectivity false

def Idd (α : Type) : Type := α
inductive RLI (α : Type) : Type where
  | node (a : α) (cs : List (Idd (RLI α))) : RLI α
inductive TLI : Type where
  | node (l : List (RLI TLI)) : TLI
