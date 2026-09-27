--#export T.rec T.rec_1 T.rec_2 T.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key-named recursor route, a flexible key LITERAL in a key leaf's spelling (lane
   PRIMREC/NESTKN-NL, DESIGN "PRIMREC / NESTKN-NL" round 5, risk R-absRK (b)).  Node
   `W3 List T (List T)` holds the flexible family `z` for `List T` (`DsF = [List, T, z]`);
   instantiating `W3.mk`'s field `List (γ β)` creates `List (List T)` with `List T`
   LITERAL (no family), so the recursor route's match abstracts it to `z` on the leaf's
   side while the positivity check binds the child's family to the literal key.  Official
   0.  Wired (wire-K + wire-R), the route typed the call at the callee's ABSTRACTED
   parameters and rejected it (a false reject); it now types a container-key leaf at the
   leaf's own relocated spelling.  Target 0. -/

inductive W3 (γ : Type → Type) (β : Type) (δ : Type) : Type where
  | mk : List (γ β) → δ → W3 γ β δ
inductive T : Type where
  | leaf : T
  | mk (w : W3 List T (List T)) : T
