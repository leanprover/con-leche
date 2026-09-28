--#export R.rec R.rec_1 R.rec_2 R.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key identity under level instantiation AT A PARAMETER (lane
   CC-LEVELNF), from an ordinary SOURCE: `corner_keynamed_level_inst`
   nested at `D.{w,w} R R` instead of `D.{0,0} R R`.  The container's
   field `List.{max u v} (Prod.{u,v} β γ)` instantiates, in official's
   `instantiate_lparams`, to `List.{w}` (`level.cpp` `mk_max`: `l1 == l2`
   gives `l1`), so the exported recursor's major is `List.{w} (R × R)`;
   this checker's `Level.subst` gives `List.{max w w} (R × R)`.  The class
   matching compares levels by `Level.canon`, which removes the duplicate:
   official 0, ours 0 (the class route under `Level.simplify`, which keeps
   `max w w`, rejected it: 1). -/

universe u v w
inductive D (β : Type u) (γ : Type v) : Type (max u v) where
  | mk (l : List (β × γ)) : D β γ
inductive R : Type w where
  | leaf : R
  | mk (d : D.{w,w} R R) : R
