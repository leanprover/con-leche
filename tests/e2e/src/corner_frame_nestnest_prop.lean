--#export T.rec T.rec_1 T.rec_2

/- Corner case (lane FRAME, PRIMREC S4; probe
   `_tmp/uniform-inds/openind/NestNestProp.lean` (1)): nested-in-nested at
   `Prop`.  `T` nests through `W`, `W` nests through `V`, so the walk's key
   for `V`'s node carries `W`'s FRAME hole (`V (y_W x_T)`): the depth-2
   frame the frame lemma is about.  Official 0.  Target 0. -/

inductive V (γ : Prop) : Prop where
  | v : γ → V γ
inductive W (β : Prop) : Prop where
  | w : V (W β) → W β
inductive T : Prop where
  | mk : W T → T
