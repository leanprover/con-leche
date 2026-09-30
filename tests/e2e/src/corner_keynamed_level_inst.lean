--#export R.rec R.rec_1 R.rec_2 R.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Key identity under LEVEL INSTANTIATION (lane KEYNAMED): the container
   `D.{u,v}`'s constructor field is `List.{max u v} (Prod.{u,v} β γ)`.
   Nested at `D.{0,0} R R`, official's `instantiate_lparams` simplifies
   `max 0 0` to `0` (`level.cpp` `mk_max`), so its auxiliary type (and the
   exported recursor's major) is `List.{0} (Prod.{0,0} R R)`.  Official 0
   (v4.29.1 and v4.34.0-rc2).  This checker's `Level.subst` does not
   simplify: the positivity check's node is `List.{max 0 0} (Prod R R)`,
   and the recursor check rejects official's `R.rec_2` ("the recursor's
   major is … no auxiliary type of the block") — today 1, a FALSE REJECT
   (also on `uniform-inds` 6e6c5397e; not on the retired modeller).
   TARGET 0: official's simplifying level instantiation at the positivity
   check's constructor instantiation gives 0 (measured on the KEYNAMED
   prototype, verdict-neutral on every other e2e/arena row). -/

universe u v
inductive D (β : Type u) (γ : Type v) : Type (max u v) where
  | mk (l : List (β × γ)) : D β γ
inductive R : Type where
  | leaf : R
  | mk (d : D.{0,0} R R) : R
