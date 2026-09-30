--#export R.rec R.rec_1 R.rec_2 R.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Corner case D3, LEVEL half (lane PRIMREC/KEYNAMED).  The container
   `D.{u}` passes a phantom value whose binder names `List.{u} β`, and the
   class `List.{u} β → PUnit` as its type.  Official 0.  Today 0.
   The forged twin `corner_keynamed_d3_level_split`
   (`scripts/mk_keynamed_fixtures.py`) spells that binder
   `List.{max u u} β` (the elaborator normalises `max u u`, so the source
   cannot): level-defeq, so `D` stays well-typed.  At the instance
   `D.{0} R` official's `instantiate_lparams` SIMPLIFIES (`level.cpp`
   `mk_max`: `max 0 0 = 0`), so both spellings are the ONE key
   `List.{0} R` — official 0.  This checker's `Level.subst` does not
   simplify: the keys `List.{0} R` and `List.{max 0 0} R` differ — today 1
   (the recursor's majors are official's simplified classes, which the
   positivity check's nodes do not contain), frame holes named by key 1
   (two holes, the key ill-typed); both 0 with official's simplifying
   level instantiation at the positivity check's constructor
   instantiation (measured on the KEYNAMED prototype). -/

universe u
def F (α : Type u) (a : α) (β : Type u) : Type u := β
inductive C (α : Type u) (a : α) (β : Type u) : Type u where
  | mk (x : F α a β) : C α a β
inductive D (β : Type u) : Type u where
  | mk (c : C.{u} (List.{u} β → PUnit.{u+1}) (fun _ : List.{u} β => PUnit.unit) β) : D β
inductive R : Type where
  | leaf : R
  | mk (d : D.{0} R) : R
