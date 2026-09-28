--#export R.rec R.rec_1 R.rec_2 R.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- `corner_keynamed_d3_level` nested at a level PARAMETER (`D.{w} R`), the
   export source of the forged twins `corner_levelnf_d3_param_dup`
   (binder `List.{max u u} β`) and `corner_levelnf_d3_param_imax1`
   (binder `List.{imax 1 u} β`), `scripts/mk_levelnf_fixtures.py`.
   Official 0.  Ours 0 (the dup twin: 0, was 1 under `Level.simplify`;
   the imax1 twin: 0 either way, `simplify` resolves `imax 1 w`). -/

universe u w
def F (α : Type u) (a : α) (β : Type u) : Type u := β
inductive C (α : Type u) (a : α) (β : Type u) : Type u where
  | mk (x : F α a β) : C α a β
inductive D (β : Type u) : Type u where
  | mk (c : C.{u} (List.{u} β → PUnit.{u+1}) (fun _ : List.{u} β => PUnit.unit) β) : D β
inductive R : Type w where
  | leaf : R
  | mk (d : D.{w} R) : R
