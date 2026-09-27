--#export R.rec R.rec_1 R.rec_2 R.rec_3
set_option genSizeOfSpec false
set_option genInjectivity false

/- Corner case D3, PHANTOM-DEEP half: as `corner_keynamed_d3_phantom`,
   but `C` does read the parameter `a` — only as a parameter of a further
   container `Foo α a` that no constructor of `Foo` reads.  Official 0:
   `C_1`'s constructor field is the nested occurrence
   `Foo (List R → Nat) (fun _ : List ((fun x => x) R) => 0)`, replaced
   WHOLE by an auxiliary type (the split is baked into it and never
   unpacked).  Today 0.  With frame holes named by KEY both the key's
   typing (K.52) and `C.mk`'s typing at the holes fail: reject (1). -/

inductive Foo (α : Type) (a : α) : Type where
  | mk : Foo α a
inductive C (α : Type) (a : α) (β : Type) : Type where
  | mk (x : β) (y : Foo α a) : C α a β
inductive R : Type where
  | leaf : R
  | mk (l : List R) (c : C (List R → Nat) (fun _ : List ((fun x => x) R) => 0) R) : R
