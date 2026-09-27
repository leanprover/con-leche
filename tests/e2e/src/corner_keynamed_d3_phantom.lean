--#export R.rec R.rec_1 R.rec_2
set_option genSizeOfSpec false
set_option genInjectivity false

/- Corner case D3, PHANTOM half: the two spellings `List R` and
   `List ((fun x => x) R)` sit in a container parameter `a` that no
   constructor of `C` reads (`C.mk (x : β)`).  Official 0: the auxiliary
   type `C_1` has no constructor mentioning `a`, so `List ((fun x => x) R)`
   never becomes an auxiliary type.  Today 0.  A positivity check with
   frame holes named by KEY abstracts both spellings to two holes and
   types the key `C (z₀ → Nat) (fun _ : z₁ => 0) R` at them (K.52):
   ill-typed, so it would reject (1) — a false reject. -/

inductive C (α : Type) (a : α) (β : Type) : Type where
  | mk (x : β) : C α a β
inductive R : Type where
  | leaf : R
  | mk (l : List R) (c : C (List R → Nat) (fun _ : List ((fun x => x) R) => 0) R) : R
