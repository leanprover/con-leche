--#export VA.count

/- Corner case (conformance gap, accept-subset): a MUTUAL block in
   which a constructor field of `VA` mentions the OTHER member `VB`
   only in a position the field's whnf ERASES: `Const' Unit VB` ⇝
   `Unit`.  Official's `check_positivity` whnf's the domain first,
   finds no occurrence of the block and classifies an ORDINARY field
   (no inductive hypothesis in the recursor); it ACCEPTS.

   con-leche's positivity walk (Kernel/Inductives/Positivity.lean) is
   given the whole member list, so it whnf's the domain, which mentions
   only `VB`, and finds no occurrence.  Today 0, target 0. -/

abbrev Const' (α _β : Type) : Type := α

mutual
  inductive VA : Type where
    | base : VA
    | mk : Const' Unit VB → VA → VA
  inductive VB : Type where
    | mk : VA → VB
end

/-- counts `mk`s: the `Const'` field carries no inductive hypothesis -/
noncomputable def VA.count (a : VA) : Nat :=
  VA.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    0 (fun _ _ ih => ih + 1) (fun _ ih => ih) a
