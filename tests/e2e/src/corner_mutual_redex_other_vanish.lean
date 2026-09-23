--#export VA.count

/- Corner case (conformance gap, accept-subset): a MUTUAL block in
   which a constructor field of `VA` mentions the OTHER member `VB`
   only in a position the field's whnf ERASES: `Const' Unit VB` ⇝
   `Unit`.  Official's `check_positivity` whnf's the domain first,
   finds no occurrence of the block and classifies an ORDINARY field
   (no inductive hypothesis in the recursor); it ACCEPTS.

   con-leche today DECLINES (exit 2): `normPosDom` (Kernel/Inductives/
   SumInstall.lean:162, called with `ms.cvT.name` from
   BlockInstall.lean:191) sees a domain that does not mention `VA`
   and keeps it unreduced; `blockPositivity` then finds `VB` under the
   non-member head `Const'` → `.unsupported`.  At ONE member the same
   shape is normalised (the walk's name IS the block) — this is the
   k-name hole only.  Target verdict 0 (the walk's member list). -/

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
