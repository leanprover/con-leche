--#export RA.size

/- Corner case (conformance gap, accept-subset): a MUTUAL block in
   which a constructor field of `RA` reaches the OTHER member `RB` only
   through a reducible head, `Id' RB`.  Official's `check_positivity`
   whnf's the field domain first (`Id' RB` ⇝ `RB`, a valid member
   application) and ACCEPTS; its recursors treat the field as
   recursive (`is_rec_argument` whnf's too).

   con-leche today DECLINES (exit 2): the uniform route's positivity
   walk `normPosDom` (Kernel/Inductives/SumInstall.lean:162, called from
   `checkSumCtor` with `ms.cvT.name`, BlockInstall.lean:191) is given
   the member's OWN name only, so a domain mentioning only `RB` inside
   `RA`'s constructor is kept unreduced; `blockPositivity`
   (BlockParts.lean) then sees head `Id'`, a non-member constant, and
   says `.unsupported` → "a nested occurrence of the block".
   Target verdict 0: pass the whole member list to the walk. -/

abbrev Id' (α : Type) : Type := α

mutual
  inductive RA : Type where
    | base : RA
    | mk : Id' RB → RA
  inductive RB : Type where
    | mk : RA → RB
end

/-- fires `RA.rec` through the redex-typed field's inductive hypothesis -/
noncomputable def RA.size (a : RA) : Nat :=
  RA.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    0 (fun _ ih => ih + 1) (fun _ ih => ih + 1) a
