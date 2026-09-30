--#export RA.size

/- Corner case (conformance gap, accept-subset): a MUTUAL block in
   which a constructor field of `RA` reaches the OTHER member `RB` only
   through a reducible head, `Id' RB`.  Official's `check_positivity`
   whnf's the field domain first (`Id' RB` ⇝ `RB`, a valid member
   application) and ACCEPTS; its recursors treat the field as
   recursive (`is_rec_argument` whnf's too).

   con-leche's positivity walk (Kernel/Inductives/Positivity.lean) is
   given the whole member list, so it whnf's a domain that mentions only
   the other member, as official does.  Today 0, target 0. -/

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
