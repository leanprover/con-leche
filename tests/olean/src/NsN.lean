module
-- (task #421) reads NsH's recursors of nested blocks (with the nested
-- occurrences' motives) and their computation rules on a constructor.
import NsH
noncomputable def nsLsize : NsL → Nat :=
  NsL.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ n => n + 1) 0 (fun _ _ a b => a + b)
theorem nsLsize_mk : nsLsize (.mk []) = 1 := rfl
noncomputable def nsUsize : NsU → Nat :=
  NsU.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (fun _ n => n + 1) (fun _ a => a) (fun _ _ a b => a + b) (fun _ _ a => a)
theorem nsUsize_mk (u : NsU) : nsUsize (.mk (.one u)) = nsUsize u + 1 := rfl
noncomputable def nsM2depth : NsM2 → Nat :=
  NsM2.rec (motive_1 := fun _ => Nat) (motive_2 := fun _ => Nat)
    (motive_3 := fun _ => Nat) (motive_4 := fun _ => Nat) (motive_5 := fun _ => Nat)
    (fun _ n => n) 0 (fun _ _ a b => a + b + 1) 0 (fun _ _ a b => a + b) 0 (fun _ a => a)
    (fun _ a => a)
theorem nsM2depth_mk : nsM2depth (.mk none #[]) = 1 := rfl
theorem nsA_mk : NsA.mk #[] = NsA.mk #[] := rfl
theorem nsR_rec (x : NsR) : x = x := NsR.rec (motive_1 := fun x => x = x)
  (motive_2 := fun _ => True) (motive_3 := fun _ => True) (fun _ _ => rfl) (fun _ _ _ _ => .intro)
  .intro (fun _ _ _ _ => .intro) x
noncomputable def nsDsize : NsD → Nat :=
  NsD.rec (motive := fun _ => Nat) 0 (fun _ ih => ih 0 + 1)
theorem nsDsize_mk : nsDsize (.mk fun _ => .leaf) = 1 := rfl
