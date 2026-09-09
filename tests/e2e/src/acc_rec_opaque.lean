--#export Acc.opq_use
/- Task #251 probe: `Acc.rec` into `Type` on a theorem-proved major (indexed,
   recursive: no η rescue exists). -/
theorem Acc.opq : Acc (fun (_ _ : Nat) => False) 0 := Acc.intro 0 (fun _ h => h.elim)
noncomputable def Acc.opq_elim : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun x _ _ => x) Acc.opq
theorem Acc.opq_use : Eq Acc.opq_elim 0 := rfl
