--#export And.dfq_use
/- Task #251 control: the major proved by a DEF unfolds in both regimes. -/
def And.dfq : And True True := ⟨trivial, trivial⟩
noncomputable def And.dfq_elim : Nat := And.rec (motive := fun _ => Nat) (fun _ _ => 0) And.dfq
theorem And.dfq_use : Eq And.dfq_elim 0 := rfl
