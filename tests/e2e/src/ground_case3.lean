--#export t_and_ctor t_acc
/- End-to-end fixture (task #423 completeness): ι at families that may be
   `Prop` ("case 3": `And`, `Acc`), at the ground site.

   * `t_and_ctor`: `And.rec` on `And.intro trivial trivial`;
   * `t_acc`: `Acc.rec` on an explicit `Acc.intro`.

   Official (v4.29.1) accepts both: its `inductive_reduce_rec` fires
   without checks.  Con-leche's incumbent would reject **`t_acc`**: the
   elaborator abstracts the closed proof `Acc.intro …`
   into the theorem `kAcc._proof_1`, which official's whnf unfolds and
   con-leche never does (proofs are not reduced), so the major is stuck.
   Official 0.

   The ground engine evaluates the terms, with no hand-back (task #423
   soundness, ruling 4): ι case 3 has no proved rule without the
   certificates, so this is a decline (2), naming `And.rec`. -/

noncomputable def kAndC : Bool := And.rec (motive := fun _ => Bool) (fun _ _ => true) (And.intro trivial trivial)

noncomputable def kAcc : Bool :=
  @Acc.rec Nat (fun _ _ => False) (fun _ _ => Bool) (fun _ _ _ => true) 0 (Acc.intro 0 (fun _ h => h.elim))

theorem t_and_ctor : kAndC = true := rfl
theorem t_acc : kAcc = true := rfl
