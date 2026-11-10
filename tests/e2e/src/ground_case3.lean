--#export t_and_ctor t_acc
/- End-to-end fixture (task #423 completeness): ι at families that may be
   `Prop` ("case 3": `And`, `Acc`), at the ground site.

   * `t_and_ctor`: `And.rec` on `And.intro trivial trivial`;
   * `t_acc`: `Acc.rec` on an explicit `Acc.intro`.

   Official (v4.29.1) accepts both: its `inductive_reduce_rec` fires
   without checks.  Con-leche today: `t_and_ctor` accepted, **`t_acc`
   rejected**: the elaborator abstracts the closed proof `Acc.intro …`
   into the theorem `kAcc._proof_1`, which official's whnf unfolds and
   con-leche never does (proofs are not reduced), so the major is stuck.
   The file is rejected: today 1, official 0.  With the ground engine on,
   the engine fires case 3 at `And.intro` without the incumbent's
   certificates (official's shape) and hands `t_acc` back to the
   incumbent (a stuck major at a single-rule recursor with no η,
   "struct-eta major"), which rejects: 1.  Before, it aborted ("case 3",
   "struct-eta major") to the incumbent. -/

noncomputable def kAndC : Bool := And.rec (motive := fun _ => Bool) (fun _ _ => true) (And.intro trivial trivial)

noncomputable def kAcc : Bool :=
  @Acc.rec Nat (fun _ _ => False) (fun _ _ => Bool) (fun _ _ _ => true) 0 (Acc.intro 0 (fun _ h => h.elim))

theorem t_and_ctor : kAndC = true := rfl
theorem t_acc : kAcc = true := rfl
