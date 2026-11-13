--#export t_acc_def
/- End-to-end fixture (task #423 completeness): `Acc.rec` (a family that
   may be `Prop`, with large elimination, not K, not structure-like) on a
   proof argument that a DEFINITION reduces to `Acc.intro`.

   `accDef` is a definition (not a theorem), so the incumbent's whnf of
   `f accDef` unfolds `f`, then the major `accDef`, reaches `Acc.intro`,
   and fires case 3: accepted (official too).

   The ground engine erases proof arguments, so `f`'s `h` is the neutral
   cell and `Acc.rec` sees a stuck major with no η: the one place where
   erasure loses a step the incumbent takes.  The engine hands the
   comparison back to the incumbent there ("struct-eta major"), which
   accepts.  Without that hand-back the engine would answer `false`.
   Target 0.

   Task #423 soundness (no hand-back, ruling 4): this
   is a decline (2), naming `Acc.rec`. -/

def accDef : Acc (fun _ _ : Nat => False) 0 := Acc.intro 0 (fun _ h => h.elim)

noncomputable def f (h : Acc (fun _ _ : Nat => False) 0) : Bool :=
  @Acc.rec Nat (fun _ _ => False) (fun _ _ => Bool) (fun _ _ _ => true) 0 h

theorem t_acc_def : f accDef = true := rfl
