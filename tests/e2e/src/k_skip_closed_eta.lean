--#export k_skip_closed_eta
/- Task #552 (the K rule without the index check): the lost subject
reduction of `k_skip_open_eta`, at a CLOSED major.  The major is the
closed `funext` proof `k_skip_closed_eta_h : (fun x => 0 + x) = (fun x => x)`,
the motive `fun g _ => ((n : Nat) → Fin (g n + 1)) × Nat`.  With the
index check the cast `c` is stuck and structure η compares its
projections with the right side's fields, syntactically equal; without
it `c` reduces to `p`, whose type has `Fin (0 + n + 1)` where the claim
has `Fin (n + 1)`, not definitionally equal under the binder, and η's
type comparison fails.  An honest export (`rfl` elaborates).

**Verdict.**  Accept (exit 0), as official, today.  With `.skipClosed`
and `.skipAll`: reject (exit 1) — con-leche rejects what official
accepts.  Target: accept. -/
theorem k_skip_closed_eta_h : (fun x : Nat => 0 + x) = (fun x => x) :=
  funext Nat.zero_add

theorem k_skip_closed_eta (p : ((n : Nat) → Fin (0 + n + 1)) × Nat) :
    @Eq.rec (Nat → Nat) (fun x => 0 + x) (fun g _ => ((n : Nat) → Fin (g n + 1)) × Nat) p
        (fun x => x) k_skip_closed_eta_h =
      ((@Eq.rec (Nat → Nat) (fun x => 0 + x) (fun g _ => ((n : Nat) → Fin (g n + 1)) × Nat) p
          (fun x => x) k_skip_closed_eta_h).1,
       (@Eq.rec (Nat → Nat) (fun x => 0 + x) (fun g _ => ((n : Nat) → Fin (g n + 1)) × Nat) p
          (fun x => x) k_skip_closed_eta_h).2) := rfl
