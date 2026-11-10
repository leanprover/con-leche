--#export k_skip_funext_rfl
/- Task #552 (the K rule without the index check): a CLOSED major whose
type equates two functions that are propositionally (`funext`) but not
definitionally equal.  `fun x => 0 + x` and `fun x => x` differ under
the binder: `Nat.add` recurses on its second argument, a variable there.

`k_skip_funext_val` is a constant-motive `Eq.rec` on that major.  The K
rescue fabricates `Eq.refl (fun x => 0 + x)`; official's index check
(`to_cnstr_when_K`) compares its type with the major's, `0 + x ≡ x`
fails, and the recursor is stuck.  `k_skip_funext_rfl` claims the value
is `5` by `Eq.refl`.

Hand-patched stream, like `k_rescue_stuck`: the elaborator's own whnf
runs the same index check, so the source carries `sorry`, and the
committed `.ndjson` is the export with the theorem's value replaced by
`@Eq.refl.{1} Nat 5` (`scripts/splice-rfl.py k_skip_funext_rfl.ndjson
k_skip_funext_rfl`).

**Verdict.**  Today (the index check runs): reject (exit 1), as
official.  With the check skipped at closed majors (`kIndexMode
.skipClosed` or `.skipAll`, `ConLeche/Kernel/KIndex.lean`): accept — a
`rfl` proof official rejects.  Sound (the claim is true, and the model
reads no index check, DESIGN task #552); the target verdict is
official's, reject. -/
theorem k_skip_funext_h : (fun x : Nat => 0 + x) = (fun x => x) :=
  funext Nat.zero_add

def k_skip_funext_val : Nat :=
  @Eq.rec (Nat → Nat) (fun x => 0 + x) (fun _ _ => Nat) 5 (fun x => x) k_skip_funext_h

theorem k_skip_funext_rfl : k_skip_funext_val = 5 := sorry
