--#export k_skip_open_eta
/- Task #552 (the K rule without the index check): an OPEN major whose
skip changes a term's type, so that a comparison official decides
`true` fails.  Under `h : a = b`, `h ▸ p : Fin b × Nat` is a K-like
`Eq.rec` whose index check fails (`a` against `b`, two variables).  The
claim `h ▸ p = ((h ▸ p).1, (h ▸ p).2)` is structure η: with the check
the left side is stuck and η compares its projections with the right
side's fields, syntactically equal.  Without it the left side reduces
to `p : Fin a × Nat`, and η's type comparison (`Fin a × Nat` against
`Fin b × Nat`) fails: subject reduction is lost.  An honest export
(`rfl` elaborates).

**Verdict.**  Accept (exit 0), as official, today and with
`.skipClosed`.  With `.skipAll`: reject (exit 1) — con-leche rejects
what official accepts.  Target: accept. -/
theorem k_skip_open_eta (a b : Nat) (h : a = b) (p : Fin a × Nat) :
    (h ▸ p : Fin b × Nat) = ((h ▸ p : Fin b × Nat).1, (h ▸ p : Fin b × Nat).2) := rfl
