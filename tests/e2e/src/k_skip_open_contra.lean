--#export k_skip_open_contra
/- Task #552 (the K rule without the index check): `Eq.rec` on an OPEN
major under a contradictory hypothesis, the shape of the arena's
`bad/098_ruleKbad`.  Under `h : 0 = 1` the K rescue fabricates
`Eq.refl 0`, whose type `0 = 0` the index check compares with `0 = 1`.
The claim `Eq.rec 5 h = 5` by `Eq.refl` (hand-patched as
`k_skip_funext_rfl`: `scripts/splice-rfl.py k_skip_open_contra.ndjson
k_skip_open_contra`).

**Verdict.**  Today and with `.skipClosed`: reject (exit 1), as
official.  With `.skipAll`: accept (true under an inconsistent
hypothesis; sound).  Target: reject. -/
theorem k_skip_open_contra (h : 0 = 1) :
    @Eq.rec Nat 0 (fun _ _ => Nat) 5 1 h = 5 := sorry
