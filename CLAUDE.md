# Working on Setlec

Read DESIGN.md first — it holds the design decisions, verification style, and
iteration protocol. Keep it up to date when decisions change.

* Build: `lake build` (must stay warning-free). Tests: `lake test`
  (`tests/SetlecTests.lean`, `#guard`/`example`-based, fails at build time).
* Goal: the lean kernel arena tutorial tests (without custom axioms) are
  accepted and the checker is verified consistent.
* Iterate one feature at a time; every feature lands together with its
  verification and regression tests. Commit often.
* No `sorry`s on master; no new axioms. Consistency proofs stay parametric in
  the `SetTheory` interface.
* Layering: implementation (`Setlec/Kernel/*`, `Main.lean`) must never import
  theory/verification modules (`Setlec/SetTheory/*`, `Setlec/Model/*`,
  `Setlec/Verify/*`). Proofs about kernel functions go in `Setlec/Verify/*`;
  the set-theoretic model and consistency in `Setlec/Model/*`.
* Large artifacts (reference checkouts, worktrees) go in `_tmp/` (gitignored;
  /tmp and /home are tmpfs). Reference clones already there: nanodatg,
  lean-inductive-models, lean4lean-model.
* If running the checker may OOM, use a timeout and memory limit.
