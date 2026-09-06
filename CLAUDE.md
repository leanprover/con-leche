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
* Layering: implementation (`Setlec/Kernel/*`, `Setlec/Cached/*`,
  `Main.lean`) must never import theory/verification modules
  (`Setlec/SetTheory/*`, `Setlec/SetModel/*`, `Setlec/Semantics/*`,
  `Setlec/SetP/*`, `Setlec/Verify/*`). Proofs about kernel functions go in
  `Setlec/Verify/*`; the pure set constructions (no `Expr` in sight) in
  `Setlec/SetModel/*`; the Expr-facing denotation and claims in
  `Setlec/Semantics/*`; the graded set model and the consistency proofs in
  `Setlec/SetP/*` (the direct `Setlec/Model/*` tier was retired at task
  #148 T7; the collapsed-model `Setlec/SetR/*` tier was deleted 2026-09-05;
  `Setlec/SetBase/*` was split into SetModel/Semantics on 2026-09-06).
  Direct-structure installation has its own directory per layer
  (`Kernel/Direct/*`, `Verify/Direct/*`, `Semantics/Direct/*`,
  `SetP/Direct/*`).
  Exception (2026-08-24): a *self-contained* verification of a data
  structure (e.g. the arena's WF — invariants + preservation proofs
  importing no other Model/Verify modules) may live with, and be
  imported by, the implementation — the Std.HashMap pattern: the
  structure carries its invariant; downstream never re-proves it.
* Large artifacts (reference checkouts, worktrees) go in `_tmp/` (gitignored;
  /tmp and /home are tmpfs). Reference clones already there: nanodatg,
  lean-inductive-models, lean4lean-model.
* If running the checker may OOM, use a timeout and memory limit.
* Exit codes (arena convention): 0 accept, 1 reject (invalid input proof),
  2 decline, 3 error. Decline (2) only when the checker *positively detects*
  a feature it doesn't support yet — never when an internal construction
  happens to fail or an invariant is violated with unclear cause; that is
  exit 3 ("crash for unclear reasons", which verification should make rare).
