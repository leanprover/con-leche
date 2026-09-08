# Working on ConLeche

Read DESIGN.md first — it holds the design decisions, verification style, and
iteration protocol. Keep it up to date when decisions change.

* Build: `lake build` (must stay warning-free). Tests: `lake test`
  (`tests/ConLecheTests.lean`, `#guard`/`example`-based, fails at build time).
* `OVERVIEW.md`'s line-anchored links are gated by
  `tests/overview-links.sh` (run from `tests/arena.sh` and CI): if you move
  or change linked lines, re-read the citing paragraph and run
  `tests/overview-links.sh --update`.
* Goal: the lean kernel arena tutorial tests (without custom axioms) are
  accepted and the checker is verified consistent.
* Iterate one feature at a time; every feature lands together with its
  verification and regression tests. Commit often.
* No `sorry`s on master; no new axioms. Consistency proofs stay parametric in
  the `SetTheory` interface.
* Layering: implementation (`ConLeche/Kernel/*`, `ConLeche/Cached/*`,
  `Main.lean`) must never import theory/verification modules
  (`ConLeche/SetTheory/*`, `ConLeche/SetModel/*`, `ConLeche/Semantics/*`,
  `ConLeche/Model/*`, `ConLeche/Verify/*`). Proofs about kernel functions go in
  `ConLeche/Verify/*`; the pure set constructions (no `Expr` in sight) in
  `ConLeche/SetModel/*`; the Expr-facing denotation and claims in
  `ConLeche/Semantics/*`; the graded set model and the consistency proofs in
  `ConLeche/Model/*` (task #222 renamed `ConLeche/SetP/*` to this; the
  first, direct model tier — cited in old docstrings as
  `ConLeche/ModelV1/*` — was retired at task #148 T7; the
  collapsed-model `ConLeche/SetR/*` tier was deleted 2026-09-05;
  `ConLeche/SetBase/*` was split into SetModel/Semantics on 2026-09-06).
  Inductive installation has its own directory per layer
  (`Kernel/Inductives/*`, `Verify/Inductives/*`, `Semantics/Inductives/*`,
  `Model/Inductives/*`); the two routes there are the NATIVE one (the ONE
  fixpoint route, task #210 — `checkNative`, `Native*.lean`, with the
  `Struct*`/`Sum*` stage kits it builds on) and the MODELED one
  (`Kernel/Inductives/Modeled.lean`, `checkModeled`, for mutual and
  nested blocks).
  Exception (2026-08-24): a *self-contained* verification of a data
  structure (e.g. the arena's WF — invariants + preservation proofs
  importing no other Model/Verify modules) may live with, and be
  imported by, the implementation — the Std.HashMap pattern: the
  structure carries its invariant; downstream never re-proves it.
* The module system (task #231): every `.lean` file under `ConLeche/`,
  the roots and `tests/*` carries the `module` header.  A `module` may
  not import a non-`module`, so the tree converts as a whole and stays
  that way; `_probe/*`, `scripts/*.lean` and `bridge/*` are outside the
  build and stay classic (a classic file may import a `module`).
  **Checker code is exposed, because it is the subject of the proofs**:
  `ConLeche/Kernel/*`, `ConLeche/Cached/*`, `ConLeche/Frontend/*` and
  `Main.lean` open one `@[expose] public section` — the Verify/Model
  tiers unfold their bodies by design, so a `private` helper there must
  be public if any *definition* mentions it (a `theorem` proof may
  still use one: proofs are private regardless).  **Proof code is
  private by default**: the theory tiers narrow to plain `import`,
  `public` only on what another file names, `@[expose]` only on a `def`
  a downstream *proof* unfolds.  `import all X` is the escape for a
  representation that is sealed on purpose — `ConLeche/Kernel/PropWhen`
  (the datum's API and laws are its whole interface) and `Init.Util`'s
  `withPtrEq` — and nothing else; each site carries the reason.
  Elaboration-time code (`Kernel/BasisGen`, `PinGen/*`, the pin and
  basis splices) is `meta`: `meta section`, `public meta import`, and a
  module needed at BOTH levels is imported twice (`public import X` +
  `meta import X`).  A term-mode `theorem … := rfl` is elaborated in
  the PUBLIC view and fails on a hidden unfolding; `:= by rfl` is
  elaborated in the private view and is the fix.
* Large artifacts (reference checkouts, worktrees) go in `_tmp/` (gitignored;
  /tmp and /home are tmpfs). Reference clones already there: nanodatg,
  lean4lean-model.
* If running the checker may OOM, use a timeout and memory limit
  (`ulimit -v 16000000` for ordinary runs, 22 GB for Mathlib scale;
  `timeout` on every checker run; builds get `timeout` only).
* Running builds and other long processes (agents): this machine is
  shared by several agents in separate worktrees, and each worktree has
  its own `.lake`, so builds never conflict and there is nothing to wait
  for. Run your build in the foreground and capture its exit code:
  `timeout 3600 lake build > _tmp/<lane>/build.log 2>&1; echo EXIT=$?`.
  If it may exceed the tool's foreground limit, start that same command
  in the background (`run_in_background`) and wait for the completion
  notification. NEVER wait on a process-name pattern (`pgrep -f "lake
  build"`, `pgrep -f bin/con-leche`): that blocks on other agents' work,
  for as long as anyone is building. If you must poll, poll the PID you
  launched (`kill -0 $pid`). Wall time is not a measurement here (shared
  machine); use `perf stat -e instructions:u`.
* Exit codes (arena convention): 0 accept, 1 reject (invalid input proof),
  2 decline, 3 error. Decline (2) only when the checker *positively detects*
  a feature it doesn't support yet — never when an internal construction
  happens to fail or an invariant is violated with unclear cause; that is
  exit 3 ("crash for unclear reasons", which verification should make rare).
