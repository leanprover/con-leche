# Working on ConLeche

Design and architecture are not in this file. `OVERVIEW.md` is the
current, human-facing tour (module map §11, gates §12); `DESIGN.md` is
the agents' journal: its opening sections state the standing design,
the later sections are dated records. When a decision changes, update
DESIGN.md (append your lane's record at the end), and OVERVIEW.md if a
current fact changed.

## Build, tests, gates

* `lake build` and `lake test` must both be warning-free. `lake test`
  builds the test library (`tests/ConLecheTests.lean`,
  `tests/ConLecheTests/*`, `#guard`/`example`-based, fails at build
  time, and pins the capstones' axioms in `Axioms.lean`); `lake build`
  does not build it, so a warning there is invisible to the build gate.
* `tests/arena.sh` is the standard battery (CI runs it): the gates below,
  the arena tutorial tests, the end-to-end fixtures (`tests/e2e/`,
  verdicts pinned in `tests/e2e-expected.txt`), the annotation fixtures
  and the trusted-mode sweep. Each gate also runs on its own:
  - `tests/layering.sh` — the import fence (see Layering below).
  - `tests/shake.sh` — `lake shake` proposals against
    `tests/shake-allowlist.txt`, and `scripts/pub-import-plan.py --check`
    (no `public import` individually demotable).
  - `tests/trust-surface.sh` — no `unsafe`/`implemented_by`/
    `native_decide` outside the allowlisted files.
  - `tests/overview-links.sh` — line-anchored links in `OVERVIEW.md` and
    `README.md`. If you move or change linked lines, re-read the citing
    paragraph, then `tests/overview-links.sh --update`.
  - `tests/quote-gate.sh` — every fenced ```lean block headed by
    `theorem <name>`/`def <name>` in those two documents must match the
    source's statement TEXTUALLY (indentation included). No `--update`:
    the source is the truth; re-sync the quote.
  - `tests/pindump.sh`, `tests/no-local-paths.sh`, `tests/challenge.sh`.
* Every design corner case gets an end-to-end fixture right away (today's
  verdict, with a comment naming the target verdict).
* Load the `lean-rc-linearity` skill before touching hot-path state
  threading, memo/arena mutation or per-node arithmetic.

## Documents

* `README.md` is the maintainer's, human-written. An agent may turn an
  existing code name into a link, repoint a link that rotted, and re-sync
  a quoted code block the quote gate reports; no other character of it
  changes. Anything it should say differently is reported, not written.
* `OVERVIEW.md` and `README.md` state current facts: no task numbers, no
  history. Task numbers and history are fine in code comments and
  DESIGN.md.

## Process rules

* One feature at a time; every feature lands with its verification and
  regression tests. Commit often.
* No `sorry` on a landed branch; no new axioms. Consistency proofs stay
  parametric in the `SetTheory` interface.
* Git: your working directory resets between tool calls, so use
  `git -C <worktree>` always; stage by explicit path, never `git add -A`
  or `git add .`; check the branch before committing.
* Landing a lane on an integration branch: merge the integration branch
  into your lane branch, re-run the gates the intervening changes can
  affect, fast-forward the integration branch from the main checkout
  (`git -C /home/joachim/setlec merge --ff-only <lane>`, after checking
  that `git status --short` is clean apart from the maintainer's
  untracked files), remove your worktree. A partial lane does not land.
* Large artifacts (reference checkouts, worktrees, logs) go in `_tmp/`
  (gitignored; `/tmp` and `/home` are tmpfs under a memory cap).
* Builds: every worktree has its own `.lake`, so builds never conflict
  and there is nothing to wait for. Run in the foreground and capture the
  exit code: `timeout 3600 lake build > _tmp/<lane>/build.log 2>&1;
  echo EXIT=$?`. If it may exceed the foreground limit, run the same
  command with `run_in_background` and wait for the notification.
  NEVER wait on or kill by a process-name pattern (`pgrep -f "lake
  build"`, `pgrep -f bin/con-leche`): that catches other agents' work.
  If you must poll, poll the PID you launched (`kill -0 $pid`).
* Every checker run gets a `timeout`. Never `ulimit -v`: the worker
  pool's thread-stack reservation counts against it, so the binary aborts
  before checking (`failed to create thread`, exit 134) at any value
  that bounds anything. An exit 134 from a capped run is not a checker
  verdict.
* Wall time is not a measurement on this shared machine; use
  `perf stat -e instructions:u`.
* Exit codes (arena convention): 0 accept, 1 reject (invalid input),
  2 decline, 3 error. Decline only when the checker *positively detects*
  an unsupported feature; an internal construction that fails or an
  invariant violated with unclear cause is 3.

## Layering (enforced by `tests/layering.sh`)

* Implementation — `ConLeche/Kernel/*`, `ConLeche/Cached/*`,
  `ConLeche/Frontend/*`, `Main.lean` — never imports
  `ConLeche/{Term,SetTheory,SetModel,Semantics,Model,Verify,Complete}/*`.
* `ConLeche/Model/*` (the graded model) is imported only by itself, the
  capstone assembly (`Verify/Cached/MainC`, the `ConLeche.Verify.Cached`
  umbrella, `MainTheorem`) and `Complete/*`.
* `ConLeche/Complete/*` (parked work nothing consumes) is imported by
  nothing outside it.
* The rules tier (`ConLeche/Rules/*`, `ConLeche/Model/Rules/*`, except
  `Model/Rules/Recompose.lean`) imports neither the pure implementation
  (`Kernel/{Core,TypeChecker,CoreIO,Checker*,DeclCheck}`, `Cached/*`)
  nor, through public re-exports, any implementation module beyond the
  doors the script lists; that list may only shrink.
* Where proofs go: about kernel functions, needing no model →
  `Verify/*`; pure set constructions (no `Expr`) → `SetModel/*`; the
  `Expr`-facing denotation and claims → `Semantics/*`; the graded model
  and the consistency proofs → `Model/*`. Inductive installation has an
  `Inductives/` subdirectory in `Kernel/`, `Verify/`, `Semantics/` and
  `Model/`.
* Exception: a *self-contained* verification of a data structure
  (invariants and preservation proofs importing no other Model/Verify
  module) may live with, and be imported by, the implementation — the
  `Std.HashMap` pattern.

## The module system

* Every `.lean` file under `ConLeche/`, the roots and the test library
  carries the `module` header (a `module` cannot import a non-`module`).
  `_probe/*`, `scripts/*.lean`, `bridge/*` and the fixture sources under
  `tests/e2e/src/` are outside the build and stay classic.
* Checker code is exposed, because it is the subject of the proofs:
  `Kernel/*`, `Cached/*`, `Frontend/*` and `Main.lean` open one
  `@[expose] public section`, as do `Term/*`, `SetTheory/*`,
  `SetModel/*`, `Semantics/*` and `Rules/*` (the tiers above unfold
  them). A `private` helper there must be public if any *definition*
  mentions it (a `theorem` proof may still use it). The few deliberate
  deviations carry their reason in the file (the sealed
  `Kernel/PropWhen`, elaboration-time and generated modules,
  `Frontend/Scan/Equiv`).
* Proof code is private by default: `Model/*`, `Verify/*`, the tests and
  capstones open a plain `public section`; `@[expose]` goes only on a
  definition another file unfolds.
* Traps: a `private` lemma's `match` matcher is not reused, so a `rw`
  elsewhere stops finding its pattern; moving a `@[simp]` lemma from
  `:= rfl` to `:= by rfl` costs its rfl-status and `simp only` silently
  stops firing (expose what it unfolds instead); a term-mode
  `theorem … := rfl` elaborates in the PUBLIC view and fails on a hidden
  unfolding, `:= by rfl` elaborates in the private view and is the fix.
* `public import` only for a re-export something else's PUBLIC statement
  needs, and that is computed, not guessed (`scripts/pub-import-plan.py`
  over `scripts/pub-iface.lean` and the census; `tests/shake.sh` runs
  it). A missing re-export does not say "unknown identifier"; it makes a
  `rfl` stop closing.
* `import all X` only where a proof must see a body that is sealed on
  purpose (`Kernel/PropWhen`, whose API and laws are its whole
  interface) or hidden by the toolchain (`Init.Util`'s `withPtrEq`,
  `Init.Data.Repr`, the Nat-op certificate generator's `Init.Data.Nat.*`);
  each site carries its reason.
* Elaboration-time code (`Kernel/BasisGen`, `PinGen/*`, the pin and
  basis splices) is `meta`: `meta section`, `public meta import`; a
  module needed at both levels is imported twice (`public import X` +
  `meta import X`).
