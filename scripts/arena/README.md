# The Lean Kernel Arena suite

Running the *upstream* arena — every test definition in
[`leanprover/lean-kernel-arena`](https://github.com/leanprover/lean-kernel-arena)
except `mathlib` — against this working tree's `con-leche`, through the arena's own
orchestration (`lka.py`), so the exports are the ones the arena produces.

The narrative record, with the findings, is DESIGN.md, section
**"THE ARENA SUITE (all but Mathlib)"**.  This directory is the machinery and
the raw result of the run that section describes.

## The kit

| file | what it is |
|---|---|
| `con-leche.yaml` | the checker definition, in the arena's `checkers/` format.  A *simple* checker (no `url`/`dir`): `lka.py` makes an empty build directory and runs it there with `$IN` pointing at the raw export.  Every path comes from the environment, so the arena clone stays a pure checkout. |
| `run-suite.sh` | the driver: `clone` / `build-tests` / `build-checker` / `run` / `run-small` / `run-big` / `table` / `all`.  Copies `con-leche.yaml` into the clone, puts GNU `time` on `PATH`, sets the limits. |
| `table.py` | renders a run's `_results/*.json` against the expected outcomes. |
| `results/` | the committed record of the run (below). |

## Reproducing

    scripts/arena/run-suite.sh clone
    scripts/arena/run-suite.sh build-tests        # every test but mathlib
    scripts/arena/run-suite.sh run-small          # 202 runs, ~10 min
    scripts/arena/run-suite.sh run-big            # init std cedar cslib
    scripts/arena/run-suite.sh table

`CON_LECHE_MODE=--trusted` re-runs the same matrix in the unverified lane.
Building the corpus is the expensive half — `lka.py` clones and builds Cedar
(from source) and cslib (`lake exe cache get`), and the exports come to ~4 GB —
so nothing here is wired into `lake test`.  A landing gate can run `run-small`
against an already-built corpus in ten minutes.

**The big four** (`init`, `std`, `cedar`, `cslib`: 0.3 – 2.0 GB of raw export)
are Mathlib-scale in memory.  Run them strictly one at a time under
`ulimit -v 22000000`, and only when the machine's single Mathlib-scale slot is
yours — ask the coordinator; do not poll other lanes' processes.

## `results/` — the committed record

`summary.tsv` is the whole suite in one greppable file: one row per test, with
the expected outcome and the exit code in each column.  `table.txt` is the
rendered verdict table with messages, timings and peak RSS.  The `*.jsonl`
files are the runs themselves — `lka.py`'s own result records, one JSON object
per line, sorted by test name:

| file | run |
|---|---|
| `con-leche-verified.jsonl`, `con-leche-trusted.jsonl` | the 202 small tests, both modes, at master `b7fa7331` (post-rename, task #180) |
| `con-leche-verified-big.jsonl` | `cslib` |
| `setlec-verified.jsonl`, `setlec-trusted.jsonl` | the same 202 before the rename, at master `2664b1dd` — kept as the baseline the §9 diff is against |
| `setlec-verified-big.jsonl` | `init`, `std`, `cedar` (pre-rename; not re-measured, see DESIGN.md §7) |
| `official.jsonl` | the arena's own checker at v4.34.0-rc2 over the same 202 |

Provenance: arena `91f376e`, exports by `lean4export` 3.1.0 at
`leanprover/lean4:v4.29.1`.  Exit codes are the arena convention — 0 accept,
1 reject, 2 decline, 3 error.
