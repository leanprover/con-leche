# PERF.md — the setlec performance battery

| | |
|---|---|
| commit measured | `10d130f2dfa62eaa34a01cb322d006ce64540bb3` |
| tree | the merge of master `8f9e8250` (task #175 W6) with the perf-tables tooling commits; the commits above master touch only `scripts/` |
| date | 2026-09-06T01:37:21+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · parity `--no-model` · P `--set-model=p` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` |
| streams | preprocessed once off the clock by `lean-inductive-models`; both checkers read the same bytes, setlec under `--pre` |
| concurrent load | one unrelated single-process checker run (the Mathlib frontier campaign, one core of 96) was live on the machine throughout; battery cells still ran strictly one at a time |
| official kernel | `/home/joachim/setlec/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| preprocessor | `/home/joachim/setlec/_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models` |

## instructions:u

| stream | official v4.33.0 | parity `--no-model` | P `--set-model=p` | parity ÷ official | P ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.16 G | 9.83 G | 9.84 G | 1.60× | 1.60× |
| `beta-ladder` | 10.15 G | 40.78 G | 52.08 G | 4.02× | 5.13× |
| `init-prelude` | 3.91 G | 9.11 G | 11.30 G | 2.33× | 2.89× |
| `grind-ring-5` | 15.73 G | 37.50 G | 37.38 G | 2.38× | 2.38× |
| `app-lam` | 29.44 G | 208.62 G | 208.97 G | 7.09× | 7.10× |
| `init-full` | 412.93 G | 1085.56 G | 987.05 G | 2.63× | 2.39× |

## exit code / accepted declarations

| stream | official v4.33.0 | parity `--no-model` | P `--set-model=p` |
|---|---|---|---|
| `let-ladder` | 0 / 62 | 0 / 69 | 0 / 69 |
| `beta-ladder` | 0 / 50 | 0 / 56 | 0 / 56 |
| `init-prelude` | 0 / 3489 | 0 / 3653 | 0 / 3653 |
| `grind-ring-5` | 0 / 3775 | 0 / 3946 | 0 / 3946 |
| `app-lam` | 0 / 88 | 0 / 97 | 0 / 97 |
| `init-full` | 0 / 60060 | 0 / 61048 | 0 / 61048 |

Exit codes: 0 accept, 1 reject, 2 decline, 3 error.

## Notes

* **Cross-pipeline, not same-work.**  Both sides read the same bytes,
  but every setlec cell checks a *modeled* encoding of the inductive
  blocks plus an `annotate` pass with no official counterpart, while
  official checks that file with native inductive/recursor support.
  Hence the accepted-declaration counts differ too.
* **`--no-model` under-checks install-only kinds** (axioms, inductive
  blocks, quot, the pinned-cert branches run at io grade), which
  flatters the parity column on inductive-heavy streams.
* One run per cell on a shared machine: `instructions:u` is
  contention-independent, so a cell may overlap other work; wall time
  is not reported for that reason.
* Regenerate with `lake build setlec && scripts/perf-tables.sh`;
  `--render` re-renders from `perf-data/` without measuring, and
  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream.  Raw cells
  (with wall time and load, recorded but not printed) are tracked in
  `perf-data/table.tsv`, provenance in `perf-data/meta.txt`.

