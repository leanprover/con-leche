# PERF.md — the lech performance battery

| | |
|---|---|
| commit measured | `161cd827fe729dd63d0148b8559bfb6a3631ec4e` |
| tree | clean checkout of master `161cd827` (the mode rename + the ungated fast `isProof` arms and `pw` writers); no commits above master |
| date | 2026-09-06T09:14:28+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` |
| streams | preprocessed once off the clock by `lean-inductive-models`; both checkers read the same bytes, lech under `--pre` |
| concurrent load | other agents ran unrelated single-process checkers on the machine throughout (load ~19 of 96 cores); battery cells still ran strictly one at a time, and `instructions:u` is contention-independent |
| official kernel | `<main-checkout>/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| preprocessor | `<main-checkout>/_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.16 G | 8.45 G | 8.46 G | 1.37× | 1.37× |
| `beta-ladder` | 10.15 G | 41.22 G | 41.20 G | 4.06× | 4.06× |
| `init-prelude` | 3.91 G | 6.88 G | 8.98 G | 1.76× | 2.30× |
| `grind-ring-5` | 15.72 G | 27.97 G | 31.59 G | 1.78× | 2.01× |
| `app-lam` | 29.45 G | 162.43 G | 162.50 G | 5.52× | 5.52× |
| `init-full` | 413.14 G | 794.99 G | 841.70 G | 1.92× | 2.04× |

## exit code / accepted declarations

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 62 | 0 / 66 | 0 / 66 |
| `beta-ladder` | 0 / 50 | 0 / 53 | 0 / 53 |
| `init-prelude` | 0 / 3489 | 0 / 3606 | 0 / 3606 |
| `grind-ring-5` | 0 / 3775 | 0 / 3866 | 0 / 3866 |
| `app-lam` | 0 / 88 | 0 / 94 | 0 / 94 |
| `init-full` | 0 / 60060 | 0 / 60549 | 0 / 60549 |

Exit codes: 0 accept, 1 reject, 2 decline, 3 error.

## Notes

* **What changed since the previous table.**  Two landings, no method change.  (i) Since task #175 S1 a direct structure's projection table is ONE stored constant per structure instead of one per field, so every lech accepted-declaration count drops with no verdict change: init-full 60 549 (was 61 048), grind-ring-5 3 866 (3 946), init-prelude 3 606 (3 653), app-lam 94 (97), let-ladder 66 (69), beta-ladder 53 (56).  (ii) Since the 2026-09-06 mode rename the trusted mode WRITES the `pw` binder annotations and runs the fast `isProof` head-symbol arms exactly as the verified mode does — only *validating* the annotations and producing certificates stays certification-only.
* **Cross-pipeline, not same-work.**  Both sides read the same bytes,
  but every lech cell checks a *modeled* encoding of the inductive
  blocks plus an `annotate` pass with no official counterpart, while
  official checks that file with native inductive/recursor support.
  Hence the accepted-declaration counts differ too.
* **`--trusted` under-checks install-only kinds** (axioms, inductive
  blocks, quot, the pinned-cert branches run at io grade), which
  flatters the trusted column on inductive-heavy streams.
* One run per cell on a shared machine: `instructions:u` is
  contention-independent, so a cell may overlap other work; wall time
  is not reported for that reason.
* Regenerate with `lake build lech && scripts/perf-tables.sh`;
  `--render` re-renders from `perf-data/` without measuring, and
  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream.  Raw cells
  (with wall time and load, recorded but not printed) are tracked in
  `perf-data/table.tsv`, provenance in `perf-data/meta.txt`.

