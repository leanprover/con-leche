# PERF.md — con-leche against the official kernel

con-leche (`--verified`, its default mode) against the official v4.33.0 kernel, on the same `lean4export` streams, read unchanged by both.  The measurement is `perf stat -e instructions:u`, one run per cell, with con-leche at `--jobs=1` to match the single-threaded official checker.  Wall time and memory appear only as data: the machine is shared.

| | |
|---|---|
| con-leche | `cfa7cd1df`, built with Lean v4.36.0 |
| official | the lean-kernel-arena's `checkers/official-v4.33.0` (md5 `6125c70e83490973a07be2ea69523a2c`) |
| streams | Lean v4.33.0 `lean4export` NDJSON: the arena's tests, `Init`, and `Mathlib` at mathlib4 `6f1ef4e5` |
| date | 2026-11-25 |
| machine | AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM |

## Instructions, one worker

| stream | official v4.33.0 | con-leche | ratio | declarations (official v4.33.0 / con-leche) |
|---|---|---|---|---|
| `let-ladder` | 6.13 G | 2.56 G | 0.42× | 22 / 13 |
| `beta-ladder` | 10.13 G | 4.94 G | 0.49× | 20 / 11 |
| `init-prelude` | 2.21 G | 1.11 G | 0.50× | 2056 / 1777 |
| `grind-ring-5` | 13.42 G | 8.65 G | 0.64× | 2429 / 2185 |
| `app-lam` | 29.41 G | 22.09 G | 0.75× | 34 / 21 |
| `init-full` | 439.85 G | 253.37 G | 0.58× | 59430 / 57977 |
| `mathlib-full` | 10.26 T | 5.06 T | 0.49× | 707578 / 691203 |

## All of Mathlib: wall time and memory

| | official v4.33.0 | con-leche `--jobs=1` |
|---|---|---|
| wall | 32.6 min | 7.4 min |
| peak RSS | 11.41 GiB | 4.29 GiB |

## More than one worker

At `--jobs=<n>` the parse, the install and the check run on `<n>` threads.  Wall time, median of five runs (min–max), `--verified`.

| stream | `--jobs=1` | `--jobs=4` | `--jobs=8` |
|---|---|---|---|
| `init-full` | 22.6 s (22.4–22.6) | 6.1 s (6.0–6.2) | 3.7 s (3.5–3.8) |
| `mathlib-full` | 7.4 min (7.4–7.9) | 2.2 min (2.2–2.2) | 70.6 s (70.1–75.0) |

## Notes

* Parsing is a large share of the official run: its `--parse-only` mode costs about 306 instructions per input byte, 106.83 G on `init-full` and 1.85 T on `mathlib-full`.  Against the official run without its parse, con-leche's whole run (its own parse included) is 0.76× on `init-full` and 0.60× on `mathlib-full`.
* The declaration counts differ by counting, not by verdict: con-leche reports the declaration records in the file, official the size of its constant map (every constructor and recursor counted separately).  `scripts/stream-census.py` derives both from the file.
* Regenerate: `lake build con-leche && scripts/perf-tables.sh` (the battery), `scripts/perf-tables.sh --parallel` (the worker-count sweep), `scripts/perf-tables.sh --render` (re-render from `perf-data/`).  The `mathlib-full` stream is exported by hand first; the recipe is in `scripts/perf-tables.sh`.

