# PERF.md — the lech performance battery

| | |
|---|---|
| commit measured | `fb2d7bf852715dbc6e95a1d7d53d468c1bf444ce` |
| tree | clean checkout of `agent/perf-regen` at fb2d7bf8 (master bd4dcf6a plus the task #187 verdict-line fix: the accepted count is the DECLARATION-RECORD count).  The branch tip adds one further commit that touches only comments and the `--help` text, so the measured binary is the one named below and the checking code is the tip's. |
| date | 2026-09-06T19:45:55+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 22 GB, 8 h, `LECH_PROGRESS=5000`) |
| streams | preprocessed once off the clock by `lech-preprocess`; both checkers read the same bytes, lech under `--pre` |
| Mathlib stream | `<checkout>/_tmp/mathlib-scoping/mathlib-full-pre-idx.ndjson` (5695851612 bytes) |
| concurrent load | other agents' builds and single-process checkers ran on the machine throughout (load 9-45 of 96 cores); battery cells still ran strictly one at a time, and `instructions:u` is contention-independent |
| official kernel | `<main-checkout>/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| preprocessor | `<checkout>/.lake/build/bin/lech-preprocess` |
| lech binary | md5 `da560a6a9aa744209283e711ae3a2b1d` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.13 G | 8.37 G | 8.37 G | 1.37× | 1.37× |
| `beta-ladder` | 10.13 G | 40.91 G | 40.92 G | 4.04× | 4.04× |
| `init-prelude` | 3.18 G | 5.60 G | 7.21 G | 1.76× | 2.27× |
| `grind-ring-5` | 14.51 G | 26.46 G | 28.52 G | 1.82× | 1.97× |
| `app-lam` | 29.43 G | 161.60 G | 161.61 G | 5.49× | 5.49× |
| `init-full` | 406.56 G | 641.61 G | 666.09 G | 1.58× | 1.64× |
| `mathlib-full` | 10.63 T | (2.44 T, exit 2 — partial) | (2.49 T, exit 2 — partial) | — | — |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2509 | 0 / 2151 | 0 / 2151 |
| `grind-ring-5` | 0 / 2927 | 0 / 2607 | 0 / 2607 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 55346 | 0 / 53890 | 0 / 53890 |
| `mathlib-full` | 0 / 683420 | 2 / — | 2 / — |

Exit codes: 0 accept, 1 reject, 2 decline, 3 error.

## the input: what each stream contains

Properties of the preprocessed FILE, computed by
`scripts/stream-census.py` — nobody's environment representation
enters here.  `records` is the number of declaration records in the
file; `lech` and `official` are what each checker's verdict line
reports on it, both derived from the file alone (see the count note
below).  The native blocks are the inductive records the
preprocessor left for lech to install directly, split by shape.

| stream | records | lech | official | pinned | modeled | native | structures | sums | indexed |
|---|---|---|---|---|---|---|---|---|---|
| `let-ladder` | 13 | 13 | 19 | 2 | 0 | 2 | 2 | 0 | 0 |
| `beta-ladder` | 11 | 11 | 17 | 3 | 0 | 1 | 1 | 0 | 0 |
| `init-prelude` | 2156 | 2151 | 2509 | 5 | 11 | 133 | 115 | 16 | 2 |
| `grind-ring-5` | 2611 | 2607 | 2927 | 4 | 17 | 106 | 88 | 14 | 4 |
| `app-lam` | 21 | 21 | 31 | 2 | 0 | 4 | 4 | 0 | 0 |
| `init-full` | 53895 | 53890 | 55346 | 5 | 57 | 548 | 487 | 47 | 14 |
| `mathlib-full` | 664981 | 664976 | 683420 | 5 | 502 | 6364 | 5680 | 575 | 109 |

## the Mathlib row, as data (not a measurement)

Wall time and resident memory on a shared 96-core machine are
**data**, not comparisons — `instructions:u` above is the
measurement.  These are here because they are the two numbers a
reader wants before pointing the checker at all of Mathlib.

| | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| wall | 32.4 min | 4.4 min (partial) | 4.6 min (partial) |
| peak RSS (`time -v`) | 9.19 GiB | 12.82 GiB (partial) | 12.82 GiB (partial) |

## Notes

* **What changed since the previous table** (`161cd827`, 09:14 the same day).  Both the binary and the streams moved, and a control run separates them: THIS binary on the PREVIOUS table's own `init-full` stream gives official 412.89 G (previous table 413.14 G — unchanged, as it must be), `--trusted` 652.61 G (was 794.99 G) and `--verified` 679.07 G (was 841.70 G).  So −19.3 % of the verified column is the BINARY — the landings between the two tables: task #175's W2c/W3 direct indexed installs, #184's build-time split, #185's `CoreCfg` retirement (the mode is now the cores' only parameter) and #186's rename to Lech; the split among them was not measured — and a further −1.9 % is the REGENERATED stream (666.09 G), cut by the current `lech-preprocess`, whose predicate installs structures, sums and indexed families natively: 548 of init-full's 610 inductive blocks now go through the direct route and only 57 are still modeled.  Every accepted count also changed UNIT (next note), so no count here is comparable with the previous table's.
* **The `mathlib-full` lech cells do not accept — a finding, not a measurement.**  Both exit 2 (decline) after ~4.5 min at fold position 49 833 of 664 976 (7.5 %) on `missing model for CategoryTheory.Presieve.ofArrows`.  That block (read out of the stream: `numParams` 6, `numIndices` 2, one constructor with one field, non-recursive, non-nested, and a recursor whose level parameters are exactly the type's — the SMALL eliminator of a `Prop`-valued family) passes every conjunct the widened `lech-preprocess` predicate mirrors, so it is left native with no `_model`; lech's direct indexed installer then does not take it, and the frontend, finding neither a native install nor a model, declines.  `LechPreprocess.lean`'s header names the exposure itself: two conjuncts — `directCtorResidOk`'s residual shape and the rules' right-hand sides — are *argued rather than mirrored*, and the `tests/native-agree.sh` it promises does not exist.  So the preprocessor's native class is not conservative with respect to the installer's; closing that gap, and building the agreement check, is task #193, after which the stream is re-cut and the two cells re-run.  This is a predicate disagreement, not a soundness problem and not a checker regression: official accepts the same bytes outright (exit 0, 683 420 declarations), and the SAME binary accepts the PRE-#175 Mathlib stream end to end — 670 977 declaration records, exit 0, 16.10 T instructions:u, 57:02.76 wall, 12.88 GiB peak RSS, matching master `124c083f`'s acceptance run to three seconds (DESIGN task #187 §4).
* **The verdict line counts declaration RECORDS** (task #187).  It
  used to print `env.consts.length`, the number of environment
  CONSTANTS, which counts an inductive block's type former, its
  constructors, its recursor and its projection table separately —
  a property of lech's representation that moved whenever the
  representation moved.  It now prints the parsed `DeclC` count: one
  per accepted stream declaration record.  `LECH_VERBOSE=1` still
  prints the constant count, on stderr, beside it.
* **The official number is not a record count either.**  Its
  `Main.lean` prints `constMap.size`: one entry per exported
  constant, so an inductive record contributes its type formers, its
  constructors AND its recursors, less the three `Quot.mk`/`.lift`/
  `.ind` entries it erases before replay.  Both numbers are now
  functions of the input file alone, and the census table above
  reproduces each of them exactly from the bytes.
* **Cross-pipeline, not same-work.**  Both sides read the same bytes,
  but a lech cell installs the native blocks through its own direct
  route and the rest through a *modeled* encoding, and runs an
  `annotate` pass with no official counterpart, while official checks
  that file with native inductive/recursor support throughout.
* **`--trusted` under-checks install-only kinds** (axioms, inductive
  blocks, quot, the pinned-cert branches run at io grade), which
  flatters the trusted column on inductive-heavy streams.
* One run per cell on a shared machine: `instructions:u` is
  contention-independent, so a cell may overlap other work; wall time
  is not reported for that reason (the Mathlib row's minutes are
  labelled as data, above).
* Regenerate with `lake build lech && scripts/perf-tables.sh`;
  `--render` re-renders from `perf-data/` without measuring, and
  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream.  The
  `mathlib-full` row needs its stream cut by hand first (the
  preprocessor is itself a Mathlib-scale process).  Raw cells (with
  wall time and load) are tracked in `perf-data/table.tsv`, the input
  census in `perf-data/census.tsv`, provenance in `perf-data/meta.txt`.

