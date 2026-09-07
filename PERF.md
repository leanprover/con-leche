# PERF.md — the lech performance battery

| | |
|---|---|
| commit measured | `66b4190ced90c7e628a2d9c6aadf6ac62bbe18e5` |
| tree | clean checkout of `agent/perf-regen` at its merge of master 9f8afb32 (tasks #191 prelude, #192, #193 native predicate, #194, #196) plus task #187's verdict-line and tooling commits |
| date | 2026-09-06T21:37:34+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 22 GB, 8 h, `LECH_PROGRESS=5000`) |
| streams | preprocessed once off the clock by `lech-preprocess`; both checkers read the same bytes, lech under `--pre` |
| Mathlib stream | `<checkout>/_tmp/mathlib-scoping/mathlib-full-pre-idx.ndjson` (5 696 387 898 bytes), cut by the merged `lech-preprocess` in 391 s |
| concurrent load | other agents' builds and single-process checkers ran on the machine throughout; battery cells still ran strictly one at a time, and `instructions:u` is contention-independent |
| official kernel | `<main-checkout>/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| preprocessor | `<checkout>/.lake/build/bin/lech-preprocess` |
| lech binary | md5 `642fb47bb6f35156100e93d5c329d940` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.13 G | 8.38 G | 8.38 G | 1.37× | 1.37× |
| `beta-ladder` | 10.13 G | 40.42 G | 40.42 G | 3.99× | 3.99× |
| `init-prelude` | 3.18 G | 5.55 G | 7.13 G | 1.75× | 2.24× |
| `grind-ring-5` | 14.50 G | 26.32 G | 28.33 G | 1.82× | 1.95× |
| `app-lam` | 29.40 G | 161.44 G | 161.44 G | 5.49× | 5.49× |
| `init-full` | 406.30 G | 631.51 G | 655.22 G | 1.55× | 1.61× |
| `mathlib-full` | 10.64 T | 14.08 T | 15.42 T | 1.32× | 1.45× |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2509 | 0 / 2151 | 0 / 2151 |
| `grind-ring-5` | 0 / 2927 | 0 / 2607 | 0 / 2607 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 55346 | 0 / 53890 | 0 / 53890 |
| `mathlib-full` | 0 / 683531 | 0 / 665087 | 0 / 665087 |

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
| `mathlib-full` | 665092 | 665087 | 683531 | 5 | 525 | 6341 | 5680 | 575 | 86 |

## the Mathlib row, as data (not a measurement)

Wall time and resident memory on a shared 96-core machine are
**data**, not comparisons — `instructions:u` above is the
measurement.  These are here because they are the two numbers a
reader wants before pointing the checker at all of Mathlib.

| | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| wall | 33.5 min | 47.7 min | 54.1 min |
| peak RSS (`time -v`) | 9.19 GiB | 12.84 GiB | 12.84 GiB |

## Notes

* **What changed since the previous table** (`161cd827`).  Both the binary and the streams moved, and a control run separates them: THIS binary on the PREVIOUS table's own `init-full` stream gives official 413.02 G (previous table 413.14 G — unchanged, as it must be), `--trusted` 642.38 G (was 794.99 G) and `--verified` 668.05 G (was 841.70 G, 2.04× → 1.62× official).  So **−20.6 % of the verified column is the BINARY** — the landings between the two tables: #175 W2c/W3's direct indexed installs, #184's build-time split, #185's `CoreCfg` retirement, #186's rename to Lech, #191's built-in prelude, #192, #193's native-predicate fix and #194's canonical `PropWhen`; the split among them was not measured — and **a further −1.9 % is the REGENERATED stream** (655.22 G), cut by the current `lech-preprocess`, whose predicate installs structures, sums and indexed families natively: 548 of init-full's 610 inductive blocks now go through the direct route and only 57 are still modeled.  Every accepted count also changed UNIT (below), so no count here is comparable with the previous table's; and `mathlib-full` is new.
* **All of Mathlib, all three checkers, one stream.**  The `mathlib-full` row is the whole Mathlib export (`lean4export` 3.1.0, Lean 4.29.1, githash `f72c35b3f637c8c6571d353742168ab66cc22c00`), preprocessed once by the merged post-#193 `lech-preprocess` (391 s, 8.77 GiB, exit 0) into 5 696 387 898 B, and read by all three cells.  **Every cell accepts**: official 683 531 declarations, lech 665 087 declaration records in BOTH modes — and both numbers are exactly what the census predicts from the file, which is the row's own integrity check.  It is the first full-Mathlib ratio on identical bytes: **1.45× verified, 1.32× trusted**, i.e. BETTER than init-full's 1.61×/1.55 ×, so the corpus does not punish the checker at scale.  The lech cells ran under `LECH_PROGRESS=5000` (the user's ruling: the progress fold is an acceptable producer; measured cost on init-full −0.0006 %) with timestamped stderr kept beside the table.  An earlier attempt on a stream cut BEFORE task #193 declined at 7.5 % on `missing model for CategoryTheory.Presieve.ofArrows` — a preprocessor/installer predicate disagreement, found by this lane, fixed as #193, and visible in the census as 23 indexed families moving from native to modeled (109 → 86 indexed, 502 → 525 modeled).  See DESIGN task #187.
* **The verdict line counts declaration RECORDS** (task #187).  It
  used to print `env.consts.length`, the number of environment
  CONSTANTS, which counts an inductive block's type former, its
  constructors, its recursor and its projection table separately —
  a property of lech's representation that moved whenever the
  representation moved.  It now prints the STREAM's record count —
  `decls.size - preludeCount + preludeDropped` since task #191's
  built-in prelude, so a stream that re-declares a prelude block
  identically reports what it declared.  `LECH_VERBOSE=1` still
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

