# PERF.md — the con-leche performance battery

| | |
|---|---|
| commit measured | `1d470aa7ce0b933b0c5559d83a7f9d4e20e7a39b` |
| tree | master at the commit above: the two-phase fold — every record installed, then every recorded declaration checked against the prefix view of the installed index — over the hand-rolled `lean4export` parser. |
| date | 2026-09-10T17:41:04+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 22 GB, 8 h, `--progress=5000`) |
| check phase | one worker: every con-leche cell passes `--jobs=1` (the worker-count table below is the parallel lane) |
| streams | `lean4export` NDJSON, read unchanged by both checkers |
| Mathlib stream | `<checkout>/_tmp/mathlib-scoping/mathlib-full.ndjson` (5636308621 bytes, raw) |
| concurrent load | shared machine throughout — the per-cell load average is recorded in `perf-data/table.tsv` |
| official kernel | `<checkout>/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| con-leche binary | md5 `625a61babe10de48dde3ced724ad0f13` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.13 G | 8.06 G | 8.06 G | 1.31× | 1.31× |
| `beta-ladder` | 10.12 G | 39.94 G | 39.95 G | 3.95× | 3.95× |
| `init-prelude` | 2.21 G | 3.04 G | 3.20 G | 1.38× | 1.45× |
| `grind-ring-5` | 13.41 G | 21.54 G | 22.69 G | 1.61× | 1.69× |
| `app-lam` | 29.41 G | 157.30 G | 157.31 G | 5.35× | 5.35× |
| `init-full` | 403.44 G | 521.13 G | 538.46 G | 1.29× | 1.33× |
| `mathlib-full` | 10.54 T | 11.16 T | 12.01 T | 1.06× | 1.14× |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2056 | 0 / 1773 | 0 / 1773 |
| `grind-ring-5` | 0 / 2429 | 0 / 2181 | 0 / 2181 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 54472 | 0 / 53088 | 0 / 53088 |
| `mathlib-full` | 0 / 670627 | 0 / 654499 | 0 / 654499 |

Exit codes: 0 accept, 1 reject, 2 decline, 3 error.

## the input: what each stream contains

Properties of the FILE, computed by
`scripts/stream-census.py` — nobody's environment representation
enters here.  `records` is the number of declaration records in the
file; `con-leche` and `official` are what each checker's verdict line
reports on it, both derived from the file alone (see the count note
below).  `pinned` counts the basis blocks the parse matches;
`native` is every other inductive block, which con-leche installs
itself (the fixpoint route, or a model it generates in process),
split by shape.

**The `con-leche` column IS the verdict line's count.**  The
in-process modeller's generated records (30 on `init-prelude`,
`grind-ring-5` and `init-full` — `Lean.Syntax`'s; 2 168 on
`mathlib-full`, for the 51 blocks modelled in process there) are
booked as declarations of the fold, never as records of the file,
so the census predicts the verdict.  The instruction cells count
the same checked records either way.

| stream | records | con-leche | official | pinned | native | structures | sums | indexed |
|---|---|---|---|---|---|---|---|---|
| `let-ladder` | 13 | 13 | 19 | 2 | 2 | 2 | 0 | 0 |
| `beta-ladder` | 11 | 11 | 17 | 3 | 1 | 1 | 0 | 0 |
| `init-prelude` | 1777 | 1773 | 2056 | 5 | 121 | 104 | 14 | 3 |
| `grind-ring-5` | 2185 | 2181 | 2429 | 4 | 101 | 78 | 16 | 7 |
| `app-lam` | 21 | 21 | 31 | 2 | 4 | 4 | 0 | 0 |
| `init-full` | 53093 | 53088 | 54472 | 5 | 583 | 477 | 59 | 47 |
| `mathlib-full` | 654504 | 654499 | 670627 | 5 | 6639 | 5683 | 634 | 322 |

## the Mathlib row, as data (not a measurement)

Wall time and resident memory on a shared 96-core machine are
**data**, not comparisons — `instructions:u` above is the
measurement.  These are here because they are the two numbers a
reader wants before pointing the checker at all of Mathlib.

| | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| wall | 30.7 min | 17.5 min | 19.0 min |
| peak RSS (`time -v`) | 9.16 GiB | 7.87 GiB | 7.87 GiB |

## the check phase on more than one thread

The check phase runs on `--jobs=<n>` worker threads; the parse and
the install phase before it are sequential.  Wall time on a shared
machine is **indicative only** — `instructions:u` above is the
measurement, and it is taken at one worker.  What the worker count
shortens is the check phase alone: on `mathlib-full` that phase
takes 962 s at one worker, 263 s at four and 142 s at eight, and the
instruction count moves 0.2 % across the three (12.01 T, 12.04 T,
12.04 T).  The wall times below are that phase plus the sequential
prefix, which no worker count shortens.

| stream | `--jobs=1` | `--jobs=4` | `--jobs=8` |
|---|---|---|---|
| `init-full` | 50 s | 17 s | 11 s |
| `mathlib-full` | 19.1 min | 7.4 min | 5.4 min |

Each worker reserves about a gigabyte of ADDRESS SPACE — its stack reservation, committed lazily, so the resident set grows by some 25 MB per worker — and a run under an `ulimit -v` can afford only so many of them: the `init-full` cells above are measured under 16 GB, the `mathlib-full` cells under 32 GB.  Only the check phase runs on the pool.  On `mathlib-full` the sequential prefix ahead of it is 26 s of parse and 150 s of install — 16 % of the one-worker run and 56 % of the eight-worker one, which is the floor no worker count goes below.

## Notes

* **All of Mathlib, all three checkers, one stream.**  The `mathlib-full` row is the whole export (`lean4export` 3.1.0, Lean 4.29.1, 5 636 308 621 B), read by all three cells.  **Every cell accepts**: official 670 627 declarations, con-leche 654 499 declaration records in BOTH modes — **1.14× verified, 1.06× trusted**; the smaller `init-full` stream sits at 1.33× / 1.29×.  The count difference is the official binary's counting (see below), not a verdict difference.
* **The verdict line counts declaration RECORDS**, the FILE's own count
  `decls.size - genRecords` (the file's own records: the built-in
  prelude adds none, since the stream's own record is what is used
  wherever it has one),
  not the number of environment CONSTANTS, which would count an
  inductive block's type former, its constructors, its recursor and
  its projection table separately — a property of con-leche's
  representation.  `scripts/stream-census.py` derives both numbers
  from the stream.
* **The official number is not a record count either.**  Its
  `Main.lean` prints `constMap.size`: one entry per exported
  constant, so an inductive record contributes its type formers, its
  constructors AND its recursors, less the three `Quot.mk`/`.lift`/
  `.ind` entries it erases before replay.  Both numbers are
  functions of the input file alone, and the census table above
  reproduces each of them exactly from the bytes.
* **Same bytes, same job — but not the same work.**  Both sides read
  the same file and install every inductive block themselves.
  con-leche installs single blocks through its fixpoint route and a
  mutual/nested one through a `_model` family it GENERATES and then
  checks as ordinary declarations (the certification tax), and runs
  an `annotate` pass with no official counterpart; official has
  native inductive/recursor support.
* **`--trusted` under-checks install-only kinds** (axioms, inductive
  blocks, quot, the pinned-cert branches run at io grade), which
  flatters the trusted column on inductive-heavy streams.
* **The cells are the single-worker lane.**  Every con-leche cell passes
  `--jobs=1` — one worker thread, no shared claim counter and no
  result table — which is the apples-to-apples comparison against a
  single-threaded official kernel; without the flag the check phase
  takes one worker per hardware thread.  The worker-count table above
  is where the parallel lane is reported, in wall time.
* One run per cell on a shared machine: `instructions:u` is
  contention-independent, so a cell may overlap other work.  The only
  wall times here are the Mathlib row's and the worker-count table's,
  both labelled as data.
* Regenerate with `lake build con-leche && scripts/perf-tables.sh`;
  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream, and
  `scripts/perf-tables-render.py perf-data/table.tsv PERF.md
  perf-data/meta.txt perf-data/census.tsv` — which is what
  `scripts/perf-tables.sh --render` runs — re-renders this file from
  the tracked record without measuring.  The `mathlib-full` row needs
  its stream exported by hand first.  Per-cell data (with wall time
  and load) are tracked in `perf-data/table.tsv`, the input census in
  `perf-data/census.tsv`, provenance in `perf-data/meta.txt`.  The
  worker-count table is a sweep of its own, which the battery does not
  run; its cells are tracked in `perf-data/parallel.tsv`.

