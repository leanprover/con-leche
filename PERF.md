# PERF.md — the con-leche performance battery

| | |
|---|---|
| commit measured | `403a415236c4c21b0f72531ec4e0cd8643660d29` |
| tree | master `403a4152`, measured END TO END IN ONE SESSION — one pair of binaries, one set of streams, **not one cell carried forward** (the #313–#319 batteries carried the `official` column and the whole `mathlib-full` row; this one measures them).  The `official v4.33.0` binary was rebuilt for it from the arena's own source (`leanprover/lean-kernel-arena` `checkers/official-v4.33.0` at `aa259bf^`, the last revision that carried that directory; `echo leanprover/lean4:v4.33.0 > lean-toolchain && lake build`; md5 `6125c70e83490973a07be2ea69523a2c`).  The `mathlib-full` stream was re-exported for it: `lean4export` at `15f6055` (the `chore: bump toolchain to v4.33.0` commit) over the `Mathlib` module of mathlib4 `6f1ef4e5` (the last mathlib4 commit on v4.33.0), **6 069 002 157 bytes, 107 820 903 lines, 691 203 declaration records** — a different and 7.7 % larger stream than the 5 636 308 621-byte one the carried-forward row quoted, which was a Lean 4.29.1 export of an older Mathlib.  `init-full` is the #307 export (`lean4export` of `Init` at v4.33.0, 57 977 declarations, 347 714 179 bytes), unchanged.  Reproduction: `init-full` verified 453.96 G against #319's 453.95 G (+0.003 %), trusted 437.78 G against 437.78 G; the Mathlib prefix (off-battery, same session) verified 658.10 G against #319's 658.03 G (+0.01 %), trusted 630.70 G against 630.65 G. |
| date | 2026-09-20T21:19:23+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 22 GB, 8 h, `--progress=5000`) |
| check phase | one worker: every con-leche cell passes `--jobs=1` (the worker-count table below is the parallel lane) |
| streams | `lean4export` NDJSON, read unchanged by both checkers |
| Mathlib stream | `<checkout>/_tmp/mathlib-scoping/mathlib-full.ndjson` (6069002157 bytes, 107820903 lines, raw) |
| concurrent load | shared machine throughout — the per-cell load average is recorded in `perf-data/table.tsv` |
| official kernel | `<checkout>/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| con-leche binary | md5 `f037fae3a24949427026eaf835ad288f` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.12 G | 2.71 G | 2.71 G | 0.44× | 0.44× |
| `beta-ladder` | 10.13 G | 13.92 G | 13.93 G | 1.37× | 1.38× |
| `init-prelude` | 2.21 G | 2.36 G | 2.49 G | 1.07× | 1.13× |
| `grind-ring-5` | 13.42 G | 16.30 G | 17.41 G | 1.22× | 1.30× |
| `app-lam` | 29.42 G | 70.65 G | 70.66 G | 2.40× | 2.40× |
| `init-full` | 439.59 G | 437.78 G | 453.96 G | 1.00× | 1.03× |
| `mathlib-full` | 10.26 T | 7.43 T | 8.10 T | 0.72× | 0.79× |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2056 | 0 / 1777 | 0 / 1777 |
| `grind-ring-5` | 0 / 2429 | 0 / 2185 | 0 / 2185 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 59430 | 0 / 57977 | 0 / 57977 |
| `mathlib-full` | 0 / 707578 | 0 / 691203 | 0 / 691203 |

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
`grind-ring-5` and `init-full` — `Lean.Syntax`'s; 2 072 on
`mathlib-full`, for the 49 blocks modelled in process there) are
booked as declarations of the fold, never as records of the file,
so the census predicts the verdict.  The instruction cells count
the same checked records either way.

| stream | records | con-leche | official | pinned | native | structures | sums | indexed |
|---|---|---|---|---|---|---|---|---|
| `let-ladder` | 13 | 13 | 19 | 2 | 2 | 2 | 0 | 0 |
| `beta-ladder` | 11 | 11 | 17 | 3 | 1 | 1 | 0 | 0 |
| `init-prelude` | 1777 | 1777 | 2056 | 5 | 121 | 104 | 14 | 3 |
| `grind-ring-5` | 2185 | 2185 | 2429 | 4 | 101 | 78 | 16 | 7 |
| `app-lam` | 21 | 21 | 31 | 2 | 4 | 4 | 0 | 0 |
| `init-full` | 57977 | 57977 | 59430 | 5 | 610 | 493 | 63 | 54 |
| `mathlib-full` | 691203 | 691203 | 707578 | 5 | 6714 | 5764 | 604 | 346 |

## the Mathlib row, as data (not a measurement)

Wall time and resident memory on a shared 96-core machine are
**data**, not comparisons — `instructions:u` above is the
measurement.  These are here because they are the two numbers a
reader wants before pointing the checker at all of Mathlib.

| | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| wall | 29.6 min | 13.4 min | 15.1 min |
| peak RSS (`time -v`) | 11.40 GiB | 8.31 GiB | 8.33 GiB |

## the check phase on more than one thread

The check phase runs on `--jobs=<n>` worker threads; the parse and
the install phase before it are sequential.  Wall time on a shared
machine is **indicative only** — `instructions:u` above is the
measurement, and it is taken at one worker.  What the worker count
shortens is the check phase alone: on `mathlib-full` that phase
takes 718 s at one worker, 202 s at four and 120 s at eight, and the
instruction count moves 0.3 % across the three (8.10 T, 8.12 T,
8.12 T).  The wall times below are that phase plus the sequential
prefix, which no worker count shortens.

| stream | `--jobs=1` | `--jobs=4` | `--jobs=8` |
|---|---|---|---|
| `init-full` | 45 s | 15 s | 10 s |
| `mathlib-full` | 14.4 min | 5.9 min | 4.5 min |

Each worker reserves about a gigabyte of ADDRESS SPACE — its stack reservation, committed lazily, so the resident set grows by some 25 MB per worker — and a run under an `ulimit -v` can afford only so many of them: the `init-full` cells above are measured under 16 GB, the `mathlib-full` cells under 32 GB.  Only the check phase runs on the pool.  On `mathlib-full` the sequential prefix ahead of it is 23.8 s of parse and 121.0 s of install — 17 % of the one-worker run and 54 % of the eight-worker one, which is the floor no worker count goes below.

## Notes

* **All of Mathlib, all three checkers, one stream — and con-leche is the faster one.**  The `mathlib-full` row is the whole export described in the header (`lean4export` 3.1.0 at Lean 4.33.0, mathlib4 `6f1ef4e5`, 6 069 002 157 B).  **Every cell accepts**: official 707 578 declarations, con-leche 691 203 declaration records in BOTH modes, at **0.79× verified and 0.72× trusted** — where `init-full` sits at 1.03× / 1.00× and the Mathlib prefix (131 902 records, measured off-battery in the same session) at 1.02× / 0.98×.  The count difference is the official binary's counting (see below), not a verdict difference.  **Where the difference comes from, measured.**  (1) *Parsing.*  The official checker's `--parse-only` mode costs a flat 306 instructions per input byte — 106.83 G on `init-full`'s 347.7 MB, 180.70 G on the prefix's 590.9 MB, 1 852.39 G on this row's 6 069.0 MB (307.2 / 305.8 / 305.2 instr/B) — so reading the file is **18.0 % of its full-Mathlib run** (24.3 % of `init-full`, 28.0 % of the prefix).  con-leche's parse phase is ~1 % of its instructions (#307's profile of the prefix) and 23.8 s of an 863 s run.  Take the parse off both sides and the verified ratio moves from 0.79× to **0.95×**.  (2) *The check phase itself.*  Official's check costs 3.37 M instructions per declaration on the prefix and 11.89 M on all of Mathlib — **×3.53** — where con-leche's per-record cost goes 4.99 M → 11.72 M, ×2.35; so the check phases, 1.40× apart on the prefix and 1.35× apart on `init-full`, land at 0.95× on the whole library.  A `perf record` of the official binary on both streams puts that extra growth in its structural-equality path and its caches: `lean::expr_eq_fn` 2.8 % → 4.9 % of the run (×5.4 per declaration) and the `std::unordered_map` caches 12.0 % → 14.6 % (×3.8), against substitution ×3.0 and the allocator ×3.3.  Mathlib's later declarations are ~3× heavier per declaration for BOTH checkers; official's per-declaration cost simply grows the faster of the two.
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

