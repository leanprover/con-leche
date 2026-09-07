# PERF.md — the con-leche performance battery

| | |
|---|---|
| commit measured | `b33f38d9eee583117c7a9defe441486a64d95ecb` |
| tree | task #207: the first table on RAW streams — the lean-inductive-models preprocessor was dropped, so both checkers now read the same raw lean4export bytes and do the same job (con-leche installs every inductive block itself). No cell here is comparable with an earlier PERF.md. |
| date | 2026-09-07T18:10:59+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 22 GB, 8 h, `CON_LECHE_PROGRESS=5000`) |
| streams | RAW `lean4export` NDJSON; both checkers read the same bytes and do the same job (task #207: there is no preprocessing step, so these numbers are not comparable with any earlier PERF.md) |
| Mathlib stream | `<checkout>/_tmp/mathlib-scoping/mathlib-full.ndjson` (5636308621 bytes, raw) |
| official kernel | `<checkout>/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| con-leche binary | md5 `8eb8790c9c93659142491a61930e375a` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.13 G | 8.31 G | 8.31 G | 1.36× | 1.36× |
| `beta-ladder` | 10.13 G | 39.43 G | 39.43 G | 3.89× | 3.89× |
| `init-prelude` | 2.21 G | 4.41 G | 4.55 G | 2.00× | 2.06× |
| `grind-ring-5` | 13.40 G | 25.29 G | 26.11 G | 1.89× | 1.95× |
| `app-lam` | 29.40 G | 158.01 G | 158.01 G | 5.37× | 5.37× |
| `init-full` | 403.46 G | 654.11 G | 673.17 G | 1.62× | 1.67× |
| `mathlib-full` | 10.54 T | (3.15 T, exit 2 — partial) | (3.19 T, exit 2 — partial) | — | — |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2056 | 0 / 1803 | 0 / 1803 |
| `grind-ring-5` | 0 / 2429 | 0 / 2211 | 0 / 2211 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 54472 | 0 / 53118 | 0 / 53118 |
| `mathlib-full` | 0 / 670627 | 2 / — | 2 / — |

Exit codes: 0 accept, 1 reject, 2 decline, 3 error.

## the input: what each stream contains

Properties of the raw FILE, computed by
`scripts/stream-census.py` — nobody's environment representation
enters here.  `records` is the number of declaration records in the
file; `con-leche` and `official` are what each checker's verdict line
reports on it, both derived from the file alone (see the count note
below).  `modeled` counts blocks the STREAM carries a `_model`
family for — 0 on every raw stream since task #207; `native` is the
rest, which con-leche installs itself (a direct route, or a model
it generates in-process), split by shape.

**The `con-leche` column is the FILE's count and is lower than the
verdict line's** on any stream with a mutual or nested block: the
in-process modeller pushes its generated records ahead of the block
and the fold counts them, but they are not in the file, so this
census cannot see them (on `init-prelude`, `grind-ring-5` and
`init-full` the gap is exactly 30 — `Lean.Syntax`'s generated
family; `CON_LECHE_INMODEL_DUMP`'s output censuses to the verdict
number exactly).  Before task #207 the models arrived IN the file,
so the two agreed.  The exit-code table above carries the verdict
counts.

| stream | records | con-leche | official | pinned | modeled | native | structures | sums | indexed |
|---|---|---|---|---|---|---|---|---|---|
| `let-ladder` | 13 | 13 | 19 | 2 | 0 | 2 | 2 | 0 | 0 |
| `beta-ladder` | 11 | 11 | 17 | 3 | 0 | 1 | 1 | 0 | 0 |
| `init-prelude` | 1777 | 1773 | 2056 | 5 | 0 | 121 | 104 | 14 | 3 |
| `grind-ring-5` | 2185 | 2181 | 2429 | 4 | 0 | 101 | 78 | 16 | 7 |
| `app-lam` | 21 | 21 | 31 | 2 | 0 | 4 | 4 | 0 | 0 |
| `init-full` | 53093 | 53088 | 54472 | 5 | 0 | 583 | 477 | 59 | 47 |
| `mathlib-full` | 654504 | 654499 | 670627 | 5 | 0 | 6639 | 5683 | 634 | 322 |

## the Mathlib row, as data (not a measurement)

Wall time and resident memory on a shared 96-core machine are
**data**, not comparisons — `instructions:u` above is the
measurement.  These are here because they are the two numbers a
reader wants before pointing the checker at all of Mathlib.

| | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| wall | 31.3 min | 4.5 min (partial) | 4.8 min (partial) |
| peak RSS (`time -v`) | 9.17 GiB | 8.60 GiB (partial) | 8.61 GiB (partial) |

## Notes

* **Nothing here is comparable with the previous table.**  Every published cell before this one was measured on a PREPROCESSED stream, with `con-leche --pre` on one side and the same preprocessed bytes on official's; task #207 dropped the preprocessor, so both checkers now read the RAW `lean4export` export and do the same job — con-leche installs every inductive block itself.  The like-for-like control, on `init-full` `--verified`: **668.05 G** on the preprocessed stream (previous table) against **673.17 G** raw — **+0.8 %**, the price of installing the blocks ourselves.  Official moves the other way, 413.02 G → 403.46 G (**−2.3 %**), since the raw stream carries no model families; hence the ratio 1.62× → **1.67×** verified and 1.55× → **1.62×** trusted.  (#215's 782.62 G for "init-full through the default pipe" is not a third con-leche number: `perf stat` follows children, so it was con-leche PLUS the preprocessor it spawned.)
* **All of Mathlib no longer accepts on the RAW stream, and this row records it.**  The whole raw export (`lean4export` 3.1.0, Lean 4.29.1, 5 636 308 621 B) is read by all three cells.  Official accepts, 670 627 declarations, 10.54 T instructions, 31.3 min, 9.17 GiB.  Both con-leche cells **DECLINE (exit 2)** at fold position 50 008 of 656 667, after 4.5–4.8 min: `no install route for inductive block CategoryTheory.MorphismProperty.multiplicativeClosure`.  The block is a `Prop`-valued, recursive, three-constructor family with three indices, and its type former is declared AT A DEFINITION (`CategoryTheory.MorphismProperty C`, a `def`) that only *unfolds* to the index telescope.  Task #195 gave the direct SUM arm official's whnf reading of such a former; the FIXPOINT arm still reads `stripPis`, so the route stands down and no model is generated.  That is the known def-headed-former class — audit finding #206-A3/A5, pinned by `tests/e2e/ind_defhead_fix.ndjson` (expected 2) — and the external preprocessor was covering it: the 2026-09-06 full-Mathlib accept (1.45× verified / 1.32× trusted) was on the PREPROCESSED stream.  The two con-leche cells are therefore partial and no full-Mathlib ratio is published here.  The parse itself is healthy: 51 blocks modelled in-process, 0 declined, 65 projection functions rewritten.  Fixing it is the conformance batch's (extend #195's whnf'd-telescope reading to the fix arm).
* **The verdict line counts declaration RECORDS** (task #187).  It
  used to print `env.consts.length`, the number of environment
  CONSTANTS, which counts an inductive block's type former, its
  constructors, its recursor and its projection table separately —
  a property of con-leche's representation that moved whenever the
  representation moved.  It now prints the STREAM's record count —
  `decls.size - preludeCount + preludeDropped` since task #191's
  built-in prelude, so a stream that re-declares a prelude block
  identically reports what it declared.  `CON_LECHE_VERBOSE=1` still
  prints the constant count, on stderr, beside it.
* **The official number is not a record count either.**  Its
  `Main.lean` prints `constMap.size`: one entry per exported
  constant, so an inductive record contributes its type formers, its
  constructors AND its recursors, less the three `Quot.mk`/`.lift`/
  `.ind` entries it erases before replay.  Both numbers are now
  functions of the input file alone, and the census table above
  reproduces each of them exactly from the bytes.
* **Same bytes, same job — but not the same work.**  Both sides read
  the same raw file and install every inductive block themselves
  (task #207).  con-leche installs most blocks through a direct
  route and a mutual/nested one through a `_model` family it
  GENERATES and then checks as ordinary declarations (the
  certification tax), and runs an `annotate` pass with no official
  counterpart; official has native inductive/recursor support.
* **`--trusted` under-checks install-only kinds** (axioms, inductive
  blocks, quot, the pinned-cert branches run at io grade), which
  flatters the trusted column on inductive-heavy streams.
* One run per cell on a shared machine: `instructions:u` is
  contention-independent, so a cell may overlap other work; wall time
  is not reported for that reason (the Mathlib row's minutes are
  labelled as data, above).
* Regenerate with `lake build con-leche && scripts/perf-tables.sh`;
  `--render` re-renders from `perf-data/` without measuring, and
  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream.  The
  `mathlib-full` row needs its raw stream exported by hand first.
  Raw cells (with
  wall time and load) are tracked in `perf-data/table.tsv`, the input
  census in `perf-data/census.tsv`, provenance in `perf-data/meta.txt`.

