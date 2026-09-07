# PERF.md — the con-leche performance battery

| | |
|---|---|
| commit measured | `96344cd145c54d4bc4674ba854dfc3d94a6ce14c` |
| tree | task #207 + task #210 Part B: RAW streams on both sides (the lean-inductive-models preprocessor is gone, so both checkers read the same raw lean4export bytes and do the same job), measured on the merged tree — every inductive block installs through the ONE fixpoint route. No cell here is comparable with any earlier PERF.md. |
| date | 2026-09-07T19:09:51+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 22 GB, 8 h, `CON_LECHE_PROGRESS=5000`) |
| streams | RAW `lean4export` NDJSON; both checkers read the same bytes and do the same job (task #207: there is no preprocessing step, so these numbers are not comparable with any earlier PERF.md) |
| Mathlib stream | `<checkout>/_tmp/mathlib-scoping/mathlib-full.ndjson` (5636308621 bytes, raw) |
| official kernel | `<checkout>/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| con-leche binary | md5 `e5c5c0540d27fda0635982ef15e5c7ec` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.14 G | 8.31 G | 8.31 G | 1.35× | 1.35× |
| `beta-ladder` | 10.13 G | 39.43 G | 39.44 G | 3.89× | 3.89× |
| `init-prelude` | 2.21 G | 4.61 G | 4.75 G | 2.09× | 2.15× |
| `grind-ring-5` | 13.40 G | 26.97 G | 27.79 G | 2.01× | 2.07× |
| `app-lam` | 29.41 G | 158.02 G | 158.03 G | 5.37× | 5.37× |
| `init-full` | 403.64 G | 659.46 G | 678.46 G | 1.63× | 1.68× |
| `mathlib-full` | 10.53 T | 13.15 T | 14.14 T | 1.25× | 1.34× |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2056 | 0 / 1803 | 0 / 1803 |
| `grind-ring-5` | 0 / 2429 | 0 / 2211 | 0 / 2211 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 54472 | 0 / 53118 | 0 / 53118 |
| `mathlib-full` | 0 / 670627 | 0 / 656667 | 0 / 656667 |

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
census cannot see them.  On `init-prelude`, `grind-ring-5` and
`init-full` the gap is exactly 30 — `Lean.Syntax`'s generated
family; on `mathlib-full` it is 2 168, for the 51 blocks modelled
in-process there.  (`CON_LECHE_INMODEL_DUMP`'s output censuses to
the verdict number exactly.)  Before #207 the models arrived IN the file,
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
| wall | 31.6 min | 38.0 min | 42.6 min |
| peak RSS (`time -v`) | 9.17 GiB | 12.56 GiB | 12.57 GiB |

## Notes

* **Nothing here is comparable with the previous table.**  Every published cell before this one was measured on a PREPROCESSED stream, with `con-leche --pre` on one side and the same preprocessed bytes on official's.  Task #207 dropped the preprocessor and task #210 Part B put every inductive block on the one fixpoint route, so both checkers now read the RAW `lean4export` export and do the same job. The like-for-like control, `init-full` `--verified`: **668.05 G** on the preprocessed stream (previous table) -> **673.17 G** raw at the drop -> **678.46 G** here, i.e. **+0.8 %** for installing the blocks ourselves and **+0.8 %** again for Part B; official goes 413.02 G -> 403.64 G (**-2.3 %**), the raw stream carrying no model families.  So the init-full ratio WORSENS, 1.62x -> **1.68x** verified and 1.55x -> **1.63x** trusted.  (#215's 782.62 G "through the default pipe" was never a third con-leche number: `perf stat` follows children, so it was con-leche PLUS the preprocessor it spawned.)
* **All of Mathlib, all three checkers, one RAW stream — and the ratio improves.** The `mathlib-full` row is the whole raw export (`lean4export` 3.1.0, Lean 4.29.1, 5 636 308 621 B), read by all three cells with no preprocessing step anywhere. **Every cell accepts**: official 670 627 declarations, con-leche 656 667 declaration records in BOTH modes -> **1.34x verified, 1.25x trusted**, against 1.45x/1.32x on the previous table's PREPROCESSED stream, and better than `init-full`'s 1.68x/1.63x: the corpus does not punish the checker at scale, and it punishes it less now than it did through the tool.  Wall 31.6 / 38.0 / 42.6 min, peak RSS 9.17 / 12.56 / 12.57 GiB; the con-leche cells ran under `CON_LECHE_PROGRESS=5000` (measured cost on init-full -0.0006 %).  NB the earlier milestone "all of Mathlib accepted, 2026-09-06" was measured on the PREPROCESSED stream; this is the first RAW one.  It was briefly FALSE in between: on task #207's drop alone both con-leche cells declined at fold position 50 008 on `CategoryTheory.MorphismProperty.multiplicativeClosure`, a block whose type former is declared at a `def` that only unfolds to its index telescope (#206-A3/A5) and which the external preprocessor had been covering; task #210 Part B's former-sort completion closed it.  See DESIGN task #207.
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

