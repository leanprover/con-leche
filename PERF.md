# PERF.md — the con-leche performance battery

| | |
|---|---|
| commit measured | `c505b16f5a6ec62e45a78b756e33fb2a7a13997d` |
| tree | task #207: the first table on RAW streams — the lean-inductive-models preprocessor was dropped, so both checkers now read the same raw lean4export bytes and do the same job (con-leche installs every inductive block itself). No cell here is comparable with an earlier PERF.md. |
| date | 2026-09-07T17:58:34+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 22 GB, 8 h, `CON_LECHE_PROGRESS=5000`) |
| streams | RAW `lean4export` NDJSON; both checkers read the same bytes and do the same job (task #207: there is no preprocessing step, so these numbers are not comparable with any earlier PERF.md) |
| Mathlib stream | `/home/joachim/setlec/.claude/worktrees/tooldrop/_tmp/mathlib-scoping/mathlib-full.ndjson` (5636308621 bytes, raw) |
| official kernel | `/home/joachim/setlec/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| con-leche binary | md5 `eb5d21fd04049cadae6074f5302a490d` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.13 G | 8.31 G | 8.31 G | 1.35× | 1.35× |
| `beta-ladder` | 10.12 G | 39.43 G | 39.43 G | 3.89× | 3.89× |
| `init-prelude` | 2.21 G | 4.41 G | 4.55 G | 2.00× | 2.06× |
| `grind-ring-5` | 13.41 G | 25.28 G | 26.10 G | 1.88× | 1.95× |
| `app-lam` | 29.41 G | 158.01 G | 158.01 G | 5.37× | 5.37× |
| `init-full` | 403.62 G | 654.08 G | 673.20 G | 1.62× | 1.67× |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2056 | 0 / 1803 | 0 / 1803 |
| `grind-ring-5` | 0 / 2429 | 0 / 2211 | 0 / 2211 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 54472 | 0 / 53118 | 0 / 53118 |

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

| stream | records | con-leche | official | pinned | modeled | native | structures | sums | indexed |
|---|---|---|---|---|---|---|---|---|---|
| `let-ladder` | 13 | 13 | 19 | 2 | 0 | 2 | 2 | 0 | 0 |
| `beta-ladder` | 11 | 11 | 17 | 3 | 0 | 1 | 1 | 0 | 0 |
| `init-prelude` | 1777 | 1773 | 2056 | 5 | 0 | 121 | 104 | 14 | 3 |
| `grind-ring-5` | 2185 | 2181 | 2429 | 4 | 0 | 101 | 78 | 16 | 7 |
| `app-lam` | 21 | 21 | 31 | 2 | 0 | 4 | 4 | 0 | 0 |
| `init-full` | 53093 | 53088 | 54472 | 5 | 0 | 583 | 477 | 59 | 47 |

## Notes

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

