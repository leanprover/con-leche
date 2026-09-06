# PERF.md — the lech performance battery

| | |
|---|---|
| commit measured | `bd4dcf6ab1397557dc1f2e7b38c2ab0cee96d789` **(dirty working tree)** |
| tree | task #187 regeneration on agent/perf-regen off master bd4dcf6a; the verdict line now counts accepted DECLARATION RECORDS (parsed DeclC), not environment constants |
| date | 2026-09-06T19:31:40+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| columns | official v4.33.0 · trusted `--trusted` · verified `--verified` |
| metric | `perf stat -e instructions:u`, one run per cell, `ulimit -v 16000000`, `timeout 3000`, `nice -n 5` (the `mathlib-full` row: 22 GB, 8 h, `LECH_PROGRESS=5000`) |
| streams | preprocessed once off the clock by `lech-preprocess`; both checkers read the same bytes, lech under `--pre` |
| concurrent load | the full-Mathlib preprocessor cell ran on the machine alongside the six small streams; instructions:u is contention-independent |
| official kernel | `/home/joachim/setlec/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| preprocessor | `/home/joachim/setlec/.claude/worktrees/perf-regen/.lake/build/bin/lech-preprocess` |

## instructions:u

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` | trusted ÷ official | verified ÷ official |
|---|---|---|---|---|---|
| `let-ladder` | 6.13 G | 8.37 G | 8.37 G | 1.36× | 1.36× |
| `beta-ladder` | 10.13 G | 40.91 G | 40.92 G | 4.04× | 4.04× |
| `init-prelude` | 3.18 G | 5.60 G | 7.21 G | 1.76× | 2.27× |
| `grind-ring-5` | 14.49 G | 26.46 G | 28.52 G | 1.83× | 1.97× |
| `app-lam` | 29.41 G | 161.60 G | 161.61 G | 5.49× | 5.50× |
| `init-full` | 406.52 G | 641.60 G | 666.09 G | 1.58× | 1.64× |

## exit code / accepted declaration records

| stream | official v4.33.0 | trusted `--trusted` | verified `--verified` |
|---|---|---|---|
| `let-ladder` | 0 / 22 | 0 / 13 | 0 / 13 |
| `beta-ladder` | 0 / 20 | 0 / 11 | 0 / 11 |
| `init-prelude` | 0 / 2509 | 0 / 2151 | 0 / 2151 |
| `grind-ring-5` | 0 / 2927 | 0 / 2607 | 0 / 2607 |
| `app-lam` | 0 / 34 | 0 / 21 | 0 / 21 |
| `init-full` | 0 / 55346 | 0 / 53890 | 0 / 53890 |

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

## Notes

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

