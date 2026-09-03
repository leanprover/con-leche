# PERF.md — the setlec performance tables

Regenerated end to end by `scripts/perf-tables.sh` (renderer:
`scripts/perf-tables-render.py`).  Every number below is measured;
nothing here is carried over from an older round.

| | |
|---|---|
| commit measured | `8690a41b6a69f6d0281cd40a46dae2a0c1036d0a` |
| binary provenance | `644f03171fc5485ab3a6e131d180e2d18df109ce` — the last commit that can change `.lake/build/bin/setlec`; the commits between it and the one above touch only `scripts/` and this file |
| battery started | 2026-09-03T20:02:21+00:00 (a full run spans several hours) |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| repetitions | median of 3 per cell |
| per-run timeout | 1800 s |
| official kernel | `/home/joachim/setlec/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| preprocessor | `/home/joachim/setlec/_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models` |

## Invocation

```
lake build setlec        # the binary measured below
scripts/perf-tables.sh   # ~2-4 h; rewrites PERF.md after every stream
scripts/perf-tables.sh --render   # re-render from _tmp/perf-tables/table.tsv
```

Per timed run, verbatim from the script:

```
(ulimit -v 41943040; SETLEC_SUPERVISED=1 \
   perf stat -e instructions:u -x, -o $po \
   timeout $TIMEOUT nice -n 5 <checker> <flags> <preprocessed-stream>)
```

**Preprocessed input on both sides.**  `lean-inductive-models` is run
once per stream, off the clock; the resulting file is fed to the
official kernel *and* to setlec under `--pre`.  No setlec cell pays
the preprocessor or its process spawn, and both checkers see the same
bytes.  **All flags are passed explicitly** — no cell relies on a
mode-aware default.

## The table — instructions:u (G), ratio vs official, wall seconds

Instructions are the primary metric (contention-independent); wall is
indicative only (caveat 6).  Ratios are against the official column
on the same row and are cross-pipeline — read them through caveat 2.

| stream | official v4.33.0 | `--set-model` `--core=production` | `--set-model` `--core=cached-parsed` | `--tt-model` `--core=production` | `--tt-model` `--core=cached-parsed` | `--no-model` `--core=production` | `--no-model` `--core=cached-parsed` |
|---|---|---|---|---|---|---|---|
| `let-ladder` | 6.15 G / 0.56 s | 22.53 G (3.66×) / 5.06 s | 10.83 G (1.76×) / 1.00 s | **exit 3** | **exit 3** | 22.75 G (3.70×) / 5.00 s | 10.83 G (1.76×) / 1.00 s |
| `beta-ladder` | 10.15 G / 1.25 s | 78.48 G (7.73×) / 15.49 s | 47.16 G (4.65×) / 4.37 s | **exit 3** | **exit 3** | 78.28 G (7.71×) / 16.83 s | 44.68 G (4.40×) / 4.26 s |
| `init-prelude` | 3.91 G / 0.35 s | 31.61 G (8.08×) / 3.38 s | 26.17 G (6.69×) / 2.71 s | **exit 3** | **exit 3** | 14.66 G (3.75×) / 1.57 s | 25.76 G (6.58×) / 2.62 s |
| `grind-ring-5` | 15.72 G / 1.64 s | 111.76 G (7.11×) / 13.50 s | 93.32 G (5.94×) / 10.76 s | **exit 3** | **exit 3** | 65.39 G (4.16×) / 8.28 s | 92.38 G (5.87×) / 10.81 s |
| `app-lam` | 29.45 G / 3.76 s | 381.56 G (12.96×) / 84.13 s | 300.98 G (10.22×) / 29.40 s | **exit 3** | **exit 3** | 385.28 G (13.08×) / 88.73 s | 227.28 G (7.72×) / 25.77 s |
| `init-full` | 413.01 G / 51.75 s | 2968.86 G (7.19×) / 437.03 s | 2820.99 G (6.83×) / 386.79 s | **exit 3** | **exit 3** | 1685.44 G (4.08×) / 267.58 s | 2853.58 G (6.91×) / 363.47 s |

## Accepted declarations (verdict sanity)

Cells that did not exit 0 show their exit code instead.  Counts
differ between the two pipelines by construction — caveat 3.

| stream | official | SM/prod | SM/cached | TT/prod | TT/cached | NM/prod | NM/cached |
|---|---|---|---|---|---|---|---|
| `let-ladder` | 62 | 69 | 69 | exit 3 | exit 3 | 69 | 69 |
| `beta-ladder` | 50 | 56 | 56 | exit 3 | exit 3 | 56 | 56 |
| `init-prelude` | 3489 | 3653 | 3653 | exit 3 | exit 3 | 3653 | 3653 |
| `grind-ring-5` | 3775 | 3946 | 3946 | exit 3 | exit 3 | 3946 | 3946 |
| `app-lam` | 88 | 97 | 97 | exit 3 | exit 3 | 97 | 97 |
| `init-full` | 60060 | 61048 | 61048 | exit 3 | exit 3 | 61048 | 61048 |

## Derived: `--set-model` ÷ `--no-model`, same core

The certified checker over the cert-skipping lane, same binary,
same stream, same engine.  On the production core this is the
project's canonical verification-tax figure; on the cached core it
is **not** one — caveat 1.

| stream | production | cached-parsed |
|---|---|---|
| `let-ladder` | 0.99× | 1.00× |
| `beta-ladder` | 1.00× | 1.06× |
| `init-prelude` | 2.16× | 1.02× |
| `grind-ring-5` | 1.71× | 1.01× |
| `app-lam` | 0.99× | 1.32× |
| `init-full` | 1.76× | 0.99× |

## Derived: best setlec cell ÷ official, per stream

| stream | cheapest setlec configuration | ratio vs official |
|---|---|---|
| `let-ladder` | NM/cached | 1.76× |
| `beta-ladder` | NM/cached | 4.40× |
| `init-prelude` | NM/prod | 3.75× |
| `grind-ring-5` | NM/prod | 4.16× |
| `app-lam` | NM/cached | 7.72× |
| `init-full` | NM/prod | 4.08× |

## CAVEATS — read every number through these

1. **`--no-model` on `--core=cached-parsed` is NOT a parity lane.**
   There is no cert-skipping/infer-only twin under `Setlec/Cached/`;
   that cell is the *certified* cached driver (`CoreC`) running with
   `CheckMode.verified = false`, which gates exactly two checks
   (λ-codomain sort validation and annotation validation) and still
   runs the whole certification machinery.  Its distance from
   `--set-model --core=cached-parsed` is therefore **exactly those
   two gated checks and nothing else** — bounded by construction, and
   not a verification tax whatever it measures.  (It is a few percent
   on the declaration-heavy streams and materially more on `app-lam`,
   where the annotation validation bites; see the derived table
   above, and do not read that column as a certificate cost.)  This
   is caveat 5 of the task-#161 canonical table; the cached NC twin
   does not exist.  The parity lane is `--no-model --core=production`
   and only that.
2. **The preprocessor floor is removed, the modeled encoding is not.**
   Both sides read the same preprocessed bytes, so no setlec cell
   pays the preprocessor here — but every setlec cell still checks a
   *modeled* encoding of the inductive blocks (plus the `annotate`
   pass, which has no official counterpart), while official checks
   the same file with native inductive/recursor support.  Every
   official ratio is cross-pipeline, not a same-work speed ratio.
3. **Declaration counts differ from official** — the preprocessor's
   `_model` declarations.  On a preprocessed stream the gap is small
   (init-full: official 60 060 vs setlec 61 048) but it is never
   zero, and the two checkers are not checking the same list.
4. **`--tt-model` is retired** (task #148 T7b): `Main.lean` rejects the
   flag outright, so those two columns are argument-parse failures,
   not measurements.  The certified mode is `--set-model`.  The
   columns are kept, and measured, so the table records the real exit
   code instead of quietly dropping the requested combination.
5. **`--core=cached` vs `--core=cached-parsed`.**  The cached column
   is `cached-parsed`, the supported and verified cached core (task
   #163; acceptance covered by `no_proof_of_Empty_SPC_*`).
   `--core=cached` also parses, but selects `checkDeclsSharedC`, an
   explicitly unverified pilot measurement instrument — measuring it
   here would put a non-shipping lane in the headline table.
6. **Medians of 3, one machine, concurrent load.**  All cells ran on
   the single machine named above, one timed run at a time (the
   script blocks until no other checker/`perf` process is live), but
   the machine is shared with concurrent agent builds.  Instructions:u
   is robust to that; **wall seconds are not** and should be read as
   indicative only.  The per-cell load average at launch is recorded
   in the raw TSV.
7. **`--no-model --core=production` under-checks install-only kinds**
   relative to official (axioms, inductive blocks, quot and the
   pinned-cert branches run at io grade there, where official's
   declaration-type check is `check`).  This flatters the parity
   column on inductive-heavy streams — init-full most of all.
8. **Fuel.**  setlec compiles in `checkFuel = 100000` plus
   `defeqLoopFuel`; official has no fuel.  No row above exhausts it.

## Raw data

`_tmp/perf-tables/table.tsv` — one line per cell:
`stream, config, median instructions:u, median wall s, exit code,
accepted declarations, 1-min load average at launch, verdict text`.
The preprocessed streams are cached at `_tmp/perf-tables/pre/`.

