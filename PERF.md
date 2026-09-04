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

> **⚠ SUPERSEDED COLUMN — `--no-model --core=cached-parsed`.**
> The binary measured above **predates the cached parity lane**
> (`Setlec/Cached/CoreNC.lean`, landed on master at `1fa6444f`).
> In this table that cell is **not a parity lane**: it is the
> *certified* cached engine with two mode-gated checks off, all
> internal certification still running, while `--no-model
> --core=production` beside it **is** one (`CoreNC`, certs
> stripped).  Every comparison between those two columns here
> puts a still-certifying engine against a cert-free one — the
> caveat-5 confound, whose full consequence is worked out in
> DESIGN.md, "The cached parity lane and the confound
> correction".  Read the column as *the certified cached engine
> minus two checks*, which is what it measured; do not read it as
> the cached core's speed.  In particular the oddity below —
> `NM/cached` the **most expensive** cell on `init-full` — is
> that confound, not a property of the cached core.
>
> A real cert-free cached engine now exists and `--no-model
> --core=cached-parsed` dispatches to it, so **these cells are
> historical**.  The perf lead's reference medians for the new
> engine, pending regeneration: init-prelude 15.99 G,
> grind-ring-5 55.2, app-lam 228.0, beta-ladder 45.2, let-ladder
> 11.4, **init-full 1432.9 (3.55× official)** — head to head the
> cached parity lane ties or beats the interned one on every
> row.  **Those figures are on the RAW pipeline with the
> preprocessor included and are quoted against official-RAW;
> this file's cells are preprocessed-both-sides against
> official-PRE.  The two bases are not interchangeable** — mixing
> them is exactly the mixed-baseline error the DESIGN entry
> records — so do not compute a ratio across the boundary.  They
> are quoted here only to say which way the column will move.
>
> Regeneration is deferred until the #171 direct-to-ExprC parse
> lands, since that moves the cached-lane numbers again and a
> full battery costs hours.  When it is in, one command
> (below) rewrites this file and this note disappears on its
> own.

> **PENDING RULING — the `--core=production` columns.**  The user
> has ruled the interned representation **dropped entirely**
> ("one expr type with computed fields everywhere", task #172,
> the tri-core refactor).  When it lands, this matrix halves to
> the cached columns plus official; the interned cells below are
> not deleted but carried into a retired-configurations section
> with their provenance.  Until the tri-core template batches
> land, core names and dispatch are still moving and these
> columns remain live.

## Regenerating this file

One line, from the repository root:

```
lake build setlec && scripts/perf-tables.sh
```

It takes 2-4 h (the `init-full` leg alone is over an hour, plus
however long it waits for the machine to go idle), rewrites PERF.md
after every stream, and needs no target beyond `setlec`.  Useful
variants:

```
scripts/perf-tables.sh --render                  # re-render from the saved TSV, no measuring
PERF_APPEND=1 PERF_STREAMS=init-full scripts/perf-tables.sh   # resume one interrupted leg
PERF_REPS=1 PERF_STREAMS=let-ladder scripts/perf-tables.sh    # smoke test (~30 s)
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

| stream | official v4.33.0 | `--set-model` `--core=production` | `--set-model` `--core=cached-parsed` | `--tt-model` `--core=production` | `--tt-model` `--core=cached-parsed` | `--no-model` `--core=production` | `--no-model` `--core=cached-parsed` ⚠ **not a parity lane** |
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

| stream | official | SM/prod | SM/cached | TT/prod | TT/cached | NM/prod | NM/cached ⚠ |
|---|---|---|---|---|---|---|---|
| `let-ladder` | 62 | 69 | 69 | exit 3 | exit 3 | 69 | 69 |
| `beta-ladder` | 50 | 56 | 56 | exit 3 | exit 3 | 56 | 56 |
| `init-prelude` | 3489 | 3653 | 3653 | exit 3 | exit 3 | 3653 | 3653 |
| `grind-ring-5` | 3775 | 3946 | 3946 | exit 3 | exit 3 | 3946 | 3946 |
| `app-lam` | 88 | 97 | 97 | exit 3 | exit 3 | 97 | 97 |
| `init-full` | 60060 | 61048 | 61048 | exit 3 | exit 3 | 61048 | 61048 |

## Derived: `--set-model` ÷ `--no-model`, same core

The certified checker over the cert-skipping lane, same
binary, same stream, same engine.  On the production core
this is the project's canonical verification-tax figure; on
the cached core it is **not** one and never was — it is the
two mode-gated checks alone (caveat 1 and the header note).

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
| `let-ladder` | NM/cached ⚠ | 1.76× |
| `beta-ladder` | NM/cached ⚠ | 4.40× |
| `init-prelude` | NM/prod | 3.75× |
| `grind-ring-5` | NM/prod | 4.16× |
| `app-lam` | NM/cached ⚠ | 7.72× |
| `init-full` | NM/prod | 4.08× |

## CAVEATS — read every number through these

1. **`--no-model` on `--core=cached-parsed` is NOT a parity lane**
   — see the superseded-column note in the header, which is the
   short version of this caveat and takes precedence.  There was
   no cert-skipping twin under `Setlec/Cached/` when this binary
   was built; that cell is the *certified* cached driver
   (`CoreC`) running with `CheckMode.verified = false`, which
   gates exactly two checks (λ-codomain sort validation and
   annotation validation) and still runs the whole certification
   machinery.  Its distance from `--set-model
   --core=cached-parsed` is therefore **exactly those two gated
   checks and nothing else** — bounded by construction, and not a
   verification tax whatever it measures.  (It is a few percent
   on the declaration-heavy streams and materially more on
   `app-lam`, where the annotation validation bites; see the
   derived table above, and do not read that column as a
   certificate cost.)  This is caveat 5 of the task-#161
   canonical table, whose full consequence — that the
   `--no-model` cross-core comparison was confounded — was
   worked out only after this run.  In this table the parity
   lane is `--no-model --core=production` and only that.
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
7. **`--no-model` under-checks install-only kinds** relative to
   official (axioms, inductive blocks, quot and the pinned-cert
   branches run at io grade there, where official's declaration-type
   check is `check`).  This flatters every parity column on
   inductive-heavy streams — init-full most of all.
8. **Fuel.**  setlec compiles in `checkFuel = 100000` plus
   `defeqLoopFuel`; official has no fuel.  No row above exhausts it.

## Raw data

Tracked in `perf-data/`: `table.tsv` (the cells behind the live
tables), `meta.txt` (the run's provenance), and `retired.tsv` /
`retired.meta` when a configuration has been ruled out of the
matrix.  One line per cell: `stream, config, median instructions:u,
median wall s, exit code, accepted declarations, 1-min load average
at launch, verdict text`.

The working copy of a run lives at `_tmp/perf-tables/` (gitignored,
so it is a cache and not the record) and the preprocessed streams
are cached beside it at `_tmp/perf-tables/pre/`.

