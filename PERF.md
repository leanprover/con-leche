# PERF.md — the setlec performance tables

Regenerated end to end by `scripts/perf-tables.sh` (renderer:
`scripts/perf-tables-render.py`).  Every number below is measured;
nothing here is carried over from an older round.

| | |
|---|---|
| commit measured | `8690a41b6a69f6d0281cd40a46dae2a0c1036d0a` |
| binary provenance | `644f03171fc5485ab3a6e131d180e2d18df109ce` — the last commit that can change `.lake/build/bin/setlec`; the commits between it and the one above touch only `scripts/` and this file |
| battery started | 2026-09-03T20:02:21+00:00 |
| machine | bubblewrap — AMD EPYC 9455 48-Core Processor, 96 cores, 125 GB RAM, Linux 6.12.100 |
| runs per cell | median of 3 per cell |
| per-run timeout | 1800 s |
| official kernel | `/home/joachim/setlec/_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel` |
| preprocessor | `/home/joachim/setlec/_tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models` |

## Regenerating this file

One line, from the repository root:

```
lake build setlec && scripts/perf-tables.sh
```

Useful variants:

```
scripts/perf-tables.sh --render                  # re-render from the saved cells
PERF_STREAMS=init-full PERF_APPEND=1 scripts/perf-tables.sh   # re-run one stream
PERF_CONFIGS=nm-cached PERF_APPEND=1 scripts/perf-tables.sh   # confirm one suspect cell
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
mode-aware default.  One timed cell runs at a time, and each waits
for the machine to go idle first.

## The table — instructions:u in G, ratio vs official

| stream | official v4.33.0 | `--set-model` `--core=production` | `--set-model` `--core=cached-parsed` | `--no-model` `--core=production` |
|---|---|---|---|---|
| `let-ladder` | 6.15 G | 22.53 G (3.66×) | 10.83 G (1.76×) | 22.75 G (3.70×) |
| `beta-ladder` | 10.15 G | 78.48 G (7.73×) | 47.16 G (4.65×) | 78.28 G (7.71×) |
| `init-prelude` | 3.91 G | 31.61 G (8.08×) | 26.17 G (6.69×) | 14.66 G (3.75×) |
| `grind-ring-5` | 15.72 G | 111.76 G (7.11×) | 93.32 G (5.94×) | 65.39 G (4.16×) |
| `app-lam` | 29.45 G | 381.56 G (12.96×) | 300.98 G (10.22×) | 385.28 G (13.08×) |
| `init-full` | 413.01 G | 2968.86 G (7.19×) | 2820.99 G (6.83×) | 1685.44 G (4.08×) |

Ratios are against the official column on the same row.  They are
cross-pipeline, not same-work speed ratios — caveat 1.

## Accepted declarations (verdict sanity)

| stream | official | SM/prod | SM/cached | NM/prod |
|---|---|---|---|---|
| `let-ladder` | 62 | 69 | 69 | 69 |
| `beta-ladder` | 50 | 56 | 56 | 56 |
| `init-prelude` | 3489 | 3653 | 3653 | 3653 |
| `grind-ring-5` | 3775 | 3946 | 3946 | 3946 |
| `app-lam` | 88 | 97 | 97 | 97 |
| `init-full` | 60060 | 61048 | 61048 | 61048 |

## Derived: the verification tax

The certified checker over the cert-free lane — same binary, same
stream, same engine.

| stream | production |
|---|---|
| `let-ladder` | 0.99× |
| `beta-ladder` | 1.00× |
| `init-prelude` | 2.16× |
| `grind-ring-5` | 1.71× |
| `app-lam` | 0.99× |
| `init-full` | 1.76× |

## Superseded cells

Configurations that have left the matrix — a retired flag, a lane
whose meaning changed, an earlier representation — are not shown
above; their cells keep full provenance (the binary that measured
them) in `perf-data/retired.tsv`.  Currently held there: `tt-prod`, `tt-cached`, `nm-cached`.

## CAVEATS

1. **Cross-pipeline, not same-work.**  Both sides read the same
   preprocessed bytes, so no setlec cell pays the preprocessor — but
   every setlec cell checks a *modeled* encoding of the inductive
   blocks, plus an `annotate` pass with no official counterpart,
   while official checks that file with native inductive/recursor
   support.  Every official ratio carries that difference.
2. **Declaration counts differ from official** — the preprocessor's
   `_model` declarations.  On a preprocessed stream the gap is small
   but never zero, and the two checkers are not checking the same
   list.
3. **`--no-model` under-checks install-only kinds** relative to
   official (axioms, inductive blocks, quot and the pinned-cert
   branches run at io grade there, where official's declaration-type
   check is `check`).  This flatters the cert-free columns on
   inductive-heavy streams — init-full most of all.
4. **Median of 3 per cell, one machine.**  Instructions:u is
   robust to the concurrent load this shared machine sees.
5. **Fuel.**  setlec compiles in `checkFuel = 100000` plus
   `defeqLoopFuel`; official has no fuel.  No row above exhausts it.
6. **`--core=cached-parsed`, not `--core=cached`.**  The latter
   parses but selects `checkDeclsSharedC`, an explicitly
   unverified pilot instrument; the cached column is the
   supported, verified core (task #163).

## Raw data

Tracked in `perf-data/`: `table.tsv` (the cells behind the tables),
`meta.txt` (the run's provenance), and `retired.tsv` / `retired.meta`
(superseded cells, stamped with the binary that measured them).  One
line per cell: `stream, config, instructions:u, wall s, exit code,
accepted declarations, 1-min load average at launch, verdict text` —
wall and load are recorded but not printed.

The working copy of a run lives at `_tmp/perf-tables/` (gitignored,
so it is a cache and not the record); preprocessed streams are cached
beside it at `_tmp/perf-tables/pre/`.

