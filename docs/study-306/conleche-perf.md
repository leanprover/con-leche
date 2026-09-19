# Where con-leche's time goes today

Research leg of task #306 (the "faster core" design study).  Read-only: nothing was built, nothing
was run.  Every number below is quoted from a tracked artefact in the worktree (`PERF.md`,
`perf-data/*.tsv`, `DESIGN.md` records) and every claim about the algorithm is read out of the
source, with `file:line`.  Where the measurement is stale or absent, it says so.

Worktree: `<worktree>`, branch `agent/fastcore-306`.

---

## A. The measurement method the project uses

The discipline is fixed and written down in the battery script itself,
`scripts/perf-tables.sh:9-32`:

* **`perf stat -e instructions:u` is the metric**, ONE run per cell — "instructions are the only
  metric reported (contention-independent)" (`scripts/perf-tables.sh:11-12`).  The one-run rule is
  justified at `scripts/perf-tables.sh:53-59`: a medians-of-3 round measured the spread at
  0.01–0.5 %, so the third significant figure is stable off a single run.
* **Every run under `ulimit -v 16000000` (16 GB), `nice -n 5` and a `timeout`**
  (`scripts/perf-tables.sh:13-17`, `:60-63`); the `mathlib-full` row gets 22 GB and 8 h
  (`PERF.md:10`, `scripts/perf-tables.sh:99`).
* **Both checkers ingest the same RAW `lean4export` bytes** since task #207 — no preprocessing
  step on either side (`scripts/perf-tables.sh:18-28`).  This is why cells are *not* comparable
  with any PERF.md older than that regeneration.
* **All flags explicit**, and the con-leche cells all pass `--jobs=1`, the single-worker lane, as
  the apples-to-apples comparison against a single-threaded official kernel (`PERF.md:11`,
  `PERF.md:134-139`).
* **Shared machine.**  The box is a 96-core EPYC shared with other agents (`PERF.md:8`,
  `perf-data/meta.txt:6-9`); per-cell load average is recorded (`perf-data/table.tsv` column 7 —
  1.89 … 4.67 at the last regeneration).  Wall time is published as *data*, never as a measurement
  (`PERF.md:74-79`).  `CLAUDE.md` restates the rule: "Wall time is not a measurement here (shared
  machine); use `perf stat -e instructions:u`."
* For profiling, the project uses `perf record -F 99…999 -e instructions:u` with symbol buckets,
  plus a **gdb-sampling recipe** where perf's call graph fails (tail calls, no frame pointers, the
  127-frame `perf_event_max_stack` cap) — `DESIGN.md:51861-51866`, `DESIGN.md:62920-62926`.
* A recorded measurement hazard worth carrying into any new round: `perf report` resolves symbols
  against the binary *at the recorded path*, so a rebuild silently redistributes samples —
  snapshot the binary before recording (`DESIGN.md:48298-48306`).

**Perf-related scripts in the tree** (everything else under `scripts/` is a fixture generator or a
census tool — `scripts/README.md:1-9`):

| script | what it measures |
|---|---|
| `scripts/perf-tables.sh` | the whole battery: 7 streams × 3 configs, `instructions:u`, writes `perf-data/` and renders `PERF.md` |
| `scripts/perf-tables-render.py` | pure formatting: re-renders `PERF.md` from `perf-data/{table,census,parallel,meta}` without measuring |
| `scripts/stream-census.py` | properties of the *input file* (records, pinned/native inductive blocks, shapes) — `PERF.md:46-54` |
| `tests/scale.sh` + `tests/scale/gen.py` | asymptotic growth harness: per-shape doubling, `instructions:u` median-of-3, fits a growth exponent, gates it (`tests/scale.sh:1-35`) |
| `tests/scale/compare.sh` | the same growth shapes across three checkers |
| `tests/arena.sh` | the correctness battery (verdicts), not a perf harness |

`perf-data/` holds **only whole-run cells**: `table.tsv` (21 rows — stream, config, instructions,
wall, exit, accepted, load, verdict line, peak-RSS-KB for the Mathlib rows), `census.tsv` (input
shape), `parallel.tsv` (6 worker-count wall cells), `meta.txt` (provenance). **There is no
per-function or per-phase profile tracked in the repository.**  Profiles live in DESIGN records
and in `_tmp/` scratch directories that are gitignored.

---

## B. The latest whole-run numbers

Source: `PERF.md`, regenerated at commit `1d470aa7` on 2026-09-10 (task #276,
`DESIGN.md:68006-68105`).  Binary md5 `625a61babe10de48dde3ced724ad0f13` (`PERF.md:16`).  Official
column is the arena's `official-v4.33.0` kernel (`PERF.md:15`).

`instructions:u`, `--jobs=1` (`PERF.md:20-28`):

| stream | official | trusted | verified | trusted ÷ off | verified ÷ off |
|---|---|---|---|---|---|
| `let-ladder` | 6.13 G | 8.06 G | 8.06 G | 1.31× | 1.31× |
| `beta-ladder` | 10.12 G | 39.94 G | 39.95 G | **3.95×** | **3.95×** |
| `init-prelude` | 2.21 G | 3.04 G | 3.20 G | 1.38× | 1.45× |
| `grind-ring-5` | 13.41 G | 21.54 G | 22.69 G | 1.61× | 1.69× |
| `app-lam` | 29.41 G | 157.30 G | 157.31 G | **5.35×** | **5.35×** |
| `init-full` | 403.44 G | 521.13 G | 538.46 G | 1.29× | 1.33× |
| `mathlib-full` | 10.54 T | 11.16 T | 12.01 T | **1.06×** | **1.14×** |

Raw cells with wall time and load: `perf-data/table.tsv:1-21`.

**Suites named in the brief that do not exist as battery streams.** There is no `cslib` and no
`std` row, and no self-check ("con-leche checking con-leche") row.  The battery's streams are the
arena's `perf/*` fixtures plus `init-prelude`, `init-full` and `mathlib-full`
(`scripts/perf-tables.sh:66-79`).  A self-check harness exists (`scripts/selfcheck.sh`) but
contributes no tracked perf cell.

**Mathlib as data, not measurement** (`PERF.md:81-84`): wall 30.7 min official / 17.5 min trusted
/ 19.0 min verified; peak RSS 9.16 GiB official against 7.87 GiB in both con-leche modes —
con-leche is *below* official on memory.

**Sequential vs pool** (`PERF.md:86-103`, `perf-data/parallel.tsv`):

| stream | `--jobs=1` | `--jobs=4` | `--jobs=8` |
|---|---|---|---|
| `init-full` | 50.2 s | 16.8 s | 11.2 s |
| `mathlib-full` | 1143.6 s | 444.7 s | 326.4 s |

The instruction count moves **0.2 % across the three worker counts** (12.014 / 12.038 / 12.039 T —
`DESIGN.md:68069-68075`), so the pool divides work rather than adding it.

**Verified − trusted is the certificate bill**, and it is small at scale: +3.3 % on `init-full`,
+7.7 % on `mathlib-full`, and **0.00 % on `app-lam` and `beta-ladder`** (157.303 vs 157.307 G;
39.941 vs 39.946 G — `perf-data/table.tsv:13-15`, `:4-6`).  That last fact is load-bearing for
this study and is picked up in §D.

---

## C. The best available breakdown

### C.1 By phase — exists, at Mathlib scale only

`PERF.md:103` and `DESIGN.md:68069-68075` give the only tracked phase split.  On `mathlib-full`,
`--verified`:

| phase | wall | share of the `--jobs=1` run |
|---|---|---|
| parse | 26 s | 2.3 % |
| install (phase A: annotate + install-only checks + inductive installation) | 150 s | 13.1 % |
| check (phase B) | 962 s | 84.1 % |

At `--jobs=8` the check phase is 142.3 s and the sequential prefix is 56 % of the run — "the floor
no worker count goes below" (`PERF.md:103`). On `init-full` the check phase is 45.3 / 11.9 / 6.3 s
at 1 / 4 / 8 workers (`DESIGN.md:68072-68074`).

These are **wall times, not instruction counts.**  No tracked artefact splits instructions by
phase.

### C.2 By function — the record exists but it is in DESIGN, not tracked

There are four per-function profiles of record.  None is current against `1d470aa7`; each is
dated, and each measured a different tree.

**(i) The whole-run bucket attribution (task #161 follow-up 2, 2026-09-03,
`DESIGN.md:27004-27012`).**  `perf record`, symbol-bucketed, `--no-model` cached core (the
ancestor of today's `Cached/*` tier):

> ExprC walks + per-walk memo-HashMaps 31/33/49/49 % (init-prelude /
> grind-ring-5 / beta-ladder / app-lam), allocator 21–25 %, RC 16–22 %,
> preprocessor 15/9/2/0.5 %, parser 4.7/3.0/0.3/0.2 %, knot 3.8/4.1/
> 0.05/0.04 %.
> **"Allocation/RC churn plus per-walk hash-map memo traffic is 68–97 %
> of every `--no-model` run."** (`DESIGN.md:27010-27012`)

Top symbols named there: `ExprC.instantiateRevGo` / `instantiateListGo`, the `Std.DHashMap`
insert/get/expand at the walk-memo spec sites, `ExprC.beqB`.  Caveat: the preprocessor is gone
(#207) and the walk memos were re-shaped (#177), so the *shares* have moved; the *ordering* —
walks + memo + allocator + RC first, core bodies last — has never been contradicted by a later
profile.

**(ii) The substitution-walk profile (task #177, 2026-09-06, `DESIGN.md:44858-44868`).**  `perf
record -F 199/99`, three streams, both modes:

| bucket | app-lam | grind-ring-5 | init-full |
|---|---|---|---|
| `lean_dec_ref_cold` + `mi_free` + page collect + `mi_malloc` + `del_core_other` | 40.2 % | 35.1 % | 34.2 % |
| kernel page-fault / `munmap` | ~19 % | ~1 % | ~2 % |
| `instantiate*Go` / `abstractRangeGo` (self) | 6.6 % | 4.3 % | 4.5 % |
| the walks' `Std.DHashMap` spec sites | 11.2 % | 8.1 % | 6.3 % |
| `Expr.beqB`/`beqFast` (defeq descent) | 0.7 % | 5.1 % | 6.7 % |
| `Expr.bvarBoundGo`'s own memo | — | 2.4 % | 2.6 % |

**The allocator and the reference counter, together, are the single largest bucket in every
column** — larger than the walks themselves by 5–6×.

**(iii) The tail profile (task #189, 2026-09-06, `DESIGN.md:51865-51875`).**  The five slowest
declarations of a Mathlib acceptance run, `perf record -F 999` attached while on the target:

| tag | `Expr.beq*` + its memo | allocator / RC | everything else |
|---|---|---|---|
| t1 | 39.3 % | 52.0 % | **8.2 %** |
| t2 | 43.4 % | 48.7 % | **8.1 %** |
| t3 | 25.8 % | 46.0 % | 28.3 % |
| t4 | 43.5 % | 51.6 % | **5.0 %** |
| t5 | 45.7 % | 50.3 % | **4.0 %** |

and the finding that matters: **"No core symbol reaches 1 % on t1/t2/t4/t5"** — `whnfCoreBodyI`,
`defeqStepI`, `iotaRecI`, `inferBodyI` do not appear in the top 40; the highest non-`beq`,
non-allocator symbols are `ExprC.instantiateRevGo`, `abstractRangeGo` and `instantiate1Go` at
0.2–2 % (`DESIGN.md:51877-51886`).  This profile's proximate cause (a half-keyed `beq` memo) was
fixed by task #240 (`DESIGN.md:62893-63060`), which took that fixture from 236 s to 0.80 s and
left `beqGo` at 1.38 % of the run, `beqB` at 5.80 %, "and the largest single symbol is
`lean_dec_ref_cold` at 13.65 %" (`DESIGN.md:63073-63078`).

**(iv)** Task #272 (`DESIGN.md:66805-66812`) put 90.3 % of a fanout stream in
`Level.zeronessOf` — fixed; quoted as evidence that these profiles do find single-symbol
pathologies when they exist.

### C.3 Inductive installation vs whnf/defeq/infer

Not attributed at function granularity anywhere.  What is on record:

* **Installation is phase A**, and phase A is 150 s of a 1143 s `--jobs=1` Mathlib run — 13 %
  (`PERF.md:103`).  It is entirely sequential and is the floor on the parallel lane.
* The input census (`PERF.md:64-72`, `perf-data/census.tsv`) says how much installation there is:
  on `mathlib-full`, 5 pinned basis blocks and **6 639 native blocks** (5 683 structures, 634
  sums, 322 indexed), of which 51 are modelled in process producing 2 168 generated records. On
  `app-lam` and `beta-ladder` there are 4 and 1 native blocks — i.e. essentially none.
* PERF.md's own note (`PERF.md:124-130`): "Both sides read the same file and install every
  inductive block themselves… con-leche installs single blocks through its fixpoint route and a
  mutual/nested one through a `_model` family it GENERATES and then checks as ordinary
  declarations (the certification tax), and runs an `annotate` pass with no official counterpart;
  official has native inductive/recursor support."

### C.4 The certification tax — measured, but on a 2026-09-02 tree

Task #161 HARVEST P1 (`DESIGN.md:22380-22620`) is the only per-site cost inventory.  Its
structural content is still accurate (the call sites are still there — see §D.3), its percentages
are not current.  Headline:

* Of 20 internal `infer` call sites in the reduction/defeq cone, **six have no official
  counterpart at all** (the ι-spine certificates, the projection certificate's four inferences,
  and the two β-redex argument certificates — `DESIGN.md:22489-22512`).
* **"82.5 % of all application-argument certificate work in the checker is internal"** — done
  under a certificate where the official kernel would be in `inferOnly` and would do none of it
  (`DESIGN.md:22561-22564`).
* Degating all four landing sites was worth −24.4 % / −26.4 % (init-prelude prod/cached), −12.7 %
  / −16.9 % (grind-ring-5), −9.8 % / −14.7 % (init-full) against baseline
  (`DESIGN.md:22582-22588`).

The **current** number for this is the verified-minus-trusted delta in §B: 3.3 % on `init-full`,
7.7 % on `mathlib-full`, 0 % on the two β-heavy streams.  The gap between "−15 % in 2026-09-02"
and "+3.3 % in 2026-09-10" is the io grade (task #170/#172 B4), which put every internal inference
on the `inferIO` slot — `ConLeche/Kernel/Env.lean:131-133`,
`ConLeche/Cached/CoreC.lean:1968-1975`.

---

## D. Cost structure of the current core, read out of the code

### D.1 The term representation

`ConLeche/Kernel/Expr.lean:343-404` — a plain inductive `Expr` (bvar / fvar / sort / const / app /
lam / forallE / letE / lit / proj), **no arena, no hash-consing**.  One `@[computed_field] data :
Expr → UInt64` (`:357`) packs four derived quantities into one word (`:145-158`): 32-bit hash,
15-bit loose-bvar bound `bvarB`, 15-bit fvar range `fvarB`, 1-bit `hasLP`.  The two ranges
**saturate** at `satRange = 32767`; above that the accessor falls back to a memoised `O(DAG)`
walk, and the measured maxima are 213 (`init-full`), 488 (`grind-ring-5`), 4000 (`app-lam`) — the
branch is never reached (`Expr.lean:159-170`).

Consequences for cost:

* **Hashing a term for a memo is a field read**, not a traversal (`Expr.lean:314-316`); the whole
  packed word is computed once at construction, so *every node allocation pays four mixHashes and
  a packing* (`Expr.lean:358-404`).  Allocation is therefore never free here even before mimalloc:
  it is allocation + hash.
* **`bvarB ≤ d` is the substitution cut** and it is *exact*, so it cuts maximally; but exactness
  has a second consequence recorded at `DESIGN.md:44912-44922`: node-identity preservation
  ("return the original node when no child changed") **cannot fire**, because `bvarB e > d` means
  the node really does contain a loose bvar that instantiation changes.  Anything that reaches the
  rebuild rebuilds.

### D.2 What a single beta step costs

The redex path is `whnfCoreStepI` → `whnfAppI` → `betaPeelI`
(`ConLeche/Cached/CoreC.lean:950-996`, `:867-898`, `:907-940`).

1. `whnfCoreStepI` (`:955-963`) takes the spine apart with `Expr.getAppFn` + `getAppArgsC` (a
   fresh `List Expr`), whnfCores the head through the knot, then runs `whnfAppI` over the whole
   argument list.
2. At a `.lam` head, **unless `mode.betaSkip mb.pw` fires**, the certificate runs: `instListM ty
   acc` (substitute the *domain*), then `r.inferIO depth a`, then `r.defeq depth ta ty'`
   (`CoreC.lean:918-924`).  This is the β-certificate; official does none of it
   (`DESIGN.md:22509-22510`, rows 19–20).
3. Binders are **batched**: `betaPeelI` accumulates arguments and substitutes the body **once**,
   at the end, with `instListM t acc` (`CoreC.lean:911-913`).  So an `n`-ary redex is one bulk
   substitution, not `n` nested ones.
4. `instListM` (`ConLeche/Cached/StateC.lean:188-199`) is memoised **persistently across the
   declaration** on the key `(Expr × List Expr × Nat)` — a `Prod`-of-`Prod` allocated per probe,
   plus hashing a whole `List Expr` structurally.  Cap 32 M entries (`StateC.lean:162`); at the
   cap the table is dropped wholesale.
5. The substitution itself, `Expr.instantiateListGoC` (`ConLeche/Cached/ExprOpsC.lean:281-347`),
   is a **memoised DAG rebuild**: cut at `bvarB ≤ d`; atoms answered in place; every compound node
   probes a `Std.HashMap (Expr × Nat) Expr` (one `Prod` per node) and, on a miss, **allocates a
   new node**.

So: **a beta step is one DAG-sized rebuild of the body, bounded by the loose-bvar cut, plus one
hash-map probe and one `Prod` allocation per rebuilt compound node, plus a full `inferIO` +
`defeq` of the argument in verified mode.**  The memo tables are per-call for `instantiate1C`
(`ExprOpsC.lean:262` — `instantiate1GoC v {} e d`, a **fresh table every call**) and
per-declaration for the bulk form.

`instantiate1LiftC` (`ExprOpsC.lean:255-259`) shows the shape the project settled on for the small
case: a **budgeted, allocation-free plain descent** (`instantiate1LiftBC`, 4096 nodes) with the
memoised descent only past the budget.  `instantiate1C` (`:262`) has no such budget — it goes
straight to the memoised walk.

`instListRevM` (`StateC.lean:202-205`) is **deliberately not memoised** — that is the
telescope-opening substitution used by `inferLamsLeafI`/`annotateLamsLeafI`, and it is precisely
the one whose freshly-built results collide with memo keys (see D.5).

### D.3 What the other entry points cost per step

* **whnf/whnfCore/infer/annotate/inferIO** are each memoised under a single `Expr` key: `memoEI`
  (`CoreC.lean:1877-1891`) probes `Std.HashMap Expr Expr`.  Key hash is the packed word (`O(1)`);
  key *equality* is `Expr.beq` (`StateC.lean:26-34`).
* **defeq** is memoised on the **pair**, `Std.HashMap (Expr × Expr) Bool` (`memoBI`,
  `CoreC.lean:1893-1906`; `CState.defeqC`, `StateC.lean:151`) — one `Prod` allocated per probe and
  per write.
* `defeqStepI` (`CoreC.lean:1456-1612`) per step: `a == b`; the Bool-true shortcut; **two whnfCore
  calls**; `a' == b'`; `propIrrelI` (which itself runs `inferIO` on both sides —
  `DESIGN.md:22492-22496`, rows 2–6); literal folding; lazy delta with the reducibility-hint
  comparison; then the congruence cases, each of which opens binders with `inst1M` against a fresh
  `Expr.fvar depth ty` (`CoreC.lean:1575-1583`).
* **The knot is rebuilt per cache-missing call.**  `coreKnotI` (`CoreC.lean:1916-1982`) recurses
  as `let prev : Unit → CoreFnsI := fun _ => coreKnotI fe fuel` (`:1935`) — a `Unit` closure,
  deliberately **not** a `Thunk` (the comment at `:1917-1934` records that the `Thunk` version
  cost 13.8 % of `init-full` via `lean_mark_mt`).  The price of the replacement is priced in the
  same campaign: seven allocations (one record, six closures) at every memo-missing body call, **≈
  +60 G on `init-full`, ~9 % of the post-fix total** (`DESIGN.md:48366-48371`).
* **Fuel** is a `Nat` threaded three ways: the knot's recursion-depth budget `checkFuel = 100000`
  (`ConLeche/Kernel/Core.lean:2941`; every entry point is `(coreKnotI mode fe checkFuel).…`, e.g.
  `ConLeche/Cached/CheckerC.lean:71-79`), the per-loop step budgets `whnfCoreLoopFuel = 1000000` /
  `whnfLoopFuel = 100000` / `defeqLoopFuel = 100000` (`Core.lean:2029,2038,2681`), and `peelFuel =
  16777216` for the binder telescopes (`StateC.lean:172`).  Task #161's profiling put **fuel
  arithmetic below 0.05 %, "unmeasurable"** (`DESIGN.md:26999-27002`) — the fuel *plumbing* is not
  a cost; the *knot rebuild that carries it* is.

### D.4 What `Expr.beq` costs (the memo-probe comparison)

`ConLeche/Kernel/Expr.lean:955-985`.  The executed equality is `beqMemo`: `withPtrEq` (pointer
test) → `a.data == b.data` (the packed word, a cheap reject) → `beqDec` → `beqGo beqBudget none a
b` (`:952-953`).  `beqGo` (`:830`) descends **allocation-free on a 4096-node budget**
(`beqBudget`, `:773`) and only then materialises a `Std.HashMap Nat EqPair` memo, keyed by the
packed address pair `beqKey` (`:764`), which is a scalar `Nat` below `2^62` and so costs no
allocation (`:758-763`).  Leaves are neither probed nor recorded (`beqRecursive`, `:735`).

That is the fixed version.  The **mechanism it defends against** is stated at `Expr.lean` (quoted
in `DESIGN.md:51955-51960`) and is the central cost finding of this codebase:

> hash-consing identifies structurally equal terms however they arose,
> so the arena never compares two distinct-but-equal DAGs; the clone
> does exactly that whenever a reduction rebuilds a term the arena would
> have collapsed.

### D.5 Where sharing is lost

This is the crux, and it is documented rather than inferred.

* **`internI` is `ExprC.ofView`, a plain allocation with no hash-consing**
  (`DESIGN.md:51944-51949`).  Every rebuild — `annotate`'s `instListRevM`/`abstractRangeM`
  telescopes, `betaPeelI`'s `instListM`, `whnfAppI`'s `.app` reconstruction — **mints a fresh node
  that is structurally equal to one already in a memo and can never be pointer-equal to it.**
* Consequence: the memo probe's pointer test misses, the hash test cannot help (entries in one
  bucket share a hash by construction), and the probe walks the whole DAG
  (`DESIGN.md:51944-51953`).
* The extreme form of this was task #240: an `infer` memo probe compared a bulk-opened λ-telescope
  body against the DAG a previous open had produced; **one side more shared than the other**, so
  the (then half-keyed) memo re-bound 99.79 % of its writes and the walk entered **8.9 billion
  nodes for 4 687 comparisons over a 42 579-node DAG** (`DESIGN.md:62943-62965`).  The pair key
  fixed the memo; it did not fix the fact that the two sides are distinct objects.
* Node-identity preservation is closed, not by choice but by the cut's exactness
  (`DESIGN.md:44912-44922`).
* A partial mitigation is in place: unchanged atoms are returned **by reference**
  (`ExprOpsC.lean:20-27`), and a static 4096-entry `bvarPool` makes every runtime `bvar` a
  persistent, borrowed, refcount-free object (`Expr.lean:1023-1032`, `DESIGN.md:44960-44990`).

### D.6 Reference-counting churn

Two of the three biggest single wins in the project's history were RC mechanics, not algorithms:

* **`lean_mark_mt` / `lean_copy_expand_array`** (task #179): a `Thunk` in the knot marked the
  whole reachable graph multi-threaded, so `FEnv.push` stopped updating in place and copied the
  bucket array with an atomic `lean_inc` per slot at every accepted constant. Removing the `Thunk`
  was **−16.4 % on `init-full`**; `lean_mark_mt` went 10.91 % → 0.00 %, `lean_dec_ref_cold` 17.64
  % → 10.26 % (`DESIGN.md:48264-48276`).
* **The heap the check phase allocates from** (task #269): the same computation on a worker thread
  with a fresh mimalloc heap runs **2.06× faster at −1.8 % instructions** — IPC 1.29 → 2.59, **24×
  fewer demand DRAM fills per instruction** (`DESIGN.md:67845-67870`).  con-leche's working set
  does not fit; the cost is memory latency on scattered allocator pages.
* The linearity discipline is written into the driver itself: the install loop is hand-written
  tail-recursive precisely so that the C carries no `lean_inc` of `FEnv`/`CState` before each
  step, "quadratic at Mathlib scale" otherwise (`Main.lean:85-99`).

### D.7 Reading the two worst streams

`app-lam` 5.35× and `beta-ladder` 3.95× are the outliers, and **trusted equals verified on both to
five significant figures** (`perf-data/table.tsv:4-6,13-15`).  Since `--trusted` skips every
certificate family outright (`ConLeche/Kernel/Env.lean:161-172`, `:174-176` — `betaSkip` is
`!mode.certs || …`, so at `.trusted` it is the literal `true`), **the certificates explain none of
those two ratios.**  What is left is exactly §D.2/D.5: these are binder-tower fixtures (`app-lam`
is the corpus's 4 000-binder tower — `DESIGN.md:44977-44980`), so every step is a substitution
that rebuilds a body, and every rebuilt body is a fresh object that the next memo probe cannot
recognise.  Task #161's own reading agrees: `app-lam` is "a binder-chain workload… front-door
work, not cone work" with only 5.8 % of its inference internal (`DESIGN.md:22574-22578`).

Conversely `mathlib-full` at 1.06× trusted is **near parity**, and `let-ladder` at 1.31× and
`init-prelude`/`grind-ring-5` at 1.38–1.69× are within the band the project treats as the
engineering floor.

---

## E. What a new core would and would not remove

### E.1 An NbE core (values with closures, no substitution, readback at the end)

**Would remove:**

* The substitution walks outright: `instantiate1GoC`, `instantiateListGoC`, `instantiateRevGo`,
  `abstract1GoC`, `abstractRangeGoC` (`ExprOpsC.lean:86,281,360,444,502`) — profile bucket (ii)'s
  `instantiate*Go`/`abstractRangeGo` self time (4.3–6.6 %) **plus** their `Std.DHashMap` spec
  sites (6.3–11.2 %), i.e. 11–18 % directly.
* The node allocations those walks make, and therefore a large, unquantified share of the
  allocator/RC bucket that is 34–40 % of every run (bucket (ii)) and ~50 % of the tail profiles
  (bucket (iii)).  Each removed allocation also removes the packed-word computation
  (`Expr.lean:358-404`).
* **The distinct-but-equal-DAG problem** (§D.5) in its whnf/infer form: with environments, a
  closure body is *never* rebuilt, so the object identity that the memo probes and `Expr.beq`'s
  pointer test depend on is preserved by construction. This is the cost that `Expr.lean`'s own
  docstring names as the clone's structural price.
* Much of the beq traffic that dominates the tail (39–46 % on four of five slowest declarations,
  bucket (iii)) — though **not all**: NbE still needs conversion checking, which compares values,
  and the α/β/η work moves rather than disappears.

**Would not remove:** readback allocates terms (so `annotate`'s output, the stored types and the
environment still cost node construction); the defeq memo and its pair key still exist; the
knot-rebuild allocation (§D.3) is a Lean-idiom cost, not a representation cost, and survives
unless the knot changes too.

**Would add:** a proof bill. The whole verification tower (`ConLeche/Verify/Cached/*`) is a
simulation of the cached core against the pure spec core
(`ConLeche/Kernel/TypeChecker.lean:23-25`); an NbE core is a different function, not a different
implementation of the same one, and the existing "Thunk.get is definitionally the value, so no
proof moved" precedent (`DESIGN.md:27057-27065`) does **not** transfer.

### E.2 A delayed-substitution core (closures over environments, substitution forced lazily)

**Would remove:** the same walks, but only on the paths where the substitution is never fully
demanded — which is the common case in whnf-driven checking (you reduce to a head and compare
heads).  The domain substitution in `betaPeelI` (`CoreC.lean:918`) and the telescope opens in
`inferLamsLeafI`/`annotateLamsLeafI` (the `instListRevM` sites, `StateC.lean:202`) are the
concrete sites that would become lazy.

**Would remove less than NbE** where a term really is normalised (the `reduceNat` paths, iota on
large spines), and would keep the term representation, so the packed word, `Expr.beq`, the memo
keys and the existing proof tower all survive in recognisable form — a much smaller proof bill.

**Would not remove:** the fresh-object problem by itself. A delayed substitution that is
eventually forced still produces a *new* node; unless forcing is memoised on the closure identity,
the memo probes see the same distinct-but-equal DAGs they see today.

### E.3 Costs that are not in the core at all

Neither design touches these:

* **Parsing.** 26 s of 1143 s at Mathlib scale, 2.3 % (`PERF.md:103`). Profile bucket (i) put the
  parser at 0.2–4.7 % of a run (`DESIGN.md:27004-27010`).
* **The install phase** — inductive installation, the fixpoint route, the in-process `_model`
  generation for mutual/nested blocks, and the basis pins. 150 s, 13 % of the Mathlib `--jobs=1`
  run (`PERF.md:103`), and it is the **sequential floor**: 56 % of the eight-worker run. A faster
  core speeds up phase B and makes this fraction *worse*.
* **The annotate pass.** It has no official counterpart (`PERF.md:128-130`) and it is a whole
  extra traversal per declaration (`annotateBodyI`, `CoreC.lean:1780-1866`). A new core would have
  to carry it or replace it; it is not removed by either design as such. (It is also the site that
  generates the unshared telescope rebuilds of §D.5 — `DESIGN.md:51915-51922` — so a core that
  opens binders without rebuilding would help it indirectly.)
* **Memory and the allocator's page scatter.** Task #269's 2.06× is a heap-locality effect, not an
  algorithmic one (`DESIGN.md:67845-67870`). A core with a smaller working set would benefit from
  it; the effect itself lives below the core.
* **The certificates.** They are a *verification* decision, gated by `CheckMode.certs`
  (`ConLeche/Kernel/Env.lean:161-172`), currently worth 3.3 % (`init-full`) to 7.7 %
  (`mathlib-full`) and **0 % on the two streams where con-leche is furthest behind**. Any new core
  inherits them unchanged, or replaces them with new obligations of its own.

---

## F. What is unknown, and what a decision needs first

Stated plainly, because the honest answer to "where does the time go today" is *"we know the
buckets, not the functions, and the bucket measurements are between three and eighteen days old on
a tree that has moved 6.5 % since."*

1. **There is no current per-function profile.** The last one (`DESIGN.md:44858-44868`, task #177,
   2026-09-06) predates #179's Thunk removal, #240's beq pair key, #264's parse work, #266–#268's
   install work, #272's telescope datum and #269's worker-thread lane — changes that between them
   moved `mathlib-full` 6.5 % (`DESIGN.md:68039-68045`). **A `perf record -e instructions:u`
   against the `1d470aa7` binary, on `app-lam` / `beta-ladder` / `init-full` / a Mathlib prefix,
   in both modes, is the first thing any core decision needs.** Snapshot the binary first
   (`DESIGN.md:48298-48306`).
2. **No instruction-level phase split exists.** The parse/install/check split is wall time on one
   stream. An instruction split per phase is cheap to get (the heartbeat already brackets the
   phases — `Main.lean:333-360`) and would tell the study how much of the run a core can address
   at all.
3. **The allocator/RC bucket is not decomposed.** 34–50 % of every profile is `mi_malloc_small` /
   `mi_free` / `lean_dec_ref_cold` / `lean_del_core_other`, and no record attributes those samples
   to the *call sites* that allocate. perf's dwarf call graph does not resolve on this binary
   (tail calls, no frame pointers, the 127-frame cap — `DESIGN.md:48317-48325`, `:62921-62926`);
   the working technique is gdb backtrace sampling (`DESIGN.md:51888-51900`). Without that
   attribution, "NbE removes the allocations" is an argument, not a number.
4. **`app-lam`'s 5.35× has never been decomposed.** We know it is not certificates (§D.7) and not
   internal inference (5.8 % — `DESIGN.md:22576`). We do *not* know the split between substitution
   rebuild, memo probe, and allocator on that specific stream at the current binary. It is the
   cheapest decisive experiment available: one stream, 25 s, two modes.
5. **The memo hit rates are unmeasured.** How often `whnfCoreC`, `inferC`, `defeqC` and `instC`
   actually hit — and how much of the miss rate is the fresh-object problem of §D.5 rather than
   genuine novelty — decides whether NbE's identity preservation is worth percent or multiples.
   Task #240 showed the project has the technique (compiled counters behind a `@[noinline]` sink —
   `DESIGN.md:62943-62948`).
6. **The Mathlib-scale memory-latency effect may dominate whatever the core does.** Task #269
   found IPC 1.29 vs 2.59 for the *same instructions* depending only on which heap they allocate
   from (`DESIGN.md:67851-67856`). A core that retires 30 % fewer instructions on a working set
   that still does not fit may not be 30 % faster in wall time, and instructions:u — the project's
   only sanctioned metric — will not show that.
7. **No self-check, cslib or std perf lane exists** to cross-check a new core on a different
   corpus shape; the battery is seven streams (`scripts/perf-tables.sh:66`).

### One structural observation to carry forward

The streams where con-leche is furthest from official (`app-lam` 5.35×, `beta-ladder` 3.95×) are
exactly the streams where the verification tax is **zero** and the internal-inference tax is
**near zero**. The streams where the verification tax is largest (`mathlib-full`, +7.7 %) are the
ones where con-leche is nearest parity (1.06× trusted). So the gap a new core would close is
**not** the price of being verified — it is the price of rebuilding terms instead of closing over
them, which is what both candidate designs are about.


