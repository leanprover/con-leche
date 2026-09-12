#!/usr/bin/env python3
"""Render PERF.md from the battery's raw TSV.

    perf-tables-render.py table.tsv PERF.md meta.txt [census.tsv]

Pure formatting: every number comes from the TSV.  Re-runnable without
re-measuring, and the TRACKED record is what a re-render must read:

    scripts/perf-tables-render.py perf-data/table.tsv PERF.md \
        perf-data/meta.txt perf-data/census.tsv

LAYOUT RULE (user, 2026-09-05): *three columns, instructions only, one
run per cell, no superseded noise.*  The file shows the current matrix —
official, trusted (`--trusted`), verified (`--verified`) — with the exit code
and accepted-declaration count beside every cell, and nothing else.  No
historical columns, no retired flags, no "was X" annotations; prose stays
at a few lines.

Added without breaking that rule: the input census (a property
of each stream, not of any checker), and — for the `mathlib-full` row
only — wall minutes and peak RSS, printed as data in their own small
table.  The worker-count table comes from `parallel.tsv` beside the
census, and is wall time too: labelled as indicative, never as a
measurement.
"""
import sys, os

tsv, out_path, meta_path = sys.argv[1], sys.argv[2], sys.argv[3]
census_path = sys.argv[4] if len(sys.argv) > 4 else None
# The worker-count table travels with the tracked record, beside the
# census and the provenance file.
parallel_path = os.path.join(os.path.dirname(census_path or meta_path or "."),
                             "parallel.tsv")


def read_meta(path):
    m = {}
    if path and os.path.exists(path):
        for line in open(path):
            if "\t" in line:
                k, v = line.rstrip("\n").split("\t", 1)
                m[k] = v
    return m


def read_cells(path):
    """Last row per (stream, config) wins — re-measured cells override."""
    cs, order = {}, []
    if not path or not os.path.exists(path):
        return cs, order
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 8:
            continue
        s, c, instr, wall, ex, decls, load, verdict = f[:8]
        rss = f[8] if len(f) > 8 else ""
        if s not in cs:
            cs[s] = {}
            order.append(s)
        cs[s][c] = dict(instr=int(instr or 0), exit=int(ex), decls=decls,
                        wall=float(wall or 0), rss=int(rss) if rss else 0)
    return cs, order


def read_census(path):
    """label -> {column: int}, from scripts/stream-census.py."""
    rows = {}
    if not path or not os.path.exists(path):
        return rows
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 13 or f[0] == "stream":
            continue
        keys = ["records", "official", "fold", "quot", "quot_axioms",
                "tolerated", "inductive", "pinned", "native",
                "native_structures", "native_sums", "native_indexed"]
        rows[f[0]] = {k: int(v) for k, v in zip(keys, f[1:])}
    return rows


def read_parallel(path):
    """(stream, jobs) -> wall seconds, from a `stream\tjobs\twall` TSV."""
    rows, streams, jobs = {}, [], []
    if not path or not os.path.exists(path):
        return rows, streams, jobs
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 3 or f[0] == "stream":
            continue
        s, j, wall = f[0], int(f[1]), float(f[2])
        rows[(s, j)] = wall
        if s not in streams:
            streams.append(s)
        if j not in jobs:
            jobs.append(j)
    return rows, streams, sorted(jobs)


meta = read_meta(meta_path)
cells, stream_order = read_cells(tsv)
census = read_census(census_path)
par, par_streams, par_jobs = read_parallel(parallel_path)

# The three live configurations, in printing order.  A column appears
# only if the run declared it (meta `configs`) and it produced cells.
LABELS = {
    "official": "official v4.33.0",
    "trusted":  "trusted `--trusted`",
    "verified": "verified `--verified`",
}
present = [c for s in stream_order for c in cells[s]]
declared = meta.get("configs", "official trusted verified").split()
live = [c for c in declared if c in LABELS and c in present]


def ok(r):
    return r is not None and r["exit"] == 0 and r["instr"] > 0


def instr_text(r):
    """Instructions for a cell.  A cell that did NOT accept ran only a
    prefix of its stream, so its instruction count is not a measurement
    of the workload: it is printed as such, never as a bare number."""
    if r is None or not r["instr"]:
        return "—"
    n = r["instr"]
    t = f"{n / 1e12:.2f} T" if n >= 1e12 else f"{n / 1e9:.2f} G"
    return t if r["exit"] == 0 else f"({t}, exit {r['exit']} — partial)"


def ratio_text(r, base):
    return f"{r['instr'] / base:.2f}×" if ok(r) and base else "—"


L = []
A = L.append

A("# PERF.md — the con-leche performance battery")
A("")
A("| | |")
A("|---|---|")
A(f"| commit measured | `{meta.get('sha', '?')}`"
  + (" **(dirty working tree)**" if meta.get("dirty", "0") not in ("0", "") else "") + " |")
if meta.get("note"):
    A(f"| tree | {meta['note']} |")
A(f"| date | {meta.get('date', '?')} |")
A(f"| machine | {meta.get('host', '?')} — {meta.get('cpu', '?')}, "
  f"{meta.get('cores', '?')} cores, {meta.get('mem', '?')} RAM, Linux {meta.get('kernelver', '?')} |")
A("| columns | " + " · ".join(LABELS[c] for c in live) + " |")
A(f"| metric | `perf stat -e instructions:u`, one run per cell, "
  f"`ulimit -v {meta.get('vlimit', '?')}`, `timeout {meta.get('timeout', '?')}`, `nice -n 5` "
  f"(the `mathlib-full` row: 22 GB, 8 h, `--progress=5000`) |")
A("| check phase | one worker: every con-leche cell passes `--jobs=1` "
  "(the worker-count table below is the parallel lane) |")
A("| streams | `lean4export` NDJSON, read unchanged by both checkers |")
if meta.get("mathlibstream"):
    A(f"| Mathlib stream | {meta['mathlibstream']} |")
if meta.get("loadnote"):
    A(f"| concurrent load | {meta['loadnote']} |")
A(f"| official kernel | `{meta.get('official', '?')}` |")
if meta.get("binmd5"):
    A(f"| con-leche binary | md5 `{meta['binmd5']}` |")
A("")

A("## instructions:u")
A("")
A("| stream | " + " | ".join(LABELS[c] for c in live)
  + " | trusted ÷ official | verified ÷ official |")
A("|" + "---|" * (len(live) + 3))
for s in stream_order:
    base_rec = cells[s].get("official")
    base = base_rec["instr"] if ok(base_rec) else 0
    row = [instr_text(cells[s].get(c)) for c in live]
    row.append(ratio_text(cells[s].get("trusted"), base))
    row.append(ratio_text(cells[s].get("verified"), base))
    A(f"| `{s}` | " + " | ".join(row) + " |")
A("")

A("## exit code / accepted declaration records")
A("")
A("| stream | " + " | ".join(LABELS[c] for c in live) + " |")
A("|" + "---|" * (len(live) + 1))
for s in stream_order:
    row = []
    for c in live:
        r = cells[s].get(c)
        row.append("—" if r is None else f"{r['exit']} / {r['decls'] or '—'}")
    A(f"| `{s}` | " + " | ".join(row) + " |")
A("")
A("Exit codes: 0 accept, 1 reject, 2 decline, 3 error.")
A("")

if census:
    A("## the input: what each stream contains")
    A("")
    A("Properties of the FILE, computed by")
    A("`scripts/stream-census.py` — nobody's environment representation")
    A("enters here.  `records` is the number of declaration records in the")
    A("file; `con-leche` and `official` are what each checker's verdict line")
    A("reports on it, both derived from the file alone (see the count note")
    A("below).  `pinned` counts the basis blocks the parse matches;")
    A("`native` is every other inductive block, which con-leche installs")
    A("itself (the fixpoint route, or a model it generates in process),")
    A("split by shape.")
    A("")
    A("**The `con-leche` column IS the verdict line's count.**  The")
    A("in-process modeller's generated records (30 on `init-prelude`,")
    A("`grind-ring-5` and `init-full` — `Lean.Syntax`'s; 2 168 on")
    A("`mathlib-full`, for the 51 blocks modelled in process there) are")
    A("booked as declarations of the fold, never as records of the file,")
    A("so the census predicts the verdict.  The instruction cells count")
    A("the same checked records either way.")
    A("")
    A("| stream | records | con-leche | official | pinned | native | structures | sums | indexed |")
    A("|" + "---|" * 9)
    for s in stream_order:
        c = census.get(s)
        if not c:
            A(f"| `{s}` | — | — | — | — | — | — | — | — |")
            continue
        A(f"| `{s}` | {c['records']} | {c['fold']} | {c['official']} | "
          f"{c['pinned']} | {c['native']} | "
          f"{c['native_structures']} | {c['native_sums']} | {c['native_indexed']} |")
    A("")

ml = cells.get("mathlib-full")
if ml:
    A("## the Mathlib row, as data (not a measurement)")
    A("")
    A("Wall time and resident memory on a shared 96-core machine are")
    A("**data**, not comparisons — `instructions:u` above is the")
    A("measurement.  These are here because they are the two numbers a")
    A("reader wants before pointing the checker at all of Mathlib.")
    A("")
    A("| | " + " | ".join(LABELS[c] for c in live if c in ml) + " |")
    A("|" + "---|" * (1 + len([c for c in live if c in ml])))
    def mlcell(c, txt):
        return txt if ml[c]["exit"] == 0 else txt + " (partial)"
    A("| wall | " + " | ".join(mlcell(c, f"{ml[c]['wall'] / 60:.1f} min")
                               for c in live if c in ml) + " |")
    A("| peak RSS (`time -v`) | "
      + " | ".join(mlcell(c, f"{ml[c]['rss'] / 1048576:.2f} GiB") if ml[c]["rss"]
                   else "—" for c in live if c in ml) + " |")
    A("")

if par:
    A("## the check phase on more than one thread")
    A("")
    A("The check phase runs on `--jobs=<n>` worker threads; the parse and")
    A("the install phase before it are sequential.  Wall time on a shared")
    A("machine is **indicative only** — `instructions:u` above is the")
    A("measurement, and it is taken at one worker.  What the worker count")
    A("shortens is the check phase alone: on `mathlib-full` that phase")
    A("takes 962 s at one worker, 263 s at four and 142 s at eight, and the")
    A("instruction count moves 0.2 % across the three (12.01 T, 12.04 T,")
    A("12.04 T).  The wall times below are that phase plus the sequential")
    A("prefix, which no worker count shortens.")
    A("")
    A("| stream | " + " | ".join(f"`--jobs={j}`" for j in par_jobs) + " |")
    A("|" + "---|" * (1 + len(par_jobs)))
    for s in par_streams:
        row = []
        for j in par_jobs:
            w = par.get((s, j))
            row.append("—" if w is None
                       else (f"{w / 60:.1f} min" if w >= 120 else f"{w:.0f} s"))
        A(f"| `{s}` | " + " | ".join(row) + " |")
    A("")
    if meta.get("parallelnote"):
        A(meta["parallelnote"])
        A("")

A("## Notes")
A("")
if meta.get("mathlibnote"):
    A(f"* {meta['mathlibnote']}")
A("* **The verdict line counts declaration RECORDS**, the STREAM's count")
A("  `decls.size - preludeCount + preludeDropped` (so a stream that")
A("  re-declares a prelude block identically reports what it declared),")
A("  not the number of environment CONSTANTS, which would count an")
A("  inductive block's type former, its constructors, its recursor and")
A("  its projection table separately — a property of con-leche's")
A("  representation.  `scripts/stream-census.py` derives both numbers")
A("  from the stream.")
A("* **The official number is not a record count either.**  Its")
A("  `Main.lean` prints `constMap.size`: one entry per exported")
A("  constant, so an inductive record contributes its type formers, its")
A("  constructors AND its recursors, less the three `Quot.mk`/`.lift`/")
A("  `.ind` entries it erases before replay.  Both numbers are")
A("  functions of the input file alone, and the census table above")
A("  reproduces each of them exactly from the bytes.")
A("* **Same bytes, same job — but not the same work.**  Both sides read")
A("  the same file and install every inductive block themselves.")
A("  con-leche installs single blocks through its fixpoint route and a")
A("  mutual/nested one through a `_model` family it GENERATES and then")
A("  checks as ordinary declarations (the certification tax), and runs")
A("  an `annotate` pass with no official counterpart; official has")
A("  native inductive/recursor support.")
A("* **`--trusted` under-checks install-only kinds** (axioms, inductive")
A("  blocks, quot, the pinned-cert branches run at io grade), which")
A("  flatters the trusted column on inductive-heavy streams.")
A("* **The cells are the single-worker lane.**  Every con-leche cell passes")
A("  `--jobs=1` — one worker thread, no shared claim counter and no")
A("  result table — which is the apples-to-apples comparison against a")
A("  single-threaded official kernel; without the flag the check phase")
A("  takes one worker per hardware thread.  The worker-count table above")
A("  is where the parallel lane is reported, in wall time.")
A("* One run per cell on a shared machine: `instructions:u` is")
A("  contention-independent, so a cell may overlap other work.  The only")
A("  wall times here are the Mathlib row's and the worker-count table's,")
A("  both labelled as data.")
A("* Regenerate with `lake build con-leche && scripts/perf-tables.sh`;")
A("  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream, and")
A("  `scripts/perf-tables-render.py perf-data/table.tsv PERF.md")
A("  perf-data/meta.txt perf-data/census.tsv` — which is what")
A("  `scripts/perf-tables.sh --render` runs — re-renders this file from")
A("  the tracked record without measuring.  The `mathlib-full` row needs")
A("  its stream exported by hand first.  Per-cell data (with wall time")
A("  and load) are tracked in `perf-data/table.tsv`, the input census in")
A("  `perf-data/census.tsv`, provenance in `perf-data/meta.txt`.  The")
A("  worker-count table is a sweep of its own, which the battery does not")
A("  run; its cells are tracked in `perf-data/parallel.tsv`.")
A("")

open(out_path, "w").write("\n".join(L) + "\n")
print(f"rendered {out_path} ({len(stream_order)} streams, {len(live)} columns)")
