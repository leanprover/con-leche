#!/usr/bin/env python3
"""Render PERF.md from the battery's raw TSV.

    perf-tables-render.py table.tsv PERF.md meta.txt [census.tsv]

Pure formatting: every number comes from the TSV.  Re-runnable without
re-measuring (`perf-tables.sh --render`).

LAYOUT RULE (user, 2026-09-05): *three columns, instructions only, one
run per cell, no superseded noise.*  The file shows the current matrix —
official, trusted (`--trusted`), verified (`--verified`) — with the exit code
and accepted-declaration count beside every cell, and nothing else.  No
historical columns, no retired flags, no "was X" annotations; prose stays
at a few lines.

Task #187 adds, without breaking that rule: the input census (a property
of each stream, not of any checker), and — for the `mathlib-full` row
only — wall minutes and peak RSS, printed as data in their own small
table.
"""
import sys, os

tsv, out_path, meta_path = sys.argv[1], sys.argv[2], sys.argv[3]
census_path = sys.argv[4] if len(sys.argv) > 4 else None


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
        if len(f) < 14 or f[0] == "stream":
            continue
        keys = ["records", "official", "fold", "quot", "quot_axioms",
                "tolerated", "inductive", "pinned", "modeled", "native",
                "native_structures", "native_sums", "native_indexed"]
        rows[f[0]] = {k: int(v) for k, v in zip(keys, f[1:])}
    return rows


meta = read_meta(meta_path)
cells, stream_order = read_cells(tsv)
census = read_census(census_path)

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
  f"(the `mathlib-full` row: 22 GB, 8 h, `CON_LECHE_PROGRESS=5000`) |")
A("| streams | RAW `lean4export` NDJSON; both checkers read the same "
  "bytes and do the same job (task #207: there is no preprocessing "
  "step, so these numbers are not comparable with any earlier PERF.md) |")
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
    A("Properties of the raw FILE, computed by")
    A("`scripts/stream-census.py` — nobody's environment representation")
    A("enters here.  `records` is the number of declaration records in the")
    A("file; `con-leche` and `official` are what each checker's verdict line")
    A("reports on it, both derived from the file alone (see the count note")
    A("below).  `modeled` counts blocks the STREAM carries a `_model`")
    A("family for — 0 on every raw stream since task #207; `native` is the")
    A("rest, which con-leche installs itself (a direct route, or a model")
    A("it generates in-process), split by shape.")
    A("")
    A("**The `con-leche` column is the FILE's count and is lower than the")
    A("verdict line's** on any stream with a mutual or nested block: the")
    A("in-process modeller pushes its generated records ahead of the block")
    A("and the fold counts them, but they are not in the file, so this")
    A("census cannot see them (on `init-prelude`, `grind-ring-5` and")
    A("`init-full` the gap is exactly 30 — `Lean.Syntax`'s generated")
    A("family; `CON_LECHE_INMODEL_DUMP`'s output censuses to the verdict")
    A("number exactly).  Before task #207 the models arrived IN the file,")
    A("so the two agreed.  The exit-code table above carries the verdict")
    A("counts.")
    A("")
    A("| stream | records | con-leche | official | pinned | modeled | native | structures | sums | indexed |")
    A("|" + "---|" * 10)
    for s in stream_order:
        c = census.get(s)
        if not c:
            A(f"| `{s}` | — | — | — | — | — | — | — | — | — |")
            continue
        A(f"| `{s}` | {c['records']} | {c['fold']} | {c['official']} | "
          f"{c['pinned']} | {c['modeled']} | {c['native']} | "
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

A("## Notes")
A("")
if meta.get("stalenote"):
    A(f"* {meta['stalenote']}")
if meta.get("mathlibnote"):
    A(f"* {meta['mathlibnote']}")
A("* **The verdict line counts declaration RECORDS** (task #187).  It")
A("  used to print `env.consts.length`, the number of environment")
A("  CONSTANTS, which counts an inductive block's type former, its")
A("  constructors, its recursor and its projection table separately —")
A("  a property of con-leche's representation that moved whenever the")
A("  representation moved.  It now prints the STREAM's record count —")
A("  `decls.size - preludeCount + preludeDropped` since task #191's")
A("  built-in prelude, so a stream that re-declares a prelude block")
A("  identically reports what it declared.  `CON_LECHE_VERBOSE=1` still")
A("  prints the constant count, on stderr, beside it.")
A("* **The official number is not a record count either.**  Its")
A("  `Main.lean` prints `constMap.size`: one entry per exported")
A("  constant, so an inductive record contributes its type formers, its")
A("  constructors AND its recursors, less the three `Quot.mk`/`.lift`/")
A("  `.ind` entries it erases before replay.  Both numbers are now")
A("  functions of the input file alone, and the census table above")
A("  reproduces each of them exactly from the bytes.")
A("* **Same bytes, same job — but not the same work.**  Both sides read")
A("  the same raw file and install every inductive block themselves")
A("  (task #207).  con-leche installs most blocks through a direct")
A("  route and a mutual/nested one through a `_model` family it")
A("  GENERATES and then checks as ordinary declarations (the")
A("  certification tax), and runs an `annotate` pass with no official")
A("  counterpart; official has native inductive/recursor support.")
A("* **`--trusted` under-checks install-only kinds** (axioms, inductive")
A("  blocks, quot, the pinned-cert branches run at io grade), which")
A("  flatters the trusted column on inductive-heavy streams.")
A("* One run per cell on a shared machine: `instructions:u` is")
A("  contention-independent, so a cell may overlap other work; wall time")
A("  is not reported for that reason (the Mathlib row's minutes are")
A("  labelled as data, above).")
A("* Regenerate with `lake build con-leche && scripts/perf-tables.sh`;")
A("  `--render` re-renders from `perf-data/` without measuring, and")
A("  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream.  The")
A("  `mathlib-full` row needs its raw stream exported by hand first.")
A("  Raw cells (with")
A("  wall time and load) are tracked in `perf-data/table.tsv`, the input")
A("  census in `perf-data/census.tsv`, provenance in `perf-data/meta.txt`.")
A("")

open(out_path, "w").write("\n".join(L) + "\n")
print(f"rendered {out_path} ({len(stream_order)} streams, {len(live)} columns)")
