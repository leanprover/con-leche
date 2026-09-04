#!/usr/bin/env python3
"""Render PERF.md from the battery's raw TSV.

    perf-tables-render.py table.tsv PERF.md meta.txt [perf-data-dir]

Pure formatting: every number comes from the TSV, every caveat is
static text.  Re-runnable without re-measuring (`perf-tables.sh
--render`).

LAYOUT RULE (user, 2026-09-04): *less noise, fewer axes, just the
numbers.*  Only live, mutually comparable configurations appear.
Anything retired or superseded leaves the tables entirely and is
reachable through one pointer line; instructions are the only metric
printed.
"""
import sys, os

tsv, out_path, meta_path = sys.argv[1], sys.argv[2], sys.argv[3]
data_dir = sys.argv[4] if len(sys.argv) > 4 else None


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
        if s not in cs:
            cs[s] = {}
            order.append(s)
        cs[s][c] = dict(instr=int(instr or 0), wall=float(wall or 0),
                        exit=int(ex), decls=decls)
    return cs, order


meta = read_meta(meta_path)
cells, stream_order = read_cells(tsv)
retired_path = os.path.join(data_dir, "retired.tsv") if data_dir else None
has_archive = bool(retired_path and os.path.exists(retired_path))

# Column catalogue.  A configuration is printed only if the run declared
# it live (meta `configs`) AND it produced cells.  Everything else — a
# retired flag, a lane whose meaning changed, a dropped representation —
# is archived, never shown beside numbers it cannot be compared with.
LABELS = {
    "official":  "official v4.33.0",
    # transitional: mode x core
    "sm-prod":   "`--set-model` `--core=production`",
    "sm-cached": "`--set-model` `--core=cached-parsed`",
    "nm-prod":   "`--no-model` `--core=production`",
    "nm-cached": "`--no-model` `--core=cached-parsed`",
    # post-tri-core: the three lanes on the one representation
    "parity":    "parity (`--no-model`)",
    "R":         "R (`--set-model=r`)",
    "P":         "P (`--set-model=p`)",
}
SHORT = {"official": "official", "sm-prod": "SM/prod", "sm-cached": "SM/cached",
         "nm-prod": "NM/prod", "nm-cached": "NM/cached",
         "parity": "parity", "R": "R", "P": "P"}

# every configuration the data actually contains, catalogued or not, so
# that a column retired before the catalogue existed still gets counted
# as superseded rather than vanishing without trace
present = []
for s in stream_order:
    for c in cells[s]:
        if c not in present:
            present.append(c)

if meta.get("configs"):
    live = [c for c in meta["configs"].split() if c in present]
else:
    # Snapshot from before the matrix was declared in metadata: fall back
    # to the flags, so an old table still renders without stale columns.
    live = [c for c in present if not c.startswith("tt-")]
    if meta.get("cachednc", "no") != "yes" and "nm-cached" in live:
        live.remove("nm-cached")
    if meta.get("interned", "yes") != "yes":
        live = [c for c in live if not c.endswith("-prod")]
superseded = [c for c in present if c not in live]

REPS = meta.get("reps", "1")
runs_note = ("single run per cell" if REPS == "1"
             else f"median of {REPS} per cell")


def ok(r):
    return r is not None and r["exit"] == 0 and r["instr"] > 0


def g(n):
    return f"{n / 1e9:.2f}"


def cell_text(r, base):
    if r is None:
        return "—"
    if r["exit"] != 0:
        return f"**exit {r['exit']}**"
    return f"{g(r['instr'])} G" + (f" ({r['instr'] / base:.2f}×)" if base else "")


L = []
A = L.append

A("# PERF.md — the setlec performance tables")
A("")
A("Regenerated end to end by `scripts/perf-tables.sh` (renderer:")
A("`scripts/perf-tables-render.py`).  Every number below is measured;")
A("nothing here is carried over from an older round.")
A("")
A("| | |")
A("|---|---|")
A(f"| commit measured | `{meta.get('sha', '?')}`"
  + (" **(dirty working tree)**" if meta.get("dirty", "0") not in ("0", "") else "") + " |")
if meta.get("binsha") and meta.get("binsha") != meta.get("sha"):
    A(f"| binary provenance | `{meta['binsha']}` — the last commit that can change "
      "`.lake/build/bin/setlec`; the commits between it and the one above touch "
      "only `scripts/` and this file |")
A(f"| battery started | {meta.get('date', '?')} |")
A(f"| machine | {meta.get('host', '?')} — {meta.get('cpu', '?')}, "
  f"{meta.get('cores', '?')} cores, {meta.get('mem', '?')} RAM, Linux {meta.get('kernelver', '?')} |")
A(f"| runs per cell | {runs_note} |")
A(f"| per-run timeout | {meta.get('timeout', '?')} s |")
A(f"| official kernel | `{meta.get('official', '?')}` |")
A(f"| preprocessor | `{meta.get('preproc', '?')}` |")
A("")

A("## Regenerating this file")
A("")
A("One line, from the repository root:")
A("")
A("```")
A("lake build setlec && scripts/perf-tables.sh")
A("```")
A("")
A("Useful variants:")
A("")
A("```")
A("scripts/perf-tables.sh --render                  # re-render from the saved cells")
A("PERF_STREAMS=init-full PERF_APPEND=1 scripts/perf-tables.sh   # re-run one stream")
A("PERF_CONFIGS=nm-cached PERF_APPEND=1 scripts/perf-tables.sh   # confirm one suspect cell")
A("```")
A("")
A("Per timed run, verbatim from the script:")
A("")
A("```")
A("(ulimit -v 41943040; SETLEC_SUPERVISED=1 \\")
A("   perf stat -e instructions:u -x, -o $po \\")
A("   timeout $TIMEOUT nice -n 5 <checker> <flags> <preprocessed-stream>)")
A("```")
A("")
A("**Preprocessed input on both sides.**  `lean-inductive-models` is run")
A("once per stream, off the clock; the resulting file is fed to the")
A("official kernel *and* to setlec under `--pre`.  No setlec cell pays")
A("the preprocessor or its process spawn, and both checkers see the same")
A("bytes.  **All flags are passed explicitly** — no cell relies on a")
A("mode-aware default.  One timed cell runs at a time, and each waits")
A("for the machine to go idle first.")
A("")

A("## The table — instructions:u in G, ratio vs official")
A("")
A("| stream | " + " | ".join(LABELS.get(c, c) for c in live) + " |")
A("|" + "---|" * (len(live) + 1))
for s in stream_order:
    base_rec = cells[s].get("official")
    base = base_rec["instr"] if ok(base_rec) else 0
    A(f"| `{s}` | " + " | ".join(
        cell_text(cells[s].get(c), base if c != "official" else 0)
        for c in live) + " |")
A("")
A("Ratios are against the official column on the same row.  They are")
A("cross-pipeline, not same-work speed ratios — caveat 1.")
A("")

A("## Accepted declarations (verdict sanity)")
A("")
A("| stream | " + " | ".join(SHORT.get(c, c) for c in live) + " |")
A("|" + "---|" * (len(live) + 1))
for s in stream_order:
    row = []
    for c in live:
        r = cells[s].get(c)
        row.append("—" if r is None else
                   (f"exit {r['exit']}" if r["exit"] != 0 else (r["decls"] or "?")))
    A(f"| `{s}` | " + " | ".join(row) + " |")
A("")

# Derived: the verification tax, wherever a certified column and a
# cert-free column share a core.
PAIRS = [("sm-prod", "nm-prod", "production"),
         ("sm-cached", "nm-cached", "cached-parsed"),
         ("R", "parity", "R ÷ parity"),
         ("P", "parity", "P ÷ parity")]
pairs = [(a, b, n) for a, b, n in PAIRS if a in live and b in live]
if pairs:
    A("## Derived: the verification tax")
    A("")
    A("The certified checker over the cert-free lane — same binary, same")
    A("stream, same engine.")
    A("")
    A("| stream | " + " | ".join(n for _, _, n in pairs) + " |")
    A("|" + "---|" * (len(pairs) + 1))
    for s in stream_order:
        row = []
        for a, b, _ in pairs:
            ra, rb = cells[s].get(a), cells[s].get(b)
            row.append(f"{ra['instr'] / rb['instr']:.2f}×"
                       if ok(ra) and ok(rb) else "—")
        A(f"| `{s}` | " + " | ".join(row) + " |")
    A("")

if superseded or has_archive:
    names = ", ".join(f"`{c}`" for c in superseded) if superseded else ""
    A("## Superseded cells")
    A("")
    A("Configurations that have left the matrix — a retired flag, a lane")
    A("whose meaning changed, an earlier representation — are not shown")
    A("above; their cells keep full provenance (the binary that measured")
    A("them) in `perf-data/retired.tsv`."
      + (f"  Currently held there: {names}." if names else ""))
    A("")

A("## CAVEATS")
A("")
A("1. **Cross-pipeline, not same-work.**  Both sides read the same")
A("   preprocessed bytes, so no setlec cell pays the preprocessor — but")
A("   every setlec cell checks a *modeled* encoding of the inductive")
A("   blocks, plus an `annotate` pass with no official counterpart,")
A("   while official checks that file with native inductive/recursor")
A("   support.  Every official ratio carries that difference.")
A("2. **Declaration counts differ from official** — the preprocessor's")
A("   `_model` declarations.  On a preprocessed stream the gap is small")
A("   but never zero, and the two checkers are not checking the same")
A("   list.")
A("3. **`--no-model` under-checks install-only kinds** relative to")
A("   official (axioms, inductive blocks, quot and the pinned-cert")
A("   branches run at io grade there, where official's declaration-type")
A("   check is `check`).  This flatters the cert-free columns on")
A("   inductive-heavy streams — init-full most of all.")
if REPS == "1":
    A("4. **One run per cell, one machine.**  The medians-of-3 round")
    A("   measured per-cell spreads at 0.01–0.5 % on instructions:u, so")
    A("   a single run carries the figures printed here.  Instructions:u")
    A("   is robust to the concurrent load this shared machine sees; a")
    A("   cell that ever looks wrong should be re-run on its own rather")
    A("   than the whole battery re-medianed.")
else:
    A(f"4. **Median of {REPS} per cell, one machine.**  Instructions:u is")
    A("   robust to the concurrent load this shared machine sees.")
A("5. **Fuel.**  setlec compiles in `checkFuel = 100000` plus")
A("   `defeqLoopFuel`; official has no fuel.  No row above exhausts it.")
if any(c.endswith("-cached") for c in live):
    A("6. **`--core=cached-parsed`, not `--core=cached`.**  The latter")
    A("   parses but selects `checkDeclsSharedC`, an explicitly")
    A("   unverified pilot instrument; the cached column is the")
    A("   supported, verified core (task #163).")
A("")

A("## Raw data")
A("")
A("Tracked in `perf-data/`: `table.tsv` (the cells behind the tables),")
A("`meta.txt` (the run's provenance), and `retired.tsv` / `retired.meta`")
A("(superseded cells, stamped with the binary that measured them).  One")
A("line per cell: `stream, config, instructions:u, wall s, exit code,")
A("accepted declarations, 1-min load average at launch, verdict text` —")
A("wall and load are recorded but not printed.")
A("")
A("The working copy of a run lives at `_tmp/perf-tables/` (gitignored,")
A("so it is a cache and not the record); preprocessed streams are cached")
A("beside it at `_tmp/perf-tables/pre/`.")
A("")

open(out_path, "w").write("\n".join(L) + "\n")
print(f"rendered {out_path} ({len(stream_order)} streams, "
      f"{len(live)} live columns, {len(superseded)} superseded)")
