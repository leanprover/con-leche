#!/usr/bin/env python3
"""Render PERF.md from the battery's raw TSV.

    perf-tables-render.py table.tsv PERF.md meta.txt

Pure formatting: every number comes from the TSV.  Re-runnable without
re-measuring (`perf-tables.sh --render`).

LAYOUT RULE (user, 2026-09-05): *three columns, instructions only, one
run per cell, no superseded noise.*  The file shows the current matrix —
official, trusted (`--trusted`), verified (`--verified`) — with the exit code
and accepted-declaration count beside every cell, and nothing else.  No
historical columns, no retired flags, no "was X" annotations; prose stays
at a few lines.
"""
import sys, os

tsv, out_path, meta_path = sys.argv[1], sys.argv[2], sys.argv[3]


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
        cs[s][c] = dict(instr=int(instr or 0), exit=int(ex), decls=decls)
    return cs, order


meta = read_meta(meta_path)
cells, stream_order = read_cells(tsv)

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
    if r is None:
        return "—"
    return f"{r['instr'] / 1e9:.2f} G" if r["instr"] else "—"


def ratio_text(r, base):
    return f"{r['instr'] / base:.2f}×" if ok(r) and base else "—"


L = []
A = L.append

A("# PERF.md — the lech performance battery")
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
  f"`ulimit -v {meta.get('vlimit', '?')}`, `timeout {meta.get('timeout', '?')}`, `nice -n 5` |")
A("| streams | preprocessed once off the clock by `lean-inductive-models`; "
  "both checkers read the same bytes, lech under `--pre` |")
if meta.get("loadnote"):
    A(f"| concurrent load | {meta['loadnote']} |")
A(f"| official kernel | `{meta.get('official', '?')}` |")
A(f"| preprocessor | `{meta.get('preproc', '?')}` |")
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

A("## exit code / accepted declarations")
A("")
A("| stream | " + " | ".join(LABELS[c] for c in live) + " |")
A("|" + "---|" * (len(live) + 1))
for s in stream_order:
    row = []
    for c in live:
        r = cells[s].get(c)
        row.append("—" if r is None else f"{r['exit']} / {r['decls'] or '?'}")
    A(f"| `{s}` | " + " | ".join(row) + " |")
A("")
A("Exit codes: 0 accept, 1 reject, 2 decline, 3 error.")
A("")

A("## Notes")
A("")
if meta.get("stalenote"):
    A(f"* {meta['stalenote']}")
A("* **Cross-pipeline, not same-work.**  Both sides read the same bytes,")
A("  but every lech cell checks a *modeled* encoding of the inductive")
A("  blocks plus an `annotate` pass with no official counterpart, while")
A("  official checks that file with native inductive/recursor support.")
A("  Hence the accepted-declaration counts differ too.")
A("* **`--trusted` under-checks install-only kinds** (axioms, inductive")
A("  blocks, quot, the pinned-cert branches run at io grade), which")
A("  flatters the trusted column on inductive-heavy streams.")
A("* One run per cell on a shared machine: `instructions:u` is")
A("  contention-independent, so a cell may overlap other work; wall time")
A("  is not reported for that reason.")
A("* Regenerate with `lake build lech && scripts/perf-tables.sh`;")
A("  `--render` re-renders from `perf-data/` without measuring, and")
A("  `PERF_STREAMS=… PERF_APPEND=1` re-runs a single stream.  Raw cells")
A("  (with wall time and load, recorded but not printed) are tracked in")
A("  `perf-data/table.tsv`, provenance in `perf-data/meta.txt`.")
A("")

open(out_path, "w").write("\n".join(L) + "\n")
print(f"rendered {out_path} ({len(stream_order)} streams, {len(live)} columns)")
