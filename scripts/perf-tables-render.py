#!/usr/bin/env python3
"""Render PERF.md from the battery's tracked record.

    perf-tables-render.py table.tsv PERF.md meta.txt

Pure formatting: every number comes from `table.tsv` (the battery's
cells), `parallel.tsv` beside it (the worker-count sweep) and the
hand-written notes in `meta.txt`.  Two columns, official and con-leche
(`--verified`, the shipped mode); instructions are the measurement, wall
time and memory appear only as labelled data.  Keep the prose short: the
file states the current numbers and nothing about earlier ones.
"""
import os
import sys

tsv, out_path, meta_path = sys.argv[1], sys.argv[2], sys.argv[3]
parallel_path = os.path.join(os.path.dirname(tsv), "parallel.tsv")


def read_meta(path):
    m = {}
    if os.path.exists(path):
        for line in open(path):
            if "\t" in line:
                k, v = line.rstrip("\n").split("\t", 1)
                m[k] = v
    return m


def read_cells(path):
    """Last row per (stream, config) wins: re-measured cells override."""
    cs, order = {}, []
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 8:
            continue
        s, c, instr, wall, ex, decls = f[:6]
        rss = f[8] if len(f) > 8 else ""
        if s not in cs:
            cs[s] = {}
            order.append(s)
        cs[s][c] = dict(instr=int(instr or 0), exit=int(ex), decls=decls,
                        wall=float(wall or 0), rss=int(rss) if rss else 0)
    return cs, order


def read_parallel(path):
    """(stream, jobs) -> (median, min, max) wall seconds."""
    rows, streams, jobs = {}, [], []
    if not os.path.exists(path):
        return rows, streams, jobs
    for line in open(path):
        f = line.rstrip("\n").split("\t")
        if len(f) < 5 or f[0] == "stream":
            continue
        s, j = f[0], int(f[1])
        rows[(s, j)] = tuple(float(x) for x in f[2:5])
        if s not in streams:
            streams.append(s)
        if j not in jobs:
            jobs.append(j)
    return rows, streams, sorted(jobs)


meta = read_meta(meta_path)
cells, streams = read_cells(tsv)
par, par_streams, par_jobs = read_parallel(parallel_path)
OFF = meta.get("officiallabel", "official")


def instr_text(r):
    """A cell that did not accept ran only a prefix of its stream: its
    count is not a measurement of the workload, and says so."""
    if r is None or not r["instr"]:
        return "—"
    n = r["instr"]
    t = f"{n / 1e12:.2f} T" if n >= 1e12 else f"{n / 1e9:.2f} G"
    return t if r["exit"] == 0 else f"({t}, exit {r['exit']})"


def secs(w):
    return f"{w / 60:.1f} min" if w >= 120 else f"{w:.0f} s"


L = []
A = L.append
A("# PERF.md — con-leche against the official kernel")
A("")
A(f"con-leche (`--verified`, its default mode) against the {OFF} kernel, "
  "on the same `lean4export` streams, read unchanged by both.  The "
  "measurement is `perf stat -e instructions:u`, one run per cell, with "
  "con-leche at `--jobs=1` to match the single-threaded official "
  "checker.  Wall time and memory appear only as data: the machine is "
  "shared.")
A("")
A("| | |")
A("|---|---|")
A(f"| con-leche | `{meta.get('sha', '?')}`"
  + (" (dirty tree)" if meta.get("dirty", "0") not in ("0", "") else "")
  + f", built with Lean {meta.get('toolchain', '?')} |")
A(f"| official | {meta.get('official', '?')} |")
A(f"| streams | {meta.get('streams', '?')} |")
A(f"| date | {meta.get('date', '?')[:10]} |")
A(f"| machine | {meta.get('cpu', '?')}, {meta.get('cores', '?')} cores, "
  f"{meta.get('mem', '?')} RAM |")
A("")

A("## Instructions, one worker")
A("")
A(f"| stream | {OFF} | con-leche | ratio | declarations ({OFF} / con-leche) |")
A("|---|---|---|---|---|")
for s in streams:
    o, v = cells[s].get("official"), cells[s].get("verified")
    ok = o and v and o["exit"] == 0 and v["exit"] == 0 and o["instr"]
    ratio = f"{v['instr'] / o['instr']:.2f}×" if ok else "—"
    counts = " / ".join((r["decls"] or "—") if r else "—" for r in (o, v))
    A(f"| `{s}` | {instr_text(o)} | {instr_text(v)} | {ratio} | {counts} |")
A("")

ml = cells.get("mathlib-full")
if ml and "official" in ml and "verified" in ml:
    A("## All of Mathlib: wall time and memory")
    A("")
    A(f"| | {OFF} | con-leche `--jobs=1` |")
    A("|---|---|---|")
    A(f"| wall | {secs(ml['official']['wall'])} | {secs(ml['verified']['wall'])} |")
    A(f"| peak RSS | {ml['official']['rss'] / 1048576:.2f} GiB | "
      f"{ml['verified']['rss'] / 1048576:.2f} GiB |")
    A("")

if par:
    A("## More than one worker")
    A("")
    A("At `--jobs=<n>` the parse, the install and the check run on `<n>` "
      "threads.  Wall time, median of five runs (min–max), `--verified`.")
    A("")
    A("| stream | " + " | ".join(f"`--jobs={j}`" for j in par_jobs) + " |")
    A("|" + "---|" * (1 + len(par_jobs)))
    for s in par_streams:
        row = []
        for j in par_jobs:
            m = par.get((s, j))
            if m is None:
                row.append("—")
            elif m[0] >= 120:
                row.append(f"{m[0] / 60:.1f} min ({m[1] / 60:.1f}–{m[2] / 60:.1f})")
            else:
                row.append(f"{m[0]:.1f} s ({m[1]:.1f}–{m[2]:.1f})")
        A(f"| `{s}` | " + " | ".join(row) + " |")
    A("")
    if meta.get("parallelnote"):
        A(meta["parallelnote"])
        A("")

A("## Notes")
A("")
for k in ("parsenote", "extranote"):
    if meta.get(k):
        A(f"* {meta[k]}")
A("* The declaration counts differ by counting, not by verdict: con-leche "
  "reports the declaration records in the file, official the size of its "
  "constant map (every constructor and recursor counted separately).  "
  "`scripts/stream-census.py` derives both from the file.")
A("* Regenerate: `lake build con-leche && scripts/perf-tables.sh` (the "
  "battery), `scripts/perf-tables.sh --parallel` (the worker-count sweep), "
  "`scripts/perf-tables.sh --render` (re-render from `perf-data/`).  The "
  "`mathlib-full` stream is exported by hand first; the recipe is in "
  "`scripts/perf-tables.sh`.")
A("")

open(out_path, "w").write("\n".join(L) + "\n")
print(f"rendered {out_path} ({len(streams)} streams)")
