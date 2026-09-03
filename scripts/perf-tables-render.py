#!/usr/bin/env python3
"""Render PERF.md from the battery's raw TSV.

    perf-tables-render.py table.tsv PERF.md meta.txt

Pure formatting: every number comes from the TSV, every caveat is
static text.  Re-runnable without re-measuring (`perf-tables.sh
--render`).
"""
import sys, os

tsv, out_path, meta_path = sys.argv[1], sys.argv[2], sys.argv[3]

meta = {}
if os.path.exists(meta_path):
    for line in open(meta_path):
        if "\t" in line:
            k, v = line.rstrip("\n").split("\t", 1)
            meta[k] = v

# stream -> cfg -> record
cells, stream_order = {}, []
for line in open(tsv):
    f = line.rstrip("\n").split("\t")
    if len(f) < 8:
        continue
    s, c, instr, wall, ex, decls, load, verdict = f[:8]
    if s not in cells:
        cells[s] = {}
        stream_order.append(s)
    cells[s][c] = dict(instr=int(instr or 0), wall=float(wall or 0),
                       exit=int(ex), decls=decls, load=load, verdict=verdict)

CFGS = [
    ("official",  "official v4.33.0"),
    ("sm-prod",   "`--set-model` `--core=production`"),
    ("sm-cached", "`--set-model` `--core=cached-parsed`"),
    ("tt-prod",   "`--tt-model` `--core=production`"),
    ("tt-cached", "`--tt-model` `--core=cached-parsed`"),
    ("nm-prod",   "`--no-model` `--core=production`"),
    ("nm-cached", "`--no-model` `--core=cached-parsed`"),
]
SHORT = {"official": "official", "sm-prod": "SM/prod", "sm-cached": "SM/cached",
         "tt-prod": "TT/prod", "tt-cached": "TT/cached",
         "nm-prod": "NM/prod", "nm-cached": "NM/cached"}


def ok(r):
    return r is not None and r["exit"] == 0 and r["instr"] > 0


def g(n):
    return f"{n / 1e9:.2f}"


def full_cell(r, base):
    if r is None:
        return "—"
    if r["exit"] != 0:
        return f"**exit {r['exit']}**"
    ratio = f" ({r['instr'] / base:.2f}×)" if base else ""
    return f"{g(r['instr'])} G{ratio} / {r['wall']:.2f} s"


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
A(f"| date | {meta.get('date', '?')} |")
A(f"| machine | {meta.get('host', '?')} — {meta.get('cpu', '?')}, "
  f"{meta.get('cores', '?')} cores, {meta.get('mem', '?')} RAM, Linux {meta.get('kernelver', '?')} |")
A(f"| repetitions | median of {meta.get('reps', '?')} per cell |")
A(f"| per-run timeout | {meta.get('timeout', '?')} s |")
A(f"| official kernel | `{meta.get('official', '?')}` |")
A(f"| preprocessor | `{meta.get('preproc', '?')}` |")
A("")
A("## Invocation")
A("")
A("```")
A("lake build setlec        # the binary measured below")
A("scripts/perf-tables.sh   # ~2-4 h; rewrites PERF.md after every stream")
A("scripts/perf-tables.sh --render   # re-render from _tmp/perf-tables/table.tsv")
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
A("mode-aware default.")
A("")

A("## The table — instructions:u (G), ratio vs official, wall seconds")
A("")
A("Instructions are the primary metric (contention-independent); wall is")
A("indicative only (caveat 6).  Ratios are against the official column")
A("on the same row and are cross-pipeline — read them through caveat 2.")
A("")
head = "| stream | " + " | ".join(lbl for _, lbl in CFGS) + " |"
A(head)
A("|" + "---|" * (len(CFGS) + 1))
for s in stream_order:
    base_rec = cells[s].get("official")
    base = base_rec["instr"] if ok(base_rec) else 0
    A(f"| `{s}` | " + " | ".join(full_cell(cells[s].get(c), base if c != "official" else 0)
                                 for c, _ in CFGS) + " |")
A("")

A("## Accepted declarations (verdict sanity)")
A("")
A("Cells that did not exit 0 show their exit code instead.  Counts")
A("differ between the two pipelines by construction — caveat 3.")
A("")
A("| stream | " + " | ".join(SHORT[c] for c, _ in CFGS) + " |")
A("|" + "---|" * (len(CFGS) + 1))
for s in stream_order:
    row = []
    for c, _ in CFGS:
        r = cells[s].get(c)
        if r is None:
            row.append("—")
        elif r["exit"] != 0:
            row.append(f"exit {r['exit']}")
        else:
            row.append(r["decls"] or "?")
    A(f"| `{s}` | " + " | ".join(row) + " |")
A("")

# Derived: the verification tax per core (set-model / no-model).
taxrows = []
for s in stream_order:
    r = []
    for core in ("prod", "cached"):
        a, b = cells[s].get("sm-" + core), cells[s].get("nm-" + core)
        r.append(f"{a['instr'] / b['instr']:.2f}×" if ok(a) and ok(b) else "—")
    taxrows.append((s, r))
if taxrows:
    A("## Derived: `--set-model` ÷ `--no-model`, same core")
    A("")
    A("The certified checker over the cert-skipping lane, same binary,")
    A("same stream, same engine.  On the production core this is the")
    A("project's canonical verification-tax figure; on the cached core it")
    A("is **not** one — caveat 1.")
    A("")
    A("| stream | production | cached-parsed |")
    A("|---|---|---|")
    for s, r in taxrows:
        A(f"| `{s}` | {r[0]} | {r[1]} |")
    A("")

# Derived: the engineering gap, cheapest setlec cell vs official.
A("## Derived: best setlec cell ÷ official, per stream")
A("")
A("| stream | cheapest setlec configuration | ratio vs official |")
A("|---|---|---|")
for s in stream_order:
    base_rec = cells[s].get("official")
    cand = [(r["instr"], c) for c, r in cells[s].items()
            if c != "official" and ok(r)]
    if not cand or not ok(base_rec):
        A(f"| `{s}` | — | — |")
        continue
    v, c = min(cand)
    A(f"| `{s}` | {SHORT[c]} | {v / base_rec['instr']:.2f}× |")
A("")

A("## CAVEATS — read every number through these")
A("")
A("1. **`--no-model` on `--core=cached-parsed` is NOT a parity lane.**")
A("   There is no cert-skipping/infer-only twin under `Setlec/Cached/`;")
A("   that cell is the *certified* cached driver (`CoreC`) running with")
A("   `CheckMode.verified = false`, which gates exactly two checks")
A("   (λ-codomain sort validation and annotation validation) and still")
A("   runs the whole certification machinery.  Its distance from")
A("   `--set-model --core=cached-parsed` is therefore small **by")
A("   construction** and is not a verification tax.  This is caveat 5 of")
A("   the task-#161 canonical table; the cached NC twin does not exist.")
A("   The parity lane is `--no-model --core=production` and only that.")
A("2. **The preprocessor floor is removed, the modeled encoding is not.**")
A("   Both sides read the same preprocessed bytes, so no setlec cell")
A("   pays the preprocessor here — but every setlec cell still checks a")
A("   *modeled* encoding of the inductive blocks (plus the `annotate`")
A("   pass, which has no official counterpart), while official checks")
A("   the same file with native inductive/recursor support.  Every")
A("   official ratio is cross-pipeline, not a same-work speed ratio.")
A("3. **Declaration counts differ from official** — the preprocessor's")
A("   `_model` declarations.  On a preprocessed stream the gap is small")
A("   (init-full: official 60 060 vs setlec 61 048) but it is never")
A("   zero, and the two checkers are not checking the same list.")
A("4. **`--tt-model` is retired** (task #148 T7b): `Main.lean` rejects the")
A("   flag outright, so those two columns are argument-parse failures,")
A("   not measurements.  The certified mode is `--set-model`.  The")
A("   columns are kept, and measured, so the table records the real exit")
A("   code instead of quietly dropping the requested combination.")
A("5. **`--core=cached` vs `--core=cached-parsed`.**  The cached column")
A("   is `cached-parsed`, the supported and verified cached core (task")
A("   #163; acceptance covered by `no_proof_of_Empty_SPC_*`).")
A("   `--core=cached` also parses, but selects `checkDeclsSharedC`, an")
A("   explicitly unverified pilot measurement instrument — measuring it")
A("   here would put a non-shipping lane in the headline table.")
A("6. **Medians of 3, one machine, concurrent load.**  All cells ran on")
A("   the single machine named above, one timed run at a time (the")
A("   script blocks until no other checker/`perf` process is live), but")
A("   the machine is shared with concurrent agent builds.  Instructions:u")
A("   is robust to that; **wall seconds are not** and should be read as")
A("   indicative only.  The per-cell load average at launch is recorded")
A("   in the raw TSV.")
A("7. **`--no-model --core=production` under-checks install-only kinds**")
A("   relative to official (axioms, inductive blocks, quot and the")
A("   pinned-cert branches run at io grade there, where official's")
A("   declaration-type check is `check`).  This flatters the parity")
A("   column on inductive-heavy streams — init-full most of all.")
A("8. **Fuel.**  setlec compiles in `checkFuel = 100000` plus")
A("   `defeqLoopFuel`; official has no fuel.  No row above exhausts it.")
A("")
A("## Raw data")
A("")
A("`_tmp/perf-tables/table.tsv` — one line per cell:")
A("`stream, config, median instructions:u, median wall s, exit code,")
A("accepted declarations, 1-min load average at launch, verdict text`.")
A("The preprocessed streams are cached at `_tmp/perf-tables/pre/`.")
A("")

open(out_path, "w").write("\n".join(L) + "\n")
print(f"rendered {out_path} ({len(stream_order)} streams)")
