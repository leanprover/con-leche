#!/usr/bin/env python3
"""scripts/plain-reach.py — which plain-tier definitions the shipped binary runs (task #497).

The plain tier (`ConLeche/Kernel/*`, and any other module of ours outside
`ConLeche/Cached/*`, `ConLeche/Driver/*` and `Main`) is the specification the
proofs are about.  The binary may run a plain definition only where it is the
best code there is; everywhere else the cached tier has a twin.  This script
lists every plain-tier source declaration reached from `main` in the compiled
IR (`scripts/executed-decls.lean --edges`: `@[csimp]`, `@[implemented_by]` and
specializations already resolved), with

  * `rec`     — the declaration calls itself, or sits on a cycle of plain
                declarations (a walk or a loop);
  * `entries` — the cached-tier declarations (`Cached/*`, `Driver/*`, `Main`)
                from which it is reached through plain declarations only.

Usage:

    scripts/plain-reach.py [--edges FILE] [--allow FILE] [--frontend]

`--edges FILE` reads a saved edge list instead of running the Lean script.
`--frontend` includes `ConLeche/Frontend/*` (the input reader, which has no
cached twin by design: it is the only implementation) in the listing.
`--allow FILE` turns the listing into a gate: every reached plain declaration
must be named in FILE (one name per line, `#` comments, an optional
`<name>  # reason`; `module:<M>` admits every declaration of module `M`,
for generated data such as the Nat-op pins); a reached name missing from FILE, or a name in FILE
that is no longer reached, fails with exit 1.
"""
import os
import re
import subprocess
import sys
from collections import defaultdict

ROOT = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..")


def tier(mod):
    if mod == "Main" or mod.startswith("ConLeche.Cached.") or mod.startswith("ConLeche.Driver."):
        return "cached"
    if mod.startswith("ConLeche.Frontend."):
        return "frontend"
    if mod == "ConLeche" or mod.startswith("ConLeche."):
        return "plain"
    return "external"


CLOSED = re.compile(r"(\._closed_\d+)+$")


def read_edges(path):
    if path:
        text = open(path).read()
    else:
        r = subprocess.run(["lake", "env", "lean", "--run", "scripts/executed-decls.lean", "--edges"],
                           cwd=ROOT, capture_output=True, text=True)
        if r.returncode != 0:
            sys.exit(f"plain-reach: executed-decls failed (exit {r.returncode}):\n{r.stderr}")
        text = r.stdout
    edges = []
    for line in text.splitlines():
        parts = line.split("\t")
        if len(parts) == 6:
            # a generated declaration without ranges (an elaboration-time
            # splice's closed terms) stands for its parent
            parts[1] = CLOSED.sub("", parts[1])
            parts[4] = CLOSED.sub("", parts[4])
            edges.append(tuple(parts))
    return edges


def main(argv):
    edges_path = None
    allow_path = None
    frontend = False
    i = 0
    while i < len(argv):
        a = argv[i]
        if a == "--edges":
            edges_path = argv[i + 1]
            i += 2
        elif a == "--allow":
            allow_path = argv[i + 1]
            i += 2
        elif a == "--frontend":
            frontend = True
            i += 1
        else:
            sys.exit(__doc__)
    edges = read_edges(edges_path)
    mod = {}
    succ = defaultdict(set)
    pred = defaultdict(set)
    ir_succ = defaultdict(set)
    ir_src = {}
    for fi, fs, fm, ti, ts, tm in edges:
        mod.setdefault(fs, fm)
        mod.setdefault(ts, tm)
        ir_src[fi] = fs
        ir_src[ti] = ts
        ir_succ[fi].add(ti)
        if fs != ts:
            succ[fs].add(ts)
            pred[ts].add(fs)
    want = {"plain", "frontend"} if frontend else {"plain"}
    plain = {n for n, m in mod.items() if tier(m) in want}
    # a plain declaration is recursive (a walk or a loop) if one of its IR
    # declarations can reach itself through IR declarations of plain ones
    rec = set()
    plain_ir = {i for i, s in ir_src.items() if s in plain}
    for i in plain_ir:
        if ir_src[i] in rec:
            continue
        stack = [t for t in ir_succ[i] if t in plain_ir]
        seen = set()
        while stack:
            t = stack.pop()
            if t == i:
                rec.add(ir_src[i])
                break
            if t in seen:
                continue
            seen.add(t)
            stack.extend(u for u in ir_succ[t] if u in plain_ir)
    # the cached entries reaching each plain declaration through plain ones
    entries = {}
    for n in plain:
        out = set()
        stack = [n]
        seen = {n}
        while stack:
            t = stack.pop()
            for p in pred[t]:
                tp = tier(mod[p])
                if tp == "cached":
                    out.add(p)
                elif p in plain and p not in seen:
                    seen.add(p)
                    stack.append(p)
        entries[n] = out
    rows = sorted(plain, key=lambda n: (mod[n], n))
    if allow_path is None:
        for n in rows:
            e = sorted(entries[n])
            print(f"{n}\t{mod[n]}\t{'rec' if n in rec else '-'}\t{len(e)}\t{' '.join(e[:6])}{' …' if len(e) > 6 else ''}")
        print(f"plain-reach: {len(rows)} plain declarations reached, {len(rec)} recursive", file=sys.stderr)
        return 0
    allowed = set()
    allowed_mods = set()
    for line in open(allow_path):
        name = line.split("#", 1)[0].strip()
        if name.startswith("module:"):
            allowed_mods.add(name[len("module:"):])
        elif name:
            allowed.add(name)
    bad = [n for n in rows if n not in allowed and mod[n] not in allowed_mods]
    stale = sorted((allowed - plain) |
                   {"module:" + m for m in allowed_mods if not any(mod[n] == m for n in plain)})
    for n in bad:
        print(f"plain-reach: NOT ALLOWED: {n} ({mod[n]}{', rec' if n in rec else ''}) "
              f"reached from {' '.join(sorted(entries[n])[:4])}")
    for n in stale:
        print(f"plain-reach: STALE allowlist entry (no longer reached): {n}")
    if bad or stale:
        return 1
    print(f"plain-reach: {len(rows)} plain declarations reached, all allowlisted")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
