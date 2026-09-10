#!/usr/bin/env python3
"""Diff the generated Nat-op pin/proof constants against the
declared-before-op prefix of a stream — the diagnosis for a "pin
ground constants absent" decline (DESIGN.md, "Prefix allowlists vs.
stream order").  The op's self-reference always shows as "missing":
the install gate substitutes it away before `constsResolve`, so it is
a false positive.

Usage:
  lake env lean scripts/DumpNatOpPinConsts.lean > pinconsts.txt
  scripts/diagnose_natop_prefix.py <stream.ndjson> pinconsts.txt
"""
import json, sys

stream = sys.argv[1]
pinconsts = sys.argv[2]
targets = ["Nat.div", "Nat.mod", "Nat.gcd", "Nat.land", "Nat.lor", "Nat.xor",
           "Nat.shiftLeft", "Nat.shiftRight"]

# parse pinconsts.txt into {variant: {op: {"pin": set, "proofs": set}}}
# (section headers are `== <toolchain> <op> <kind>`)
variants = {}
cur = None
for line in open(pinconsts):
    line = line.strip()
    if line.startswith("== "):
        _, tc, op, kind = line.split()
        cur = variants.setdefault(tc, {}).setdefault(op, {}).setdefault(kind, set())
    elif line and cur is not None:
        cur.add(line)

# the stream's declared-before-op prefixes, once
positions = {}
prefix_sets = {}

names = {0: ""}
declared = set()
remaining = set(t for t in targets if any(t in ops for ops in variants.values()))

with open(stream) as f:
    for line in f:
        r = json.loads(line)
        if "meta" in r:
            continue
        if "in" in r:
            i = r["in"]
            if "str" in r:
                p = names[r["str"]["pre"]]
                names[i] = (p + "." if p else "") + r["str"]["str"]
            elif "num" in r:
                p = names[r["num"]["pre"]]
                names[i] = (p + "." if p else "") + str(r["num"]["i"])
            continue
        if "il" in r or "ie" in r:
            continue
        new = []
        if any(k in r for k in ("def", "thm", "opaque", "axiom")):
            kind = next(k for k in ("def", "thm", "opaque", "axiom") if k in r)
            new.append(names[r[kind]["name"]])
        elif "inductive" in r:
            b = r["inductive"]
            for t in b["types"]:
                new.append(names[t["name"]])
            for c in b["ctors"]:
                new.append(names[c["name"]])
            for rec in b.get("recs", []):
                new.append(names[rec["name"]])
        elif "quot" in r:
            new.append(names[r["quot"]["name"]])
        for n in new:
            if n in remaining:
                remaining.discard(n)
                positions[n] = len(declared)
                prefix_sets[n] = set(declared)
        declared.update(new)
        # recursors: streams declare Foo.rec implicitly with inductives
        if not remaining:
            break

for tc, opsets in variants.items():
    print(f"variant {tc}:")
    for op in targets:
        if op not in opsets:
            continue
        if op not in positions:
            print(f"  {op}: NOT REACHED in stream")
            continue
        s = opsets[op]
        mp = sorted(s.get("pin", set()) - prefix_sets[op])
        mf = sorted(s.get("proofs", set()) - prefix_sets[op])
        print(f"  {op} (at ~{positions[op]} decls): missing-in-pin={len(mp)} missing-in-proofs={len(mf)}")
        for n in mp:
            print(f"    PIN   {n}")
        for n in mf:
            print(f"    PROOF {n}")
