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
           "Nat.shiftLeft", "Nat.shiftRight", "Nat.log2"]

# parse pinconsts.txt into {op: {"pin": set, "proofs": set}}
opsets = {}
cur = None
for line in open(pinconsts):
    line = line.strip()
    if line.startswith("== "):
        _, op, kind = line.split()
        cur = opsets.setdefault(op, {}).setdefault(kind, set())
    elif line and cur is not None:
        cur.add(line)

names = {0: ""}
declared = set()
prefixes = {}
remaining = set(t for t in targets if t in opsets)

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
                s = opsets[n]
                missing_pin = sorted(s.get("pin", set()) - declared)
                missing_prf = sorted(s.get("proofs", set()) - declared)
                prefixes[n] = (len(declared), missing_pin, missing_prf)
        declared.update(new)
        # recursors: streams declare Foo.rec implicitly with inductives
        if not remaining:
            break

for op in targets:
    if op not in prefixes:
        print(f"{op}: NOT REACHED in stream")
        continue
    pos, mp, mf = prefixes[op]
    print(f"{op} (at ~{pos} decls): missing-in-pin={len(mp)} missing-in-proofs={len(mf)}")
    for n in mp:
        print(f"  PIN   {n}")
    for n in mf:
        print(f"  PROOF {n}")
