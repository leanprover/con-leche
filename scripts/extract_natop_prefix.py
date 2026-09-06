#!/usr/bin/env python3
"""Extract, from lean4export 3.x ndjson streams, the set of constant
names declared *before* each pin-certified Nat operation — the
allowlists the elab-time pin generator (Setlec/PinGen.lean) checks the
pinned expressions against (a pin may only mention constants that
exist in the stream when the pinned operation is installed).  Since
task #113 the allowlists apply to the *pins* only: the certificate
proofs are closed over the operation's own dependency cone instead
(self-contained, valid for dependency-sliced streams too).

Multiple streams may be given; for an operation occurring in several
streams the prefixes are intersected (the allowlist must be valid for
every supported stream).  An operation missing from all streams is an
error.

Usage: extract_natop_prefix.py <out.json> <stream.ndjson>...
"""
import json
import sys

TARGETS = [
    "Nat.div", "Nat.mod", "Nat.gcd", "Nat.land", "Nat.lor", "Nat.xor",
    "Nat.shiftLeft", "Nat.shiftRight",
]


def stream_prefixes(stream_path: str) -> dict[str, list[str]]:
    names = {0: ""}
    declared: list[str] = []
    prefixes: dict[str, list[str]] = {}
    targets = set(TARGETS)

    def name(i: int) -> str:
        return names[i]

    with open(stream_path) as f:
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
            # declaration records
            new: list[str] = []
            if "def" in r or "thm" in r or "opaque" in r or "axiom" in r:
                kind = next(k for k in ("def", "thm", "opaque", "axiom") if k in r)
                new.append(name(r[kind]["name"]))
            elif "inductive" in r:
                b = r["inductive"]
                for t in b["types"]:
                    new.append(name(t["name"]))
                for c in b["ctors"]:
                    new.append(name(c["name"]))
                for rec in b["recs"]:
                    new.append(name(rec["name"]))
            elif "quot" in r:
                new.append(name(r["quot"]["name"]))
            for n in new:
                if n in targets and n not in prefixes:
                    prefixes[n] = list(declared)
                declared.append(n)
    return prefixes


def main(out_path: str, stream_paths: list[str]) -> None:
    merged: dict[str, list[str]] = {}
    for sp in stream_paths:
        prefixes = stream_prefixes(sp)
        print(f"{sp}:")
        for t in TARGETS:
            if t in prefixes:
                print(f"  {t}: {len(prefixes[t])} names in prefix")
        for t, pre in prefixes.items():
            if t in merged:
                keep = set(pre)
                merged[t] = [n for n in merged[t] if n in keep]
            else:
                merged[t] = pre
    missing = set(TARGETS) - set(merged)
    if missing:
        sys.exit(f"targets not found in any stream: {sorted(missing)}")
    with open(out_path, "w") as f:
        json.dump(merged, f, indent=0, sort_keys=True)
    print("merged:")
    for t in TARGETS:
        print(f"  {t}: {len(merged[t])} names in prefix")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2:])
