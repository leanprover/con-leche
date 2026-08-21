#!/usr/bin/env python3
"""Extract, from a lean4export 3.x ndjson stream, the set of constant
names declared *before* Nat.mod resp. Nat.div — the allowlists the
GenDivModPins generator checks the pinned expressions and certificate
proofs against (a pin may only mention constants that exist in the
stream when the pinned operation is installed).

Usage: extract_divmod_prefix.py <stream.ndjson> <out.json>
"""
import json
import sys


def main(stream_path: str, out_path: str) -> None:
    names = {0: ""}
    declared: list[str] = []
    prefixes: dict[str, list[str]] = {}
    targets = {"Nat.mod", "Nat.div"}

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

    missing = targets - set(prefixes)
    if missing:
        sys.exit(f"targets not found in stream: {missing}")
    with open(out_path, "w") as f:
        json.dump(prefixes, f, indent=0, sort_keys=True)
    for t in sorted(prefixes):
        print(f"{t}: {len(prefixes[t])} names in prefix")


if __name__ == "__main__":
    main(sys.argv[1], sys.argv[2])
