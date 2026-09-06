#!/usr/bin/env python3
"""Perturb a lean4export ndjson stream's `Bool` block into a DIFFERENT
but valid inductive: `Bool : Type 1` instead of `Bool : Type`.

    scripts/mk_prelude_bool_bad.py <in.ndjson> <out.ndjson>

The `Bool` type former's `type` field is re-pointed at a fresh
`Sort 2` expression entry (a fresh `succ` level entry over the stream's
`succ 0`); constructors, recursor and every use are untouched, so the
stream is still a well-formed export of a well-formed inductive (a
two-constructor enumeration in `Type 1`) — the official kernel accepts
it.  The checker's built-in prelude (task #191) installs the
toolchain's own `Bool : Type` first, and a later stream `Bool` is
compared with it: this one differs, so the run DECLINES (exit 2,
naming `Bool`).  `tests/e2e/prelude_bool_redefined.ndjson` is
`tests/e2e/natop_order.ndjson` through this script.
"""
import json
import sys


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    src, out = sys.argv[1], sys.argv[2]
    names = {0: ""}
    lines: list[str] = []
    max_il = 0
    max_ie = 0
    succ0: int | None = None
    bool_idx: int | None = None
    with open(src) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if not line.strip():
                continue
            lines.append(line)
            r = json.loads(line)
            if "in" in r:
                i = r["in"]
                if "str" in r:
                    p = names[r["str"]["pre"]]
                    names[i] = (p + "." if p else "") + r["str"]["str"]
                else:
                    p = names[r["num"]["pre"]]
                    names[i] = (p + "." if p else "") + str(r["num"]["i"])
                if names[i] == "Bool":
                    bool_idx = i
            elif "il" in r:
                max_il = max(max_il, r["il"])
                if r.get("succ") == 0 and succ0 is None:
                    succ0 = r["il"]
            elif "ie" in r:
                max_ie = max(max_ie, r["ie"])
    if bool_idx is None or succ0 is None:
        print("no Bool block / no `succ 0` level in the stream", file=sys.stderr)
        return 3
    lvl2 = max_il + 1
    sort2 = max_ie + 1
    patched = False
    with open(out, "w") as f:
        for line in lines:
            r = json.loads(line)
            if "inductive" in r and not patched:
                types = r["inductive"]["types"]
                for t in types:
                    if t["name"] == bool_idx:
                        f.write(json.dumps({"il": lvl2, "succ": succ0},
                                           separators=(",", ":")) + "\n")
                        f.write(json.dumps({"ie": sort2, "sort": lvl2},
                                           separators=(",", ":")) + "\n")
                        t["type"] = sort2
                        patched = True
                        line = json.dumps(r, separators=(",", ":"))
            f.write(line + "\n")
    if not patched:
        print("the Bool inductive record was not found", file=sys.stderr)
        return 3
    print(f"{out}: Bool : Type 1", file=sys.stderr)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
