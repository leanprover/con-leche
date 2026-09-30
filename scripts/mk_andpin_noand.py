#!/usr/bin/env python3
"""Drop a lean4export ndjson stream's `And` block record, leaving every
use of `And` in place.

    scripts/mk_andpin_noand.py <in.ndjson> <out.ndjson>

The stream then USES `And`, `And.intro` and `And.rec` without declaring
them — no Lean export looks like this, since an export declares every
constant it mentions.  The checker's built-in prelude carries the
toolchain's `And` block (`pinnedPreludeMembers`,
`ConLeche/PinGen/Prelude.lean`) and `preparePrelude` puts it at the
front of the records, so the uses resolve to the pinned `And` and the
stuck-proof rescue serves them.  `tests/e2e/and_rec_opaque_noand.ndjson`
is `tests/e2e/and_rec_opaque.ndjson` through this script.
"""
import json
import sys


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    src, out = sys.argv[1], sys.argv[2]
    names = {0: ""}
    kept: list[str] = []
    dropped = 0
    with open(src) as f:
        for raw in f:
            line = raw.rstrip("\n")
            if not line.strip():
                continue
            r = json.loads(line)
            if "in" in r:
                i = r["in"]
                if "str" in r:
                    p = names[r["str"]["pre"]]
                    names[i] = (p + "." if p else "") + r["str"]["str"]
                else:
                    p = names[r["num"]["pre"]]
                    names[i] = (p + "." if p else "") + str(r["num"]["i"])
            elif "inductive" in r:
                if any(names.get(t["name"]) == "And" for t in r["inductive"]["types"]):
                    dropped += 1
                    continue
            kept.append(line)
    if dropped != 1:
        print(f"expected one `And` block record, found {dropped}", file=sys.stderr)
        return 3
    with open(out, "w") as f:
        f.write("\n".join(kept) + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
