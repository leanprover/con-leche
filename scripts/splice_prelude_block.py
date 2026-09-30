#!/usr/bin/env python3
"""Splice one inductive block of a lean4export prelude into a stream.

    scripts/splice_prelude_block.py <prelude.ndjson> <NAME> <in.ndjson> <out.ndjson>

Copies every table line (`in`/`il`/`ie`) of <prelude.ndjson> that
precedes the `inductive` record declaring NAME, and that record, to the
front of <in.ndjson> (right after its meta line), with every name,
level and expression index moved past the stream's own (the parser
takes sparse indices, `ConLeche/Frontend/Export.lean`).  Unused table
entries are harmless; no other declaration of the prelude is copied.

What it is for (lane PUNIT, 2026-09-29): `PUnit` left the built-in
prelude when it stopped being a pinned basis block, so a forged fixture
that USES `PUnit` without declaring it (the `nested_pin_collide*_nomodel`
twins: their spliced `_model` records mention it) now declares it
itself, from the pre-PUNIT prelude (`git show 2753fe664:pins/leanprover-lean4-v4.33.0.prelude.ndjson`).
"""
import json
import sys

NAME_KEYS = {"in", "pre", "name", "induct", "ctor", "typeName", "param"}
NAME_LIST_KEYS = {"all", "ctors", "levelParams"}
LEVEL_KEYS = {"il", "sort"}
LEVEL_LIST_KEYS = {"max", "imax", "us"}
EXPR_KEYS = {"ie", "type", "body", "value", "fn", "arg", "rhs", "struct"}


def shift(obj, on, ol, oe):
    nm = lambda i: i if i == 0 else i + on
    lv = lambda i: i if i == 0 else i + ol
    if isinstance(obj, list):
        return [shift(x, on, ol, oe) for x in obj]
    if not isinstance(obj, dict):
        return obj
    out = {}
    for k, v in obj.items():
        if k in NAME_KEYS and isinstance(v, int):
            out[k] = nm(v)
        elif k in NAME_LIST_KEYS and isinstance(v, list) and all(isinstance(x, int) for x in v):
            out[k] = [nm(x) for x in v]
        elif k in LEVEL_KEYS and isinstance(v, int):
            out[k] = lv(v)
        elif k == "succ" and isinstance(v, int):
            out[k] = lv(v)
        elif k in LEVEL_LIST_KEYS and isinstance(v, list):
            out[k] = [lv(x) for x in v]
        elif k in EXPR_KEYS and isinstance(v, int):
            out[k] = v + oe
        else:
            out[k] = shift(v, on, ol, oe)
    return out


def main() -> int:
    if len(sys.argv) != 5:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    prelude, name, src, dst = sys.argv[1:]
    plines = [json.loads(l) for l in open(prelude, encoding="utf-8") if l.strip()]
    names = {}
    for r in plines:
        if "in" in r:
            s = r.get("str") or {}
            pre = names.get(s.get("pre"), "") if s.get("pre") else ""
            names[r["in"]] = (pre + "." if pre else "") + s.get("str", "")
    slines = open(src, encoding="utf-8").read().splitlines()
    srecs = [json.loads(l) for l in slines[1:] if l.strip()]
    on = max([r["in"] for r in srecs if "in" in r] + [0]) + 1
    ol = max([r["il"] for r in srecs if "il" in r] + [0]) + 1
    oe = max([r["ie"] for r in srecs if "ie" in r] + [0]) + 1
    picked = []
    for r in plines[1:]:
        if any(k in r for k in ("in", "il", "ie")):
            picked.append(r)
            continue
        ind = r.get("inductive")
        if ind and any(names.get(t["name"]) == name for t in ind["types"]):
            picked.append(r)
            break
    else:
        print(f"no inductive record declares {name}", file=sys.stderr)
        return 1
    with open(dst, "w", encoding="utf-8") as f:
        f.write(slines[0] + "\n")
        for r in picked:
            f.write(json.dumps(shift(r, on, ol, oe), ensure_ascii=False, separators=(",", ":")) + "\n")
        for l in slines[1:]:
            f.write(l + "\n")
    return 0


if __name__ == "__main__":
    sys.exit(main())
