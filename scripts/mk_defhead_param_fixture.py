#!/usr/bin/env python3
"""Derive tests/e2e/ind_defhead_param_bad.ndjson from ind_defhead_param_base.ndjson: the former `K`
stored at the constant `Two`, whose definition is its telescope, parameters included.

Usage: scripts/mk_defhead_param_fixture.py [base.ndjson] [out.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/ind_defhead_param_base.ndjson"
dst = sys.argv[2] if len(sys.argv) > 2 else "tests/e2e/ind_defhead_param_bad.ndjson"
lines = open(src).read().splitlines()
recs = [json.loads(l) for l in lines]


def nid(s):
    for r in recs:
        if "in" in r and "str" in r and r["str"] == {"pre": 0, "str": s}:
            return r["in"]
    raise SystemExit(f"no name {s}")


two, k = nid("Two"), nid("K")
fresh = max(r["ie"] for r in recs if "ie" in r) + 1
blocks = [r for r in recs if "inductive" in r and r["inductive"]["types"][0]["name"] == k]
if len(blocks) != 1:
    raise SystemExit("no block K")
# the block moves to the end of the stream: `Two` is exported after it
block = blocks[0]
block["inductive"]["types"][0]["type"] = fresh
out = [r for r in recs if r is not block] + [{"ie": fresh, "const": {"name": two, "us": []}}, block]
open(dst, "w").write("\n".join(json.dumps(r) for r in out) + "\n")
