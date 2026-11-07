#!/usr/bin/env python3
"""Derive the inductive-block defect fixtures (task #494) from
tests/e2e/corner_fuseloop_order_base.ndjson, whose one inductive block
`W.{u} (α : Sort u)` with constructor `W.mk` and recursor `W.rec` is
accepted.  Each variant changes one thing of that block, so that the
block can no longer be read as an inductive block, and pins the reason
the checker reports.  The official kernel rejects every one of them
except the last, which it accepts (it generates the recursor itself):

  block_no_type        — the block declares no inductive type.
  block_params_exceed  — `W` declares more parameters than its type
                         has binders (the constructor and the recursor
                         follow, so the decoder's count checks agree).
  block_ctor_params    — the constructor `W.mk` declares a different
                         parameter count than the block.
  block_ctor_levels    — `W.mk` declares no universe parameter, `W`
                         declares `u`.
  block_no_rec         — the block carries no recursor record.

Usage: scripts/mk_block_defect_fixtures.py [tests/e2e/corner_fuseloop_order_base.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/corner_fuseloop_order_base.ndjson"
recs = [json.loads(l) for l in open(src).read().splitlines()]


def emit(path, patch):
    out = []
    for r in recs:
        r = json.loads(json.dumps(r))
        if "inductive" in r:
            patch(r["inductive"])
        out.append(json.dumps(r))
    open(path, "w").write("\n".join(out) + "\n")


def no_type(ind):
    ind["types"] = []


def params_exceed(ind):
    for part in ("types", "ctors", "recs"):
        for x in ind[part]:
            x["numParams"] = 5


def ctor_params(ind):
    ind["ctors"][0]["numParams"] = 0


def ctor_levels(ind):
    ind["ctors"][0]["levelParams"] = []


def no_rec(ind):
    ind["recs"] = []


emit("tests/e2e/block_no_type.ndjson", no_type)
emit("tests/e2e/block_params_exceed.ndjson", params_exceed)
emit("tests/e2e/block_ctor_params.ndjson", ctor_params)
emit("tests/e2e/block_ctor_levels.ndjson", ctor_levels)
emit("tests/e2e/block_no_rec.ndjson", no_rec)
