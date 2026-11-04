#!/usr/bin/env python3
"""Fixtures for a recursor record read as it stands (task #480).

The install reads a recursor's K flag, its rules and its firing data off
the record; the block's job checks them.  Each stream is the smallest edit
of a committed good stream.  Official 1, target 1 for all of them.

  rec_record_k_off_bad         <- restrict_a37_myeq_k
      `MyEq.rec`, a K recursor, declares `k := false`.
  rec_record_k_on_nested_bad   <- corner_nestind_f13_listrose
      an auxiliary recursor declares `k := true`: an outside major's
      recursor is never K (the parser's own check skips nested blocks).
  rec_record_nfields_bad       <- nest_rose_tree
      a rule of the auxiliary recursor declares one field more than its
      constructor has.
  rec_record_ctor_numparams_bad <- restrict_a37_myeq_k
      the constructor's record declares one parameter more than the block
      has: the parameter count a rule fires at is the constructor's.

Usage: scripts/mk_rec_record_fixtures.py   (reads and writes under tests/e2e/)
"""
import copy
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load(src):
    p = os.path.join(ROOT, "tests/e2e", src + ".ndjson")
    return [json.loads(l) for l in open(p).read().splitlines()]


def dump(name, recs):
    p = os.path.join(ROOT, "tests/e2e", name + ".ndjson")
    with open(p, "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s: %d lines" % (name, len(recs)))


def ind(recs):
    """The stream's inductive records, last first (the block under test)."""
    return [r["inductive"] for r in reversed(recs) if "inductive" in r]


def last_with(recs, pred):
    for i in ind(recs):
        if pred(i):
            return i
    raise SystemExit("no such inductive record")


recs = load("restrict_a37_myeq_k")
out = copy.deepcopy(recs)
b = last_with(out, lambda i: any(r["k"] for r in i["recs"]))
b["recs"][0]["k"] = False
dump("rec_record_k_off_bad", out)

recs = load("corner_nestind_f13_listrose")
out = copy.deepcopy(recs)
b = last_with(out, lambda i: len(i["recs"]) > len(i["types"]))
b["recs"][-1]["k"] = True
dump("rec_record_k_on_nested_bad", out)

recs = load("nest_rose_tree")
out = copy.deepcopy(recs)
b = last_with(out, lambda i: len(i["recs"]) > len(i["types"]))
b["recs"][0]["rules"][-1]["nfields"] += 1
dump("rec_record_nfields_bad", out)

recs = load("restrict_a37_myeq_k")
out = copy.deepcopy(recs)
b = last_with(out, lambda i: any(r["k"] for r in i["recs"]))
b["ctors"][0]["numParams"] += 1
dump("rec_record_ctor_numparams_bad", out)
