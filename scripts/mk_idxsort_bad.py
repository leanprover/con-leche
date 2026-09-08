#!/usr/bin/env python3
"""Derive the BAD twin of task #227's fixture (`ind_mutual_idxsort`).

  ind_mutual_idxsort_bad.ndjson — ind_mutual_idxsort with the constant
      `IdxSort.IdxW`, used as the second index domain of the mutual pair
      `MA`/`MB`, replaced IN PLACE by `Nat.zero`: an index domain that is
      not a type at all.  (The expression node is shared by every use, so
      the members, their constructors and the examples change together.)

      Official rejects the input ("type expected", exit 1).  con-leche's
      modeller does not validate the domain — the user's ruling: it may be
      "yolo-like", invalid input is caught in the checked code — and the
      sort CEILING (`Kit.sortCeil`) returns a level for `Nat.zero` like it
      would for any term, so the modeller emits a tag family with a field
      `(i : Nat.zero)`; the fold rejects that generated record, exit 1.
      The ceiling can only make the tag's universe too large, never make
      an ill-sorted domain pass.

Usage: scripts/mk_idxsort_bad.py   (reads and writes under tests/e2e/)
"""
import json


def load(path):
    return [json.loads(l) for l in open(path).read().splitlines()]


def dump(path, recs):
    with open(path, "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")


def names_of(recs):
    names = {}
    for r in recs:
        if "in" in r and "str" in r:
            names[r["in"]] = (r["str"]["pre"], r["str"]["str"])
        elif "in" in r and "num" in r:
            names[r["in"]] = (r["num"]["pre"], str(r["num"]["i"]))

    def full(i):
        if i == 0:
            return ""
        pre, s = names[i]
        p = full(pre)
        return s if p == "" else p + "." + s

    return {full(i): i for i in names}


src = "tests/e2e/ind_mutual_idxsort.ndjson"
recs = load(src)
names = names_of(recs)
idxw = names["IdxSort.IdxW"]
zero = names["Nat.zero"]
target = None
for i, r in enumerate(recs):
    if "ie" in r and "const" in r and r["const"]["name"] == idxw:
        assert target is None, "several `IdxW` const nodes"
        target = i
assert target is not None, "no `IdxW` const node"
ie = recs[target]["ie"]
recs[target] = {"const": {"name": zero, "us": []}, "ie": ie}
dump("tests/e2e/ind_mutual_idxsort_bad.ndjson", recs)
print("ind_mutual_idxsort_bad.ndjson: `IdxW` (ie %d) -> `Nat.zero`" % ie)
