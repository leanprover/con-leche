#!/usr/bin/env python3
"""Derive the `ind_flags_*` twins of tests/e2e/direct_fix_nat.ndjson (task #630).

lean4export 3.2.0 (lean4 PR #16595) writes five more booleans on every
inductive type record: `isImpredicative`, `isK`, `hasProjections`,
`hasEta`, `hasLargeElim`.  Both twins patch INDUCTIVE TYPE RECORDS only.

  ind_flags_parse       — every type record carries the five flags the
                          official kernel would accept for it (`Nat'`
                          and `List'`: a large eliminator and nothing
                          else; `Eq`: not impredicative, K, a large
                          eliminator).  ACCEPTS (0).
  ind_flags_partial_bad — `Nat'` carries `isImpredicative` and `isK`
                          only: a 3.2.0 record lacks three required
                          keys, a 3.1.0 record has two too many.
                          Malformed input, REJECTED (1) by the parse.
  ind_flags_no_reflexive — `ind_flags_parse` without `isReflexive`,
                          which lean4 dropped from `InductiveVal`: the
                          key is optional and ignored.  ACCEPTS (0).

Usage: scripts/mk_ind_flags_parse.py [tests/e2e/direct_fix_nat.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/direct_fix_nat.ndjson"
lines = open(src).read().splitlines()
recs = [json.loads(l) for l in lines]

names = {}
for r in recs:
    if "in" in r:
        v = r.get("str") or r.get("num")
        names[r["in"]] = (v["pre"], v.get("str"))


def name(i):
    pre, s = names[i]
    return s if pre == 0 else name(pre) + "." + s


FLAGS = {
    "Nat'": (False, False, False, False, True),
    "List'": (False, False, False, False, True),
    "Eq": (False, True, False, False, True),
}
KEYS = ["isImpredicative", "isK", "hasProjections", "hasEta", "hasLargeElim"]


def emit(path, patch):
    out = []
    for line, r in zip(lines, recs):
        if "inductive" in r:
            r = json.loads(json.dumps(r))
            for t in r["inductive"]["types"]:
                patch(name(t["name"]), t)
            line = json.dumps(r, separators=(",", ":"), ensure_ascii=False)
        out.append(line)
    open(path, "w").write("\n".join(out) + "\n")


def full(n, t):
    for k, v in zip(KEYS, FLAGS[n]):
        t[k] = v


def partial(n, t):
    if n == "Nat'":
        t["isImpredicative"] = False
        t["isK"] = False


emit("tests/e2e/ind_flags_parse.ndjson", full)
emit("tests/e2e/ind_flags_partial_bad.ndjson", partial)


def no_reflexive(n, t):
    full(n, t)
    del t["isReflexive"]


emit("tests/e2e/ind_flags_no_reflexive.ndjson", no_reflexive)
