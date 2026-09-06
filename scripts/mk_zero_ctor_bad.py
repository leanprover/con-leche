#!/usr/bin/env python3
"""Derive the two bad twins of tests/e2e/zero_ctor.ndjson (task #181).

  zero_ctor_false_proof.ndjson  — the stream plus a theorem `bogus : False`
                                  whose value is the closed term `Prop`
                                  (ill-typed); the checker must REJECT.
  zero_ctor_bad_rec.ndjson      — `Nada.rec`'s type replaced by `Type`
                                  (the type former's own type): a
                                  recognised zero-constructor block whose
                                  recursor is not the generated one; the
                                  direct sum install must REJECT.

Usage: scripts/mk_zero_ctor_bad.py [tests/e2e/zero_ctor.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/zero_ctor.ndjson"
lines = open(src).read().splitlines()
recs = [json.loads(l) for l in lines]

names = {}      # name index -> (prefix index, string)
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

def name_idx(s):
    for i in names:
        if full(i) == s:
            return i
    raise SystemExit(f"name {s} not in the stream")

false_n = name_idx("False")
zero_lvl = 0        # the level table's implicit entry 0 is `zero`
false_const = None
prop_sort = None
for r in recs:
    if "ie" in r:
        e = r
        if "const" in e and e["const"]["name"] == false_n and e["const"]["us"] == []:
            false_const = e["ie"]
        if "sort" in e and e["sort"] == zero_lvl:
            prop_sort = e["ie"]
if false_const is None:
    raise SystemExit("no `False` constant expression in the stream")
if prop_sort is None:
    # find how sorts are spelled and pick Prop
    for r in recs:
        if "ie" in r and "sort" in r:
            raise SystemExit(f"sort spelling: {r}")
    raise SystemExit("no sort expression")

max_in = max(r["in"] for r in recs if "in" in r)
bogus_n = max_in + 1
out = lines + [
    json.dumps({"in": bogus_n, "str": {"pre": 0, "str": "bogus"}}),
    json.dumps({"thm": {"all": [bogus_n], "levelParams": [], "name": bogus_n,
                        "type": false_const, "value": prop_sort}}),
]
open("tests/e2e/zero_ctor_false_proof.ndjson", "w").write("\n".join(out) + "\n")

# the bad recursor: Nada.rec's type := Nada's type (`Type`)
nada_n = name_idx("Nada")
nada_rec_n = name_idx("Nada.rec")
out = []
for l in lines:
    r = json.loads(l)
    if "inductive" in r:
        blk = r["inductive"]
        if any(t["name"] == nada_n for t in blk["types"]):
            nada_ty = [t for t in blk["types"] if t["name"] == nada_n][0]["type"]
            for rec in blk["recs"]:
                if rec["name"] == nada_rec_n:
                    rec["type"] = nada_ty
            l = json.dumps(r, separators=(",", ":"))
    out.append(l)
open("tests/e2e/zero_ctor_bad_rec.ndjson", "w").write("\n".join(out) + "\n")
print("wrote tests/e2e/zero_ctor_false_proof.ndjson and tests/e2e/zero_ctor_bad_rec.ndjson")
