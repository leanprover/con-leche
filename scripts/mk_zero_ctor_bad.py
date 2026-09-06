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

And the three REDEFINITION twins (user ruling, task #181: `Empty` and
`False` are pinned, and a stream declaring either name as anything but
the pinned block is REJECTED):

  empty_redefined.ndjson        — the one-constructor `OfNat` block renamed
                                  to `Empty` (so `Empty`, `Empty.ofNat`,
                                  `Empty.mk`, `Empty.rec`): REJECT.
  false_redefined.ndjson        — `def False : Prop := PEmpty'.{0}` placed
                                  before the toolchain's `False` block:
                                  REJECT.
  false_rec_bad.ndjson          — the toolchain's `False` block with
                                  `False.rec`'s type replaced by `Type`
                                  (not the pin any more): REJECT.

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

# empty_redefined: the one-constructor `OfNat` block becomes `Empty`
ofnat_n = name_idx("OfNat")
out = []
for l in lines:
    r = json.loads(l)
    if "in" in r and r["in"] == ofnat_n:
        r["str"]["str"] = "Empty"
        l = json.dumps(r, separators=(",", ":"))
    out.append(l)
open("tests/e2e/empty_redefined.ndjson", "w").write("\n".join(out) + "\n")

# false_redefined: `def False : Prop := PEmpty'.{0}` before the `False` block
pempty_n = name_idx("PEmpty'")
max_ie = max(r["ie"] for r in recs if "ie" in r)
pempty0 = max_ie + 1
out = []
for l in lines:
    r = json.loads(l)
    if "inductive" in r and any(t["name"] == false_n for t in r["inductive"]["types"]):
        out.append(json.dumps({"ie": pempty0, "const": {"name": pempty_n, "us": [zero_lvl]}},
                              separators=(",", ":")))
        out.append(json.dumps({"def": {"all": [false_n], "hints": {"regular": 1},
                                       "levelParams": [], "name": false_n, "safety": "safe",
                                       "type": prop_sort, "value": pempty0}},
                              separators=(",", ":")))
    out.append(l)
open("tests/e2e/false_redefined.ndjson", "w").write("\n".join(out) + "\n")

# false_rec_bad: the toolchain's `False.rec` with type `Type`
false_rec_n = name_idx("False.rec")
type1 = None
for r in recs:
    if "ie" in r and "sort" in r:
        # `Type` = sort (succ zero): find the level `succ 0`
        pass
succ0 = None
for r in recs:
    if "il" in r and r.get("succ") == zero_lvl:
        succ0 = r["il"]
for r in recs:
    if "ie" in r and r.get("sort") == succ0:
        type1 = r["ie"]
if type1 is None:
    raise SystemExit("no `Type` expression in the stream")
out = []
for l in lines:
    r = json.loads(l)
    if "inductive" in r and any(t["name"] == false_n for t in r["inductive"]["types"]):
        for rec in r["inductive"]["recs"]:
            if rec["name"] == false_rec_n:
                rec["type"] = type1
        l = json.dumps(r, separators=(",", ":"))
    out.append(l)
open("tests/e2e/false_rec_bad.ndjson", "w").write("\n".join(out) + "\n")
print("wrote the five bad twins under tests/e2e/")
