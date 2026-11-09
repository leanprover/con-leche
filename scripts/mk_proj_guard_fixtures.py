#!/usr/bin/env python3
"""Derive the projection-guard fixtures of task #480 from prop_proj_raw.

`PropStructure.{u,v}` is a `Prop` structure with the fields
  0 aProof : PUnit.{u}, 1 someData : PUnit.{v}, 2 aSecondProof : PUnit.{u},
  3 someMoreData : PUnit.{v}, 4 aProofAboutData : someMoreData = someMoreData,
  5 aFinalProof : PUnit.{u}
and the guard at a use `.proj PropStructure i x` at levels {0, 1} is official
`infer_proj`'s: field `i`, and every earlier field a later one uses, must be
a proposition.  Field 1 is data nothing uses, field 3 is data field 4 uses.

  proj_guard_data_bad            field 1: its own sort is not Prop
  proj_guard_prop_after_data     field 2: Prop, the data before it unused (accepted)
  proj_guard_used_data_bad       field 4: Prop, but field 3 is used data
  proj_guard_past_used_data_bad  field 5: Prop, but field 3 is used data

Each appends one definition to prop_proj_raw.ndjson; the literal-Prop test at
the use reads the entry, the rows are computed at the use (`projGuardRows`).

Usage: scripts/mk_proj_guard_fixtures.py
"""
import json

SRC = "tests/e2e/prop_proj_raw.ndjson"


def main():
    lines = open(SRC).read().splitlines()
    recs = [json.loads(l) for l in lines]
    names = {}
    for r in recs:
        if "in" in r and "str" in r:
            s = r["str"]
            names[(s["pre"], s["str"])] = r["in"]
    next_in = max(r["in"] for r in recs if "in" in r) + 1
    next_ie = max(r["ie"] for r in recs if "ie" in r) + 1
    exprs = {}
    for r in recs:
        if "ie" in r:
            exprs[r["ie"]] = r
    # the structure at levels {0, 1}: the existing `x`'s domain; its PUnit.{0}
    k = recs[-1]["def"]
    lam = exprs[k["value"]]["lam"]
    pi = exprs[k["type"]]["forallE"]
    struct, x_name = lam["type"], lam["name"]
    punit0 = pi["body"]
    pstruct_name = exprs[lam["body"]]["proj"]["typeName"]
    punit_name = names[(0, "PUnit")]
    eq_name = names[(0, "Eq")]
    # level 1 is the structure's second level argument
    one = exprs[struct]["const"]["us"][1]

    def fixture(out, def_name, mk):
        nonlocal_ie = [next_ie]
        new = [{"in": next_in, "str": {"pre": 0, "str": def_name}}]

        def add(payload):
            i = nonlocal_ie[0]
            nonlocal_ie[0] += 1
            new.append({**payload, "ie": i})
            return i

        def proj(j):
            return add({"proj": {"idx": j, "struct": add({"bvar": 0}), "typeName": pstruct_name}})

        idx, ty = mk(add, proj)
        body = add({"proj": {"idx": idx, "struct": add({"bvar": 0}), "typeName": pstruct_name}})
        value = add({"lam": {"binderInfo": "default", "body": body, "name": x_name, "type": struct}})
        typ = add({"forallE": {"binderInfo": "default", "body": ty, "name": x_name, "type": struct}})
        new.append({"def": {"all": [next_in], "hints": "opaque", "levelParams": [], "name": next_in,
                            "safety": "safe", "type": typ, "value": value}})
        with open(out, "w") as f:
            for l in lines:
                f.write(l + "\n")
            for r in new:
                f.write(json.dumps(r, separators=(",", ":"), sort_keys=True) + "\n")

    def punit1(add):
        return add({"const": {"name": punit_name, "us": [one]}})

    fixture("tests/e2e/proj_guard_data_bad.ndjson", "projData",
            lambda add, proj: (1, punit1(add)))
    fixture("tests/e2e/proj_guard_prop_after_data.ndjson", "projAfterData",
            lambda add, proj: (2, punit0))

    def eq_about_data(add, proj):
        p = punit1(add)
        eq = add({"const": {"name": eq_name, "us": [one]}})
        a = proj(3)
        f = add({"app": {"arg": p, "fn": eq}})
        g = add({"app": {"arg": a, "fn": f}})
        return (4, add({"app": {"arg": a, "fn": g}}))

    fixture("tests/e2e/proj_guard_used_data_bad.ndjson", "projAboutData", eq_about_data)
    fixture("tests/e2e/proj_guard_past_used_data_bad.ndjson", "projPastData",
            lambda add, proj: (5, punit0))


main()
