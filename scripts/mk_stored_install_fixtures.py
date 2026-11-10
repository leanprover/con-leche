#!/usr/bin/env python3
"""Derive the stored-install twins of tests/e2e/ind_defhead_fix.ndjson (task #431).

Every inductive block is installed as stored on the parallel install,
its checked install a job of the check phase; where a part of the
reading fails the block's records are pushed as declared, and the
verdict is the job's.  Both twins make a later record (`L.len`, which
uses `L.rec`) depend on such a block, so the install goes on past it:

  ind_defhead_opaque_bad — `MyType` becomes an OPAQUE `MyType : Type 1
                           := Type`, which does not unfold, so `L :
                           MyType` does not reduce to a sort.
                           Official rejects ("type former does not
                           reduce"); the stored install pushes the
                           former as declared, and the job rejects.
  ind_ctor_levels_use    — the constructor `L.nil` declares a level
                           parameter the block does not have, so the
                           block is not installed (nothing is pushed)
                           and `L.len`'s install fails on the missing
                           `L.rec`; the verdict is the block's (its
                           checked install rejects the constructor's
                           universe parameters, as official does), at
                           every `--jobs`.

Usage: scripts/mk_stored_install_fixtures.py [tests/e2e/ind_defhead_fix.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/ind_defhead_fix.ndjson"
recs = [json.loads(l) for l in open(src).read().splitlines()]
names = {r["in"]: r["str"]["str"] for r in recs if "in" in r and "str" in r}


def nid(s, pre=0):
    for r in recs:
        if "in" in r and "str" in r and r["str"] == {"pre": pre, "str": s}:
            return r["in"]
    raise SystemExit(f"no name {s}")


my_type, l_name = nid("MyType"), nid("L")
u_name = nid("u")


def emit(path, patch):
    out = [json.dumps(patch(json.loads(json.dumps(r)))) for r in recs]
    open(path, "w").write("\n".join(out) + "\n")


def opaque(r):
    d = r.get("def")
    if d and d["name"] == my_type:
        return {"opaque": {"all": [my_type], "isUnsafe": False, "levelParams": [],
                           "name": my_type, "type": d["type"], "value": d["value"]}}
    return r


def ctor_levels(r):
    ind = r.get("inductive")
    if ind and ind["types"][0]["name"] == l_name:
        ind["ctors"][0]["levelParams"] = [u_name]
    return r


emit("tests/e2e/ind_defhead_opaque_bad.ndjson", opaque)
emit("tests/e2e/ind_ctor_levels_use.ndjson", ctor_levels)
