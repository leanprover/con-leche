#!/usr/bin/env python3
"""Forge the RECPOS robustness fixtures (lane SEEDDEFEQ, from the RECPOS
spike's `forge.py`): variations of official's auxiliary recursor family,
each from an EXPORTED good twin.

* `corner_recpos_missing_rec_1`, `_missing_rec_2` — the aux recursor
  `TL.rec_1` / `TL.rec_2` of `corner_nestind_f13_listrose` dropped from the
  inductive record.  Official 0 (replay generates the auxiliaries itself
  and compares only the recursors the stream carries).  Ours 1: the
  stream must carry every auxiliary recursor (ruling 2026-09-27, an
  official-compatible restriction, charter item 9).
* `corner_recpos_missing_unreached` — the aux recursor `AT.rec_1` of
  `corner_posderiv_major_delta` (major `List AT`, an occurrence whnf
  erases, no rule calls it) dropped.  Official 0; ours 1 (same ruling).
* `corner_recpos_mutual_missing_unreached` — the same at a MUTUAL block:
  `MA.rec_1` of `corner_recpos_mutual_delta` (source
  `tests/e2e/src/corner_recpos_mutual_delta.lean`) dropped.  Official 0;
  ours 0: nothing reads the erased class (no rule calls it, the name set
  is consistent, and the one-member conformance check does not run at
  k = 2), so the omission is invisible — see DESIGN, SEEDDEFEQ.
* `corner_recpos_perm_names` — `TL.rec_1` and `TL.rec_2` renamed into
  each other.  Official 1 ("Invalid recursor TL.rec", generated names
  compared by name); ours 0 (the check reads classes by major, not by
  name): a sound superset.
* `corner_recpos_split_copy` — an extra copy of `TL.rec_1` as `TL.rec_3`
  (same major, nobody calls it).  Official 1 ("No such recursor
  TL.rec_3"); ours 0: a sound superset.
* `corner_recpos_merge_defeq` — `corner_nestind_k53_callee_bad` with the
  now-uncalled `WT.rec_2` dropped and `WT.rec_3` renamed `WT.rec_2`: the
  call on `l : List ((fun _ => WR WT) Nat)` lands at the defeq class
  `List (WR WT)`, which is the only one.  Official 1 ("Invalid recursor
  WT.rec_2"); coarser identification, a sound superset once the call
  tie is per-component defeq.

Official verdicts measured with the arena official v4.34.0-rc2.

Usage: scripts/mk_recpos_fixtures.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
E2E = os.path.join(ROOT, "tests/e2e")


def load(n):
    return [json.loads(l) for l in open(f"{E2E}/{n}.ndjson")]


def names(recs):
    nm = {0: ""}
    for r in recs:
        if "in" in r:
            k = "str" if "str" in r else "num"
            pre = nm[r[k]["pre"]]
            s = str(r[k][k if k == "str" else "i"])
            nm[r["in"]] = (pre + "." if pre else "") + s
    return nm


def nid(recs, full):
    return [i for i, s in names(recs).items() if s == full][0]


def setstr(recs, i, s):
    for r in recs:
        if r.get("in") == i:
            r["str"]["str"] = s


def ind_with_rec(recs, recname):
    i = nid(recs, recname)
    for r in recs:
        if "inductive" in r and any(x["name"] == i for x in r["inductive"]["recs"]):
            return r, i


def drop_rec(recs, recname):
    ind, i = ind_with_rec(recs, recname)
    ind["inductive"]["recs"] = [x for x in ind["inductive"]["recs"] if x["name"] != i]


def save(recs, n):
    with open(f"{E2E}/{n}.ndjson", "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":")) + "\n")


for drop in ("TL.rec_1", "TL.rec_2"):
    R = load("corner_nestind_f13_listrose")
    drop_rec(R, drop)
    save(R, "corner_recpos_missing_" + drop.split(".")[1])

R = load("corner_posderiv_major_delta")
drop_rec(R, "AT.rec_1")
save(R, "corner_recpos_missing_unreached")

R = load("corner_recpos_mutual_delta")
drop_rec(R, "MA.rec_1")
save(R, "corner_recpos_mutual_missing_unreached")

R = load("corner_nestind_f13_listrose")
a, b = nid(R, "TL.rec_1"), nid(R, "TL.rec_2")
setstr(R, a, "rec_2")
setstr(R, b, "rec_1")
save(R, "corner_recpos_perm_names")

R = load("corner_nestind_f13_listrose")
ind, i = ind_with_rec(R, "TL.rec_1")
pre = [r for r in R if r.get("in") == i][0]["str"]["pre"]
new = max(r["in"] for r in R if "in" in r) + 1
R.insert(R.index(ind), {"in": new, "str": {"pre": pre, "str": "rec_3"}})
cp = dict([x for x in ind["inductive"]["recs"] if x["name"] == i][0])
cp["name"] = new
ind["inductive"]["recs"].append(cp)
save(R, "corner_recpos_split_copy")

R = load("corner_nestind_k53_callee_bad")
i2 = nid(R, "WT.rec_2")
i3 = nid(R, "WT.rec_3")
drop_rec(R, "WT.rec_2")
setstr(R, i2, "rec_9")
setstr(R, i3, "rec_2")
save(R, "corner_recpos_merge_defeq")
