#!/usr/bin/env python3
"""Forge the RPTIE order fixture `tests/e2e/corner_rptie_order_decline`
from its exported good twin `tests/e2e/corner_rptie_order_base.ndjson`
(source `tests/e2e/src/corner_rptie_order_base.lean`; the expression and
level indices below are that export's).

Usage: scripts/mk_rptie_fixtures.py [<twin.ndjson> [<out.ndjson.gz>]]

A stream with TWO independent conditions --
* `P.mk : (α → E) → P α` (was `α → P α`; `P.rec` and `T.rec_1`'s
  minor premise at `P.mk` forged to match): the class `P (T α)`, which the
  field `K (P (T α))` names only under a redex whnf erases, has a
  constructor non-positive in `T` (official: its auxiliary type is
  non-positive, reject; we: the SEED of `T.rec_1` walks it, reject);
* `T.rec_1`'s parameter domain `Sort (M+1)` with `M` a max-chain of `u`
  exhausting the level comparison's fuel against the former's
  `Sort (u+1)` (K6, stage (b); our resource limit: decline).
The recursor check resolves every major (stage (b)) before it walks the
seeds, so stage (b)'s decline comes first: exit 2.  Official 1; before lane
RPTIE (the seeds read off the raw records and walked in the pass) 1."""
import json, sys, gzip
FUEL = 10000
args = sys.argv[1:] + [None, None]
src = args[0] or "tests/e2e/corner_rptie_order_base.ndjson"
out = args[1] or "tests/e2e/corner_rptie_order_decline.ndjson.gz"
R = [json.loads(l) for l in open(src)]
il = max(r["il"] for r in R if "il" in r)
ie = max(r["ie"] for r in R if "ie" in r)
new = []
def lvl(**k):
    global il
    il += 1; new.append(dict({"il": il}, **k)); return il
def ex(**k):
    global ie
    ie += 1; new.append(dict(k, ie=ie)); return ie
U, CONST_E, SORT_TYPE_U = 2, 1, 14
m = lvl(max=[U, U])
for _ in range(FUEL):
    m = lvl(max=[m, U])
sM = ex(sort=lvl(succ=m))
def fa(name, ty, body, bi="default"):
    return ex(forallE={"binderInfo": bi, "body": body, "name": name, "type": ty})
def lam(name, ty, body):
    return ex(lam={"binderInfo": "default", "body": body, "name": name, "type": ty})
def app(f, a):
    return ex(app={"fn": f, "arg": a})
# P.mk : {α : Type u} → (α → E) → P α
pmk = fa(17, SORT_TYPE_U, fa(23, fa(23, 4, CONST_E), 20), "implicit")
# P.rec: the minor premise and the rule's λ at the new field type
minor = fa(23, fa(23, 19, CONST_E), 29)
prec = fa(17, SORT_TYPE_U, fa(5, 25, fa(26, minor, 32), "implicit"), "implicit")
prhs = lam(17, SORT_TYPE_U, lam(5, 25, lam(26, minor, lam(23, fa(23, 7, CONST_E), 36))))
# the new records go before the first inductive that reads them (P's)
iP = next(i for i, r in enumerate(R) if "inductive" in r and r["inductive"]["ctors"][0]["type"] == 22)
P = R[iP]["inductive"]
P["ctors"][0]["type"] = pmk
assert P["recs"][0]["type"] == 35 and P["recs"][0]["rules"][0]["rhs"] == 40
P["recs"][0]["type"] = prec
P["recs"][0]["rules"][0]["rhs"] = prhs
R = R[:iP] + new + R[iP:]
# T.rec_1 : {α : Sort (M+1)} → …  (was {α : Type u}), its P.mk minor at the
# new field (`(a : T α → E) → motive_1 (P.mk (T α) a)`), before T's record
new = []
body = app(56, app(app(26, app(41, 75)), 4))
m74 = fa(23, fa(23, 66, CONST_E), body)
rec1 = fa(17, sM, fa(31, 50, fa(32, 52, fa(33, 55, fa(26, 65, fa(26, m74, 78))), "implicit"),
    "implicit"), "implicit")
T = R[-1]["inductive"]
assert T["recs"][0]["type"] == 84
T["recs"][0]["type"] = rec1
R = R[:-1] + new + R[-1:]
text = "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in R)
with open(out, "wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=9) as g:
    g.write(text.encode())
