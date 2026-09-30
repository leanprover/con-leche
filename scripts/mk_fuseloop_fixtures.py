#!/usr/bin/env python3
"""Forge the FUSELOOP order fixture `tests/e2e/corner_fuseloop_order_decline`
from its exported good twin `tests/e2e/corner_fuseloop_order_base.ndjson`
(source `tests/e2e/src/corner_fuseloop_order_base.lean`; the expression
indices below are that export's).

Usage: scripts/mk_fuseloop_fixtures.py [<twin.ndjson> [<out.ndjson.gz>]]

A stream with TWO independent conditions --
a non-positive constructor (official and we reject it) and a recursor
whose parameter domain is `Sort (M+1)` with `M` a max-chain of `u`
exhausting the level comparison's fuel against the former's `Sort (u+1)`
(our resource limit: decline).  The positivity check runs in the pass,
before the recursor's type: exit 1, as official.  (Under the fused
traversal FUSELOOP, reverted by lane UNFUSE, the recursor's type ran
first: exit 2.)"""
import json, sys, gzip
FUEL = 10000
args = sys.argv[1:] + [None, None]
src = args[0] or "tests/e2e/corner_fuseloop_order_base.ndjson"
out = args[1] or "tests/e2e/corner_fuseloop_order_decline.ndjson.gz"
R = [json.loads(l) for l in open(src)]
ind = R.pop()
assert "inductive" in ind
il = max(r["il"] for r in R if "il" in r)
ie = max(r["ie"] for r in R if "ie" in r)
new = []
def lvl(**k):
    global il
    il += 1; new.append(dict({"il": il}, **k)); return il
def ex(**k):
    global ie
    ie += 1; new.append(dict(k, ie=ie)); return ie
u = 1
m = lvl(max=[u, u])
for _ in range(FUEL):
    m = lvl(max=[m, u])
m1 = lvl(succ=m)
sM = ex(sort=m1)
# the constructor: `{α} → (W α → α) → W α` (was `(α → W α) → W α`)
neg = ex(forallE={"binderInfo": "default", "body": 4, "name": 9, "type": 9})
f = ex(forallE={"binderInfo": "default", "body": 5, "name": 9, "type": neg})
ct = ex(forallE={"binderInfo": "implicit", "body": f, "name": 3, "type": 0})
ind["inductive"]["ctors"][0]["type"] = ct
# the recursor: `{α : Sort (M+1)} → …` (was `{α : Type u} → …`)
rt = ex(forallE={"binderInfo": "implicit", "body": 28, "name": 3, "type": sM})
ind["inductive"]["recs"][0]["type"] = rt
R += new + [ind]
text = "".join(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n" for r in R)
with open(out, "wb") as raw, gzip.GzipFile(filename="", mode="wb", fileobj=raw, mtime=0, compresslevel=9) as g:
    g.write(text.encode())
