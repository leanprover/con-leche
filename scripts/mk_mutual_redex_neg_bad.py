#!/usr/bin/env python3
"""Forge a MUTUAL block whose constructor field reaches the OTHER member
NEGATIVELY through a reducible head — the reject twin of the accept-
subset fixture `corner_mutual_redex_other`.

  corner_mutual_redex_other_neg_bad  <- corner_mutual_redex_other
      The block's field `RA.mk : Id' RB → RA` is kept; the definition
      `Id'` it reaches through is re-pointed from `fun α => α` to
      `fun α => α → α` (and renamed `Neg'`), so the field's domain
      whnf's to `RB → RB`: a Π whose DOMAIN mentions the member `RB`.
      Official's `check_positivity` whnf's the domain, walks the Π and
      REJECTS ("non positive occurrence").  Lean cannot elaborate the
      block, hence the forge.  Everything after the block (`RA.size`,
      which fires the recursor) is dropped; the block's recursors are
      the exporter's, for the `Id'` block — official never reaches
      them.

      con-leche today DECLINES (exit 2): the uniform route's
      positivity walk is run with the member's own name only, so the
      domain is not normalised and the classifier sees the head `Neg'`
      (`.unsupported`).  Target verdict 1.

Usage: scripts/mk_mutual_redex_neg_bad.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = "corner_mutual_redex_other.ndjson"
OUT = "corner_mutual_redex_other_neg_bad.ndjson"

recs = [json.loads(l) for l in
        open(os.path.join(ROOT, "tests/e2e", SRC)).read().splitlines()]
E = {r["ie"]: r for r in recs if "ie" in r}
nxt = max(E) + 1

names = {r["in"]: r["str"]["str"] for r in recs if "in" in r and "str" in r
         and r["str"]["pre"] == 0}
idn = next(i for i, s in names.items() if s == "Id'")
defi = next(k for k, r in enumerate(recs)
            if "def" in r and r["def"]["name"] == idn)
d = recs[defi]["def"]
lam = E[d["value"]]["lam"]            # fun (α : Type) => α
assert E[lam["body"]] == {"bvar": 0, "ie": lam["body"]}

ins = []


def ex(node):
    global nxt
    r = dict(node, ie=nxt)
    nxt += 1
    ins.append(r)
    return r["ie"]


b1 = ex({"bvar": 1})
arrow = ex({"forallE": {"binderInfo": "default", "body": b1,
                        "name": lam["name"], "type": lam["body"]}})
val = ex({"lam": {"binderInfo": "default", "body": arrow,
                  "name": lam["name"], "type": lam["type"]}})
d["value"] = val
for r in recs:
    if r.get("in") == idn:
        r["str"]["str"] = "Neg'"

blk = next(k for k, r in enumerate(recs)
           if "inductive" in r and any(t["name"] == next(
               i for i, s in names.items() if s == "RA")
               for t in r["inductive"]["types"]))
out = recs[:defi] + ins + recs[defi:blk + 1]
with open(os.path.join(ROOT, "tests/e2e", OUT), "w") as f:
    for r in out:
        f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
print("%s: %d lines" % (OUT, len(out)))
