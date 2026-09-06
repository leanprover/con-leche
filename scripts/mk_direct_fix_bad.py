#!/usr/bin/env python3
"""Derive the two bad twins of tests/e2e/direct_fix_nat.ndjson (task #188).

  direct_fix_nat_neg_bad.ndjson — `Nat'.succ`'s field type patched from
                                  `Nat'` to `Nat' → Nat'`: a NON-POSITIVE
                                  occurrence of the block in a field, which
                                  the official kernel rejects; the direct
                                  fixed-point install must REJECT.
  direct_fix_nat_ih_bad.ndjson  — `Nat'.rec`'s `n_ih` binder patched from
                                  `motive n` to `Nat'`: a recognised
                                  recursive block whose recursor is not the
                                  generated one (the inductive hypothesis
                                  has the wrong type); the install must
                                  REJECT at the recursor comparison.

Usage: scripts/mk_direct_fix_bad.py [tests/e2e/direct_fix_nat.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/direct_fix_nat.ndjson"
lines = open(src).read().splitlines()
recs = [json.loads(l) for l in lines]

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

def name_idx(s):
    for i in names:
        if full(i) == s:
            return i
    raise SystemExit(f"name {s} not in the stream")

exprs = {}          # ie -> record
order = []          # (line index, record)
for k, r in enumerate(recs):
    if "ie" in r:
        exprs[r["ie"]] = r

nat_n = name_idx("Nat'")
succ_n = name_idx("Nat'.succ")
rec_n = name_idx("Nat'.rec")
nih_n = name_idx("n_ih")
n_n = name_idx("n")

def find_const(name):
    for e in exprs.values():
        if "const" in e and e["const"]["name"] == name and e["const"]["us"] == []:
            return e["ie"]
    raise SystemExit(f"no constant {full(name)} in the stream")

nat_const = find_const(nat_n)
max_ie = max(exprs)

def fresh():
    global max_ie
    max_ie += 1
    return max_ie

CHILD_KEYS = {"forallE": ("type", "body"), "lam": ("type", "body"),
              "app": ("fn", "arg"), "letE": ("type", "value", "body"),
              "proj": ("struct",), "mdata": ("expr",)}

def kind_of(e):
    for k in CHILD_KEYS:
        if k in e:
            return k
    return None

def rebuild(ie, target, replacer, new_recs, memo):
    """Copy the DAG below `ie` along every path to `target`, applying
    `replacer` to the target node; returns the (possibly new) ie."""
    if ie in memo:
        return memo[ie]
    e = exprs[ie]
    if ie == target:
        n = fresh()
        new_recs.append(replacer(e, n))
        memo[ie] = n
        return n
    k = kind_of(e)
    if k is None:
        memo[ie] = ie
        return ie
    node = dict(e[k])
    changed = False
    for ck in CHILD_KEYS[k]:
        if ck in node and isinstance(node[ck], int):
            c = rebuild(node[ck], target, replacer, new_recs, memo)
            if c != node[ck]:
                node[ck] = c
                changed = True
    if not changed:
        memo[ie] = ie
        return ie
    n = fresh()
    new_recs.append({"ie": n, k: node})
    memo[ie] = n
    return n

def block_of(name):
    for k, r in enumerate(recs):
        if "inductive" in r and any(t["name"] == name for t in r["inductive"]["types"]):
            return k, r
    raise SystemExit(f"no inductive block {full(name)}")

bk, block = block_of(nat_n)

# --- twin 1: the non-positive field ------------------------------------
succ = [c for c in block["inductive"]["ctors"] if c["name"] == succ_n][0]
new1 = []
arrow = fresh()
new1.append({"ie": arrow, "forallE": {"binderInfo": "default", "body": nat_const,
                                       "name": n_n, "type": nat_const}})
ctyp = fresh()
new1.append({"ie": ctyp, "forallE": {"binderInfo": "default", "body": nat_const,
                                      "name": n_n, "type": arrow}})
block1 = json.loads(json.dumps(block))
for c in block1["inductive"]["ctors"]:
    if c["name"] == succ_n:
        c["type"] = ctyp
out1 = [json.dumps(r) for r in recs[:bk]] + [json.dumps(r) for r in new1] + \
       [json.dumps(block1)] + [json.dumps(r) for r in recs[bk + 1:]]
open("tests/e2e/direct_fix_nat_neg_bad.ndjson", "w").write("\n".join(out1) + "\n")

# --- twin 2: the wrong inductive hypothesis -----------------------------
rec = [r for r in block["inductive"]["recs"] if r["name"] == rec_n][0]
ih_nodes = [e["ie"] for e in exprs.values()
            if "forallE" in e and e["forallE"]["name"] == nih_n]
if len(ih_nodes) != 1:
    raise SystemExit(f"expected one n_ih binder, found {ih_nodes}")
new2 = []
max_ie = max(exprs)
def replacer(e, n):
    node = dict(e["forallE"])
    node["type"] = nat_const
    return {"ie": n, "forallE": node}
new_ty = rebuild(rec["type"], ih_nodes[0], replacer, new2, {})
block2 = json.loads(json.dumps(block))
for r in block2["inductive"]["recs"]:
    if r["name"] == rec_n:
        r["type"] = new_ty
out2 = [json.dumps(r) for r in recs[:bk]] + [json.dumps(r) for r in new2] + \
       [json.dumps(block2)] + [json.dumps(r) for r in recs[bk + 1:]]
open("tests/e2e/direct_fix_nat_ih_bad.ndjson", "w").write("\n".join(out2) + "\n")
print("wrote direct_fix_nat_neg_bad.ndjson, direct_fix_nat_ih_bad.ndjson")
