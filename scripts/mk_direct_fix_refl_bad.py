#!/usr/bin/env python3
"""Derive the two bad twins of tests/e2e/direct_fix_wtype.ndjson (task #202
Stage B: `Type`-valued reflexive blocks).

  direct_fix_wtype_neg_bad.ndjson — `W'.sup`'s reflexive field `f : β a →
                                    W' α β` patched to `f : (β a → W' α β) →
                                    W' α β`: the block occurs NEGATIVELY
                                    (under the binder of a domain), which the
                                    official kernel rejects; the direct
                                    fixed-point install must REJECT
                                    (positivity).
  direct_fix_wtype_ih_bad.ndjson  — `W'.rec`'s `f_ih` binder patched from
                                    `∀ b, motive (f b)` to the closed type
                                    `Type` (the sort of the parameter `α`,
                                    a node the stream defines before the
                                    block): a recognised block whose
                                    recursor is not the generated one (the
                                    inductive hypothesis has the wrong type);
                                    the install must REJECT at the recursor
                                    comparison.

Usage: scripts/mk_direct_fix_refl_bad.py [tests/e2e/direct_fix_wtype.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/direct_fix_wtype.ndjson"
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

exprs = {r["ie"]: r for r in recs if "ie" in r}
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

w_n = name_idx("W'")
sup_n = name_idx("W'.sup")
rec_n = name_idx("W'.rec")
f_n = name_idx("f")
fih_n = name_idx("f_ih")

bk, block = block_of(w_n)

def pi_chain(ie):
    out = []
    while "forallE" in exprs[ie]:
        out.append(ie)
        ie = exprs[ie]["forallE"]["body"]
    return out

# --- twin 1: the non-positive reflexive field ---------------------------
sup = [c for c in block["inductive"]["ctors"] if c["name"] == sup_n][0]
field = [ie for ie in pi_chain(sup["type"]) if exprs[ie]["forallE"]["name"] == f_n]
if len(field) != 1:
    raise SystemExit("expected exactly one binder `f` in W'.sup's type")
field = field[0]
new1 = []
def neg_replacer(e, n):
    dom = e["forallE"]["type"]              # `β a → W' α β`
    body = exprs[dom]["forallE"]["body"]    # `W' α β` under one binder
    wrapped = fresh()
    new1.append({"ie": wrapped, "forallE": {"binderInfo": "default", "body": body,
                                             "name": f_n, "type": dom}})
    node = dict(e["forallE"])
    node["type"] = wrapped
    return {"ie": n, "forallE": node}
memo = {}
ctyp = rebuild(sup["type"], field, neg_replacer, new1, memo)
block1 = json.loads(json.dumps(block))
for c in block1["inductive"]["ctors"]:
    if c["name"] == sup_n:
        c["type"] = ctyp
out1 = [json.dumps(r) for r in recs[:bk]] + [json.dumps(r) for r in new1] + \
       [json.dumps(block1)] + [json.dumps(r) for r in recs[bk + 1:]]
open("tests/e2e/direct_fix_wtype_neg_bad.ndjson", "w").write("\n".join(out1) + "\n")

# --- twin 2: the wrong inductive hypothesis -----------------------------
rec = [r for r in block["inductive"]["recs"] if r["name"] == rec_n][0]
# the closed type `Type`: the sort of `W'.sup`'s first binder (the
# parameter `α`), defined before the block
junk = exprs[sup["type"]]["forallE"]["type"]
if "sort" not in exprs[junk]:
    raise SystemExit("expected W'.sup's first binder to be a sort")

def find_ih(ie):
    """the `f_ih` binder reachable from the recursor's type"""
    seen = set()
    stack = [ie]
    while stack:
        x = stack.pop()
        if x in seen:
            continue
        seen.add(x)
        e = exprs[x]
        if "forallE" in e and e["forallE"]["name"] == fih_n:
            return x
        k = kind_of(e)
        if k:
            for ck in CHILD_KEYS[k]:
                if ck in e[k] and isinstance(e[k][ck], int):
                    stack.append(e[k][ck])
    raise SystemExit("no `f_ih` binder in W'.rec's type")
ih = find_ih(rec["type"])
new2 = []
def ih_replacer(e, n):
    node = dict(e["forallE"])
    node["type"] = junk
    return {"ie": n, "forallE": node}
memo = {}
rtyp = rebuild(rec["type"], ih, ih_replacer, new2, memo)
block2 = json.loads(json.dumps(block))
for r in block2["inductive"]["recs"]:
    if r["name"] == rec_n:
        r["type"] = rtyp
out2 = [json.dumps(r) for r in recs[:bk]] + [json.dumps(r) for r in new2] + \
       [json.dumps(block2)] + [json.dumps(r) for r in recs[bk + 1:]]
open("tests/e2e/direct_fix_wtype_ih_bad.ndjson", "w").write("\n".join(out2) + "\n")
print("wrote direct_fix_wtype_neg_bad.ndjson and direct_fix_wtype_ih_bad.ndjson")
