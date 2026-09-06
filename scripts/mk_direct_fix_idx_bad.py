#!/usr/bin/env python3
"""Derive the bad twin of tests/e2e/direct_fix_vec.ndjson (task #188, indexed).

  direct_fix_vec_ih_idx_bad.ndjson — `Vec'.rec`'s `v_ih` binder patched
                                     from `motive n v` to
                                     `motive (Nat.succ n) v`: the inductive
                                     hypothesis at the WRONG index (the
                                     constructor's result index instead of
                                     the recursive field's); the direct
                                     fixed-point install must REJECT at the
                                     recursor comparison.

Usage: scripts/mk_direct_fix_idx_bad.py [tests/e2e/direct_fix_vec.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/direct_fix_vec.ndjson"
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

exprs = {}
for r in recs:
    if "ie" in r:
        exprs[r["ie"]] = r

vec_n = name_idx("Vec'")
rec_n = name_idx("Vec'.rec")
vih_n = name_idx("v_ih")
succ_n = name_idx("Nat.succ")

def find_const(name):
    for e in exprs.values():
        if "const" in e and e["const"]["name"] == name and e["const"]["us"] == []:
            return e["ie"]
    raise SystemExit(f"no constant {full(name)} in the stream")

succ_const = find_const(succ_n)
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

bk, block = block_of(vec_n)
rec = [r for r in block["inductive"]["recs"] if r["name"] == rec_n][0]

# the `v_ih` binder: `∀ (v_ih : motive n v), …` with `motive n v =
# app (app (bvar 4) (bvar 2)) (bvar 0)` at the binder's frame
ih_nodes = [e["ie"] for e in exprs.values()
            if "forallE" in e and e["forallE"]["name"] == vih_n]
if len(ih_nodes) != 1:
    raise SystemExit(f"expected one v_ih binder, found {ih_nodes}")
ih = exprs[ih_nodes[0]]
ty = exprs[ih["forallE"]["type"]]
inner = exprs[ty["app"]["fn"]]
if "app" not in ty or "app" not in inner or "bvar" not in exprs[inner["app"]["arg"]]:
    raise SystemExit("v_ih's type is not `motive n v`")
n_bvar = inner["app"]["arg"]

new = []
succ_n_ie = fresh()
new.append({"ie": succ_n_ie, "app": {"fn": succ_const, "arg": n_bvar}})
inner2 = fresh()
new.append({"ie": inner2, "app": {"fn": inner["app"]["fn"], "arg": succ_n_ie}})
ty2 = fresh()
new.append({"ie": ty2, "app": {"fn": inner2, "arg": ty["app"]["arg"]}})

def replacer(e, n):
    node = dict(e["forallE"])
    node["type"] = ty2
    return {"ie": n, "forallE": node}

new_ty = rebuild(rec["type"], ih_nodes[0], replacer, new, {})
block2 = json.loads(json.dumps(block))
for r in block2["inductive"]["recs"]:
    if r["name"] == rec_n:
        r["type"] = new_ty
out = [json.dumps(r) for r in recs[:bk]] + [json.dumps(r) for r in new] + \
      [json.dumps(block2)] + [json.dumps(r) for r in recs[bk + 1:]]
open("tests/e2e/direct_fix_vec_ih_idx_bad.ndjson", "w").write("\n".join(out) + "\n")
print("wrote direct_fix_vec_ih_idx_bad.ndjson")
