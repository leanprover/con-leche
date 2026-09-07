#!/usr/bin/env python3
"""Derive two bad twins of tests/e2e/direct_fix_vec.ndjson (task #210 Part D):
an occurrence of the block inside an INDEX expression, which official's
`is_valid_ind_app` rejects (`has_ind_occ` on every index argument).

  direct_fix_vec_idx_occ_bad.ndjson — `Vec'.cons`'s recursive field
      `v : Vec' α n` patched to `v : Vec' α ((fun β : Sort (u+1) => n)
      (Vec' α n))`: the index whnf's to `n`, but official does not whnf
      index arguments — "non valid occurrence of the datatypes being
      declared".  REJECT.
  direct_fix_vec_res_occ_bad.ndjson — `Vec'.cons`'s result `Vec' α
      (Nat.succ n)` patched to `Vec' α ((fun β : Sort (u+1) => Nat.succ n)
      (Vec' α n))`: official's "invalid return type".  REJECT.

Both constructors are well typed (the redex has type `Nat`); the
recursor is left as exported.

Usage: scripts/mk_direct_fix_occ_bad.py [tests/e2e/direct_fix_vec.ndjson]
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
cons_n = name_idx("Vec'.cons")
alpha_n = name_idx("α")
v_n = name_idx("v")

def block_of(name):
    for k, r in enumerate(recs):
        if "inductive" in r and any(t["name"] == name for t in r["inductive"]["types"]):
            return k, r
    raise SystemExit(f"no inductive block {full(name)}")

bk, block = block_of(vec_n)
former = [t for t in block["inductive"]["types"] if t["name"] == vec_n][0]
cons = [c for c in block["inductive"]["ctors"] if c["name"] == cons_n][0]

# the former's sort `Sort (u+1)`: the body of its telescope
t = exprs[former["type"]]
while "forallE" in t:
    t = exprs[t["forallE"]["body"]]
if "sort" not in t:
    raise SystemExit("the former does not end in a sort")
sort_ie = t["ie"]

max_ie = max(exprs)
new = []

def node(body):
    """A fresh node, or an existing one with the same content."""
    global max_ie
    for e in list(exprs.values()) + new:
        if {k: v for k, v in e.items() if k != "ie"} == body:
            return e["ie"]
    max_ie += 1
    e = dict(body); e["ie"] = max_ie
    new.append(e)
    return max_ie

def bvar(i): return node({"bvar": i})
def app(f, a): return node({"app": {"fn": f, "arg": a}})
def lam(name, ty, body):
    return node({"lam": {"binderInfo": "default", "body": body, "name": name, "type": ty}})
def forall(name, ty, body, bi="default"):
    return node({"forallE": {"binderInfo": bi, "body": body, "name": name, "type": ty}})

def occ_index(fam_app, idx_body):
    """`(fun β : Sort (u+1) => idx_body) fam_app` — `idx_body` is written
    at the frame UNDER the binder."""
    return app(lam(alpha_n, sort_ie, idx_body), fam_app)

# Walk `Vec'.cons`'s type: α, n, a, v, result.
ty = exprs[cons["type"]]
binders = []
while "forallE" in ty:
    binders.append(ty)
    ty = exprs[ty["forallE"]["body"]]
result = ty
if len(binders) != 4 or names[binders[3]["forallE"]["name"]][1] != "v":
    raise SystemExit("Vec'.cons is not `α n a v → …`")

def rebuild_tele(bs, body):
    for b in reversed(bs):
        f = b["forallE"]
        body = forall(f["name"], f["type"], body, f["binderInfo"])
    return body

# twin 1: the field `v : Vec' α n` (frame α=#2, n=#1) gets the index
# `(fun β => n) (Vec' α n)`, `n` = #2 under the binder.
vty = exprs[binders[3]["forallE"]["type"]]        # app (app Vec' #2) #1
fam_at_v = vty["app"]["fn"]                       # app Vec' #2
vty2 = app(fam_at_v, occ_index(binders[3]["forallE"]["type"], bvar(2)))
b3 = dict(binders[3]["forallE"]); b3["type"] = vty2
v_binder = forall(b3["name"], b3["type"], b3["body"], b3["binderInfo"])
# rebuild the outer three binders around it
ty1 = v_binder
for b in reversed(binders[:3]):
    f = b["forallE"]
    ty1 = forall(f["name"], f["type"], ty1, f["binderInfo"])

# twin 2: the result `Vec' α (Nat.succ n)` (frame α=#3, n=#2, v=#0) gets
# the index `(fun β => Nat.succ n) (Vec' α n)`, `Nat.succ n` = succ #3
# under the binder, `Vec' α n` = app (app Vec' #3) #2.
res = result                                      # app (app Vec' #3) (succ #2)
fam_at_res = res["app"]["fn"]
succ_node = exprs[res["app"]["arg"]]              # app (const Nat.succ) #2
succ_c = succ_node["app"]["fn"]
res2 = app(fam_at_res, occ_index(app(fam_at_res, bvar(2)), app(succ_c, bvar(3))))
ty2 = rebuild_tele(binders, res2)

def write(name, cty):
    block2 = json.loads(json.dumps(block))
    for c in block2["inductive"]["ctors"]:
        if c["name"] == cons_n:
            c["type"] = cty
    out = [json.dumps(r) for r in recs[:bk]] + [json.dumps(r) for r in new] + \
          [json.dumps(block2)] + [json.dumps(r) for r in recs[bk + 1:]]
    open(f"tests/e2e/{name}.ndjson", "w").write("\n".join(out) + "\n")
    print(f"wrote {name}.ndjson")

write("direct_fix_vec_idx_occ_bad", ty1)
write("direct_fix_vec_res_occ_bad", ty2)
