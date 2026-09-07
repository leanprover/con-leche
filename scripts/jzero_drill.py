#!/usr/bin/env python3
"""Task #214: drill into WHERE a field type's unshared size comes from.

For a given expr index prints, per distinct DAG node, its tree size and its
multiplicity (number of unshared occurrences), sorted by their product = the
node's total contribution to the tree size.  Head constants are named.
"""
import json, sys, collections

stream, target = sys.argv[1], sys.argv[2]
WHICH = sys.argv[3] if len(sys.argv) > 3 else "ctor"

names = {0: ""}; kids = {}; kind = {}; headconst = {}; records = []

def name_of(i): return names.get(i, f"<{i}>")

with open(stream) as f:
    for line in f:
        j = json.loads(line)
        if "in" in j:
            i = j["in"]
            if "str" in j:
                v = j["str"]; p = name_of(v["pre"]); names[i] = (p+"."+v["str"]) if p else v["str"]
            elif "num" in j:
                v = j["num"]; p = name_of(v["pre"]); names[i] = (p+"."+str(v["i"])) if p else str(v["i"])
            continue
        if "il" in j: continue
        if "ie" in j:
            i = j["ie"]
            if "app" in j: v=j["app"]; kids[i]=(v["fn"],v["arg"]); kind[i]="app"
            elif "lam" in j: v=j["lam"]; kids[i]=(v["type"],v["body"]); kind[i]="lam"
            elif "forallE" in j: v=j["forallE"]; kids[i]=(v["type"],v["body"]); kind[i]="forallE"
            elif "letE" in j: v=j["letE"]; kids[i]=(v["type"],v["value"],v["body"]); kind[i]="letE"
            elif "proj" in j: v=j["proj"]; kids[i]=(v["struct"],); kind[i]="proj"
            elif "const" in j: kids[i]=(); kind[i]="const"; headconst[i]=j["const"]["name"]
            elif "mdata" in j: v=j["mdata"]; kids[i]=(v["expr"],); kind[i]="mdata"
            else: kids[i]=(); kind[i]="leaf"
            continue
        if "meta" in j: continue
        records.append(j)

hit = None
for j in records:
    if "inductive" in j and any(target in name_of(t["name"]) for t in j["inductive"]["types"]):
        hit = j["inductive"]; break

memo = {}
def tree_size(i):
    stack=[(i,False)]
    while stack:
        n,d = stack.pop()
        if n in memo: continue
        cs = kids.get(n,())
        if d: memo[n] = 1 + sum(memo[c] for c in cs)
        else:
            stack.append((n,True))
            for c in cs:
                if c not in memo: stack.append((c,False))
    return memo[i]

def head(i):
    """the head constant of an application spine, if any"""
    seen = 0
    while kind.get(i)=="app" and seen < 100:
        i = kids[i][0]; seen += 1
    if kind.get(i)=="const": return name_of(headconst[i])
    return f"<{kind.get(i)}>"

def spine_len(i):
    n = 0
    while kind.get(i)=="app": i = kids[i][0]; n += 1
    return n

def analyse(label, root):
    tree_size(root)
    # multiplicity: number of unshared occurrences of each DAG node under root
    mult = collections.defaultdict(int); mult[root] = 1
    # topological order (parents before children) via DFS postorder reversed
    order = []; seen=set(); stack=[(root,False)]
    while stack:
        n,d = stack.pop()
        if d: order.append(n); continue
        if n in seen: continue
        seen.add(n); stack.append((n,True))
        for c in kids.get(n,()): stack.append((c,False))
    for n in reversed(order):
        for c in kids.get(n,()): mult[c] += mult[n]
    print(f"\n===== {label}: dag={len(seen)} tree={memo[root]:,} =====")
    rows = sorted(seen, key=lambda n: -(mult[n]*memo[n]))
    print(f"{'contrib':>14} {'mult':>10} {'size':>9} {'kind':8} head")
    for n in rows[:20]:
        print(f"{mult[n]*memo[n]:>14,} {mult[n]:>10,} {memo[n]:>9,} {kind.get(n,'?'):8} {head(n)} (args={spine_len(n)})")
    # per-head-constant aggregate over *unshared occurrences*
    agg = collections.Counter()
    for n in seen:
        if kind.get(n)=="app" and kind.get(kids[n][0])!="app":
            pass
    # count unshared occurrences of each constant leaf
    cagg = collections.Counter()
    for n in seen:
        if kind.get(n)=="const": cagg[name_of(headconst[n])] += mult[n]
    print("  -- most-repeated constants (unshared occurrences) --")
    for nm,c in cagg.most_common(12):
        print(f"     {c:>12,}  {nm}")
    return mult

# the fields of the ctor
c = hit["ctors"][0]
i = c["type"]; k=0; fields=[]
while kind.get(i)=="forallE":
    ty,body = kids[i]; fields.append((k,ty)); i=body; k+=1

if WHICH == "ctor":
    for (k,ty) in fields:
        if tree_size(ty) > 1000000:
            analyse(f"ctor binder [{k}]", ty)
elif WHICH == "rhs":
    r = hit["recs"][0]; ru = r["rules"][0]
    analyse("rule rhs", ru["rhs"])
    analyse("minor premise (rec binder 8)", None)
