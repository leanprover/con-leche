#!/usr/bin/env python3
"""Task #214: the multiplicity ladder of one field type — which DAG nodes are
re-entered how often, and what the branching factor of each rung is."""
import json, sys, collections
stream, target = sys.argv[1], sys.argv[2]
BINDER = int(sys.argv[3]) if len(sys.argv) > 3 else 10
names={0:""}; kids={}; kind={}; hc={}; records=[]
def name_of(i): return names.get(i,f"<{i}>")
with open(stream) as f:
    for line in f:
        j=json.loads(line)
        if "in" in j:
            i=j["in"]
            if "str" in j: v=j["str"]; p=name_of(v["pre"]); names[i]=(p+"."+v["str"]) if p else v["str"]
            elif "num" in j: v=j["num"]; p=name_of(v["pre"]); names[i]=(p+"."+str(v["i"])) if p else str(v["i"])
            continue
        if "il" in j: continue
        if "ie" in j:
            i=j["ie"]
            if "app" in j: v=j["app"]; kids[i]=(v["fn"],v["arg"]); kind[i]="app"
            elif "lam" in j: v=j["lam"]; kids[i]=(v["type"],v["body"]); kind[i]="lam"
            elif "forallE" in j: v=j["forallE"]; kids[i]=(v["type"],v["body"]); kind[i]="forallE"
            elif "letE" in j: v=j["letE"]; kids[i]=(v["type"],v["value"],v["body"]); kind[i]="letE"
            elif "proj" in j: v=j["proj"]; kids[i]=(v["struct"],); kind[i]="proj"
            elif "const" in j: kids[i]=(); kind[i]="const"; hc[i]=j["const"]["name"]
            else: kids[i]=(); kind[i]="leaf"
            continue
        if "meta" in j: continue
        records.append(j)
hit=None
for j in records:
    if "inductive" in j and any(target in name_of(t["name"]) for t in j["inductive"]["types"]): hit=j["inductive"]; break
memo={}
def ts(i):
    st=[(i,False)]
    while st:
        n,d=st.pop()
        if n in memo: continue
        cs=kids.get(n,())
        if d: memo[n]=1+sum(memo[c] for c in cs)
        else:
            st.append((n,True))
            for c in cs:
                if c not in memo: st.append((c,False))
    return memo[i]
def head(i):
    while kind.get(i)=="app": i=kids[i][0]
    return name_of(hc[i]) if kind.get(i)=="const" else f"<{kind.get(i)}>"
c=hit["ctors"][0]; i=c["type"]; k=0; root=None
while kind.get(i)=="forallE":
    ty,body=kids[i]
    if k==BINDER: root=ty
    i=body; k+=1
ts(root)
seen=set(); order=[]; st=[(root,False)]
while st:
    n,d=st.pop()
    if d: order.append(n); continue
    if n in seen: continue
    seen.add(n); st.append((n,True))
    for ch in kids.get(n,()): st.append((ch,False))
mult=collections.defaultdict(int); mult[root]=1
indeg=collections.defaultdict(int)
for n in reversed(order):
    for ch in kids.get(n,()):
        mult[ch]+=mult[n]; indeg[ch]+=1
print(f"binder [{BINDER}]: dag={len(seen)} tree={memo[root]:,} sharing={memo[root]/len(seen):.0f}x")
print("\n-- nodes by multiplicity (the ladder): mult, in-degree (distinct parents), own tree size --")
print(f"{'mult':>10} {'indeg':>6} {'size':>10} {'kind':8} head")
for n in sorted(seen,key=lambda n:-mult[n])[:30]:
    print(f"{mult[n]:>10,} {indeg[n]:>6} {memo[n]:>10,} {kind.get(n,'?'):8} {head(n)}")
print("\n-- the multiplying spine: from the root down, always into the child with max mult --")
n=root; depth=0
while depth < 60:
    cs=kids.get(n,())
    print(f"  d={depth:3d} mult={mult[n]:>10,} size={memo[n]:>10,} indeg={indeg[n]:>5} {kind.get(n,'?'):8} {head(n)}")
    if not cs: break
    n=max(cs,key=lambda ch:mult[ch]); depth+=1
