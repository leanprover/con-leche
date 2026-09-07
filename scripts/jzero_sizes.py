#!/usr/bin/env python3
"""Task #214: measure the DAG / unshared-tree sizes of one inductive block in a
raw lean4export ndjson stream.

Usage: jzero_sizes.py STREAM BLOCK_NAME_SUBSTRING
"""
import json, sys, collections

stream, target = sys.argv[1], sys.argv[2]

names = {0: ""}          # idx -> full dotted name
kids  = {}               # expr idx -> tuple of child expr idxs
kind  = {}               # expr idx -> kind tag
records = []             # (lineno, kind, json) for declaration records

BUDGET = 33554432

def name_of(i):
    return names.get(i, f"<{i}>")

EXPR_KEYS = ("app","lam","forallE","letE","proj","const","bvar","sort","natVal","strVal","mdata")

lineno = 0
with open(stream, "r") as f:
    for line in f:
        lineno += 1
        j = json.loads(line)
        if "in" in j:
            i = j["in"]
            if "str" in j:
                v = j["str"]; p = name_of(v["pre"])
                names[i] = (p + "." + v["str"]) if p else v["str"]
            elif "num" in j:
                v = j["num"]; p = name_of(v["pre"])
                names[i] = (p + "." + str(v["i"])) if p else str(v["i"])
            continue
        if "il" in j:
            continue
        if "ie" in j:
            i = j["ie"]
            if "app" in j:
                v = j["app"]; kids[i] = (v["fn"], v["arg"]); kind[i] = "app"
            elif "lam" in j:
                v = j["lam"]; kids[i] = (v["type"], v["body"]); kind[i] = "lam"
            elif "forallE" in j:
                v = j["forallE"]; kids[i] = (v["type"], v["body"]); kind[i] = "forallE"
            elif "letE" in j:
                v = j["letE"]; kids[i] = (v["type"], v["value"], v["body"]); kind[i] = "letE"
            elif "proj" in j:
                v = j["proj"]; kids[i] = (v["struct"],); kind[i] = "proj"
            elif "const" in j:
                kids[i] = (); kind[i] = "const"; names.setdefault(-1, "")
                kind[i] = ("const", j["const"]["name"])
            elif "mdata" in j:
                v = j["mdata"]; kids[i] = (v["expr"],); kind[i] = "mdata"
            else:
                kids[i] = (); kind[i] = "leaf"
            continue
        if "meta" in j:
            continue
        records.append((lineno, j))

sys.stderr.write(f"parsed {lineno} lines, {len(kids)} expr entries, {len(records)} decl records\n")

# ---- find the target inductive record
hit = None
for (ln, j) in records:
    if "inductive" not in j: continue
    v = j["inductive"]
    for t in v["types"]:
        if target in name_of(t["name"]):
            hit = (ln, j); break
    if hit: break
if hit is None:
    sys.exit(f"no inductive record containing {target}")

ln, j = hit
v = j["inductive"]
print(f"=== inductive record at line {ln} ===")
print("types:", [name_of(t['name']) for t in v["types"]])
print("ctors:", [name_of(c['name']) for c in v["ctors"]])
print("recs: ", [name_of(r['name']) for r in v["recs"]])

# ---- sizes
tree_memo = {}
def tree_size(i, cap=None):
    """unshared tree size, iterative, optional saturating cap"""
    stack = [(i, False)]
    while stack:
        n, done = stack.pop()
        if n in tree_memo: continue
        cs = kids.get(n, ())
        if done:
            s = 1 + sum(tree_memo[c] for c in cs)
            if cap is not None: s = min(cap, s)
            tree_memo[n] = s
        else:
            stack.append((n, True))
            for c in cs:
                if c not in tree_memo: stack.append((c, False))
    return tree_memo[i]

def dag_size(i):
    seen = set(); stack = [i]
    while stack:
        n = stack.pop()
        if n in seen: continue
        seen.add(n)
        stack.extend(kids.get(n, ()))
    return len(seen)

def report(label, i):
    t = tree_size(i, cap=None)
    d = dag_size(i)
    flag = "  *** OVER BUDGET ***" if t >= BUDGET else ""
    print(f"{label:60s} idx={i:8d} dag={d:7d} tree={t:,}{flag}")
    return (d, t)

print("\n--- type formers ---")
for t in v["types"]:
    report(name_of(t["name"]), t["type"])
print("\n--- constructors ---")
for c in v["ctors"]:
    report(name_of(c["name"]) + f" (nP={c['numParams']} nF={c['numFields']})", c["type"])
print("\n--- recursors ---")
for r in v["recs"]:
    report(name_of(r["name"]), r["type"])
    for ru in r["rules"]:
        report(f"  rule rhs ctor={name_of(ru['ctor'])} nf={ru['nfields']}", ru["rhs"])

# ---- per-field breakdown of the constructor type: walk the Pi spine
print("\n--- constructor Pi spine (each binder domain) ---")
for c in v["ctors"]:
    print(f"* {name_of(c['name'])}: nP={c['numParams']} nF={c['numFields']}")
    i = c["type"]; k = 0
    while kind.get(i) == "forallE":
        ty, body = kids[i]
        t = tree_size(ty); d = dag_size(ty)
        role = "param" if k < c["numParams"] else "field"
        print(f"   [{k:2d}] {role:5s} dag={d:6d} tree={t:,}")
        i = body; k += 1
    print(f"   codomain: dag={dag_size(i)} tree={tree_size(i):,}")

# ---- recursor spine
print("\n--- recursor Pi spine ---")
for r in v["recs"]:
    print(f"* {name_of(r['name'])}: nP={r['numParams']} nM={r['numMotives']} nm={r['numMinors']} nI={r['numIndices']}")
    i = r["type"]; k = 0
    while kind.get(i) == "forallE":
        ty, body = kids[i]
        print(f"   [{k:2d}] dag={dag_size(ty):6d} tree={tree_size(ty):,}")
        i = body; k += 1
    print(f"   codomain: dag={dag_size(i)} tree={tree_size(i):,}")

# ---- rule rhs: the lambda spine, then the body
print("\n--- rule rhs lambda spine ---")
for r in v["recs"]:
    for ru in r["rules"]:
        print(f"* rule for {name_of(ru['ctor'])} (nfields={ru['nfields']})")
        i = ru["rhs"]; k = 0
        while kind.get(i) == "lam":
            ty, body = kids[i]
            print(f"   lam[{k:2d}] dom dag={dag_size(ty):6d} tree={tree_size(ty):,}")
            i = body; k += 1
        print(f"   body: dag={dag_size(i)} tree={tree_size(i):,}")
