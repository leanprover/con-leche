#!/usr/bin/env python3
"""Forge `corner_nestind_k53_callee_bad` (lane NESTIND s24, finding F16,
kernel check K.53) from its good twin `corner_nestind_k53_callee_free`
(source `tests/e2e/src/corner_nestind_k53_callee_free.lean`).

`WT.node (r : WR WT) (l : List ((fun _ => WR WT) Nat))`: the exported
recursor calls `WT.rec_2` (major `List ((fun _ => WR WT) Nat)`) on `l`.
The forged stream calls `WT.rec_3` (major `List (WR WT)`, DEFEQ by β but
another class) instead, and every recursor type's `l_ih` binder is
retargeted to that class's motive, so the recursors stay well-typed.

Official rejects: its recursors are generated and compared structurally
("Invalid recursor WT.rec_2", arena official v4.34.0-rc2, measured).
Today 1 (the modelled route: application type mismatch).  Target 1 (K.53:
the callee's major is not the whnf of the called field's type).

Usage: scripts/mk_nestind_k53_bad.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "tests/e2e/corner_nestind_k53_callee_free.ndjson")
DST = os.path.join(ROOT, "tests/e2e/corner_nestind_k53_callee_bad.ndjson")

recs = [json.loads(l) for l in open(SRC)]
names = {0: ""}
E = {}
for r in recs:
    if "in" in r:
        k = "str" if "str" in r else "num"
        pre = names[r[k]["pre"]]
        s = str(r[k][k if k == "str" else "i"])
        names[r["in"]] = (pre + "." if pre else "") + s
    if "ie" in r:
        E[r["ie"]] = r
nxt = max(E) + 1
new = []


def mk(body):
    global nxt
    r = dict(body)
    r["ie"] = nxt
    nxt += 1
    new.append(r)
    E[r["ie"]] = r
    return r["ie"]


def rewrite(i, f, memo):
    if i in memo:
        return memo[i]
    r = f(i)
    if r is not None:
        memo[i] = r
        return r
    e = E[i]
    out = i
    for kind, keys in (("app", ("fn", "arg")), ("lam", ("type", "body")),
                       ("forallE", ("type", "body"))):
        if kind in e:
            sub = {k: rewrite(e[kind][k], f, memo) for k in keys}
            if any(sub[k] != e[kind][k] for k in keys):
                d = dict(e[kind])
                d.update(sub)
                out = mk({kind: d})
    memo[i] = out
    return out


# the `l_ih` binder: its domain `motive_3 l` (bvar 4) becomes `motive_4 l` (bvar 3)
M = [i for i, e in E.items() if "forallE" in e and names[e["forallE"]["name"]] == "l_ih"]
assert len(M) == 1, M
M = M[0]
ty = E[E[M]["forallE"]["type"]]["app"]
assert E[ty["fn"]].get("bvar") == 4
b3 = [i for i, e in E.items() if e.get("bvar") == 3][0]
newM = mk({"forallE": dict(E[M]["forallE"], type=mk({"app": {"fn": b3, "arg": ty["arg"]}}))})


def fM(i):
    return newM if i == M else None


c2 = [i for i, e in E.items() if "const" in e and names[e["const"]["name"]] == "WT.rec_2"]
c3 = [i for i, e in E.items() if "const" in e and names[e["const"]["name"]] == "WT.rec_3"]
assert len(c2) == 1 and len(c3) == 1


def f23(i):
    return newM if i == M else (c3[0] if i == c2[0] else None)


for r in recs:
    ind = r.get("inductive")
    if ind and any(names[t["name"]] == "WT" for t in ind["types"]):
        for x in ind["recs"]:
            x["type"] = rewrite(x["type"], fM, {})
            for rl in x["rules"]:
                g = f23 if (names[x["name"]] == "WT.rec" and names[rl["ctor"]] == "WT.node") else fM
                rl["rhs"] = rewrite(rl["rhs"], g, {})
out = []
for r in recs:
    if "inductive" in r and any(names[t["name"]] == "WT" for t in r["inductive"]["types"]):
        out += new
    out.append(r)
with open(DST, "w") as f:
    for r in out:
        f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
