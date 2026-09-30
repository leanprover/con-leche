#!/usr/bin/env python3
"""Forge `corner_nestind_f18_bare_bad` (lane NESTIND s27, finding F18) from
its good twin `corner_nestind_f18_bare_free` (source
`tests/e2e/src/corner_nestind_f18_bare_free.lean`).

The good twin: `C (α) | mk : Wrap C → C α` (`C` UNAPPLIED inside the
phantom `Wrap`) nested in `T | mk : C T → Wrap (fun _ => T) → T`; its
family carries `T.rec_2` on the class `Wrap (fun _ => T)`.  The forged
stream replaces the λ `fun _ => T` by the constant `C` throughout `T`'s
block: `T.mk`'s second field, and `T.rec_2`'s major, become `Wrap C` —
the class of the node the walk of `C`'s frame at `[T]` would visit at
`Wrap H` (`H` the frame's bare hole), whose parameters name no member of
`T` (official's `is_nested` rejects it as a major).

Usage: scripts/mk_nestind_f18_bad.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = os.path.join(ROOT, "tests/e2e/corner_nestind_f18_bare_free.ndjson")
DST = os.path.join(ROOT, "tests/e2e/corner_nestind_f18_bare_bad.ndjson")

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


def const_of(n):
    cs = [i for i, e in E.items() if "const" in e and names[e["const"]["name"]] == n
          and e["const"]["us"] == []]
    assert len(cs) == 1, (n, cs)
    return cs[0]


cT, cC = const_of("T"), const_of("C")
lams = [i for i, e in E.items() if "lam" in e and e["lam"]["body"] == cT]
assert len(lams) == 1, lams
lam = lams[0]


def f(i):
    return cC if i == lam else None


memo = {}
for r in recs:
    ind = r.get("inductive")
    if ind and any(names[t["name"]] == "T" for t in ind["types"]):
        for t in ind["types"]:
            t["type"] = rewrite(t["type"], f, memo)
        for c in ind["ctors"]:
            c["type"] = rewrite(c["type"], f, memo)
        for x in ind["recs"]:
            x["type"] = rewrite(x["type"], f, memo)
            for rl in x["rules"]:
                rl["rhs"] = rewrite(rl["rhs"], f, memo)
out = []
for r in recs:
    if "inductive" in r and any(names[t["name"]] == "T" for t in r["inductive"]["types"]):
        out += new
    out.append(r)
with open(DST, "w") as fh:
    for r in out:
        fh.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
