#!/usr/bin/env python3
"""Forge WALKFREE's (S) example (lane PRIMREC/WFMEASURE, 2026-09-27) from
its good twin.

  primrec_nest_missing_class  from `primrec_nest_with_class`
      (`W α | a : α → W α | c : List α → W α`, `T | mk : W T → T`):
      the family becomes {T, W T} WITHOUT the `List T` class — `T.rec`
      and `T.rec_1` take the types of `Forge.rec0`/`Forge.rec1` (two
      motives, three minors; `W.c`'s minor takes no ih), their rules the
      values of `Forge.rhs0`/`rhs1a`/`rhs1c` with `Forge.rec0`/`rec1`
      renamed to `T.rec`/`T.rec_1`; `T.rec_2` and the `Forge.*`
      definitions are dropped.  Every term record is moved ahead of the
      declarations (the forged rules use terms the stream first built for
      the `Forge.*` definitions).

Usage: scripts/mk_wfmeasure_fixtures.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
E2E = os.path.join(ROOT, "tests/e2e")
KIDS = (("app", ("fn", "arg")), ("lam", ("type", "body")), ("forallE", ("type", "body")))


def forge(src, dst):
    recs = [json.loads(l) for l in open(os.path.join(E2E, src + ".ndjson"))]
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
    nid = {v: k for k, v in names.items()}
    nxt = [max(E) + 1]
    new = []

    def mk(body):
        r = dict(body)
        r["ie"] = nxt[0]
        nxt[0] += 1
        new.append(r)
        E[r["ie"]] = r
        return r["ie"]

    ren = {nid["Forge.rec0"]: nid["T.rec"], nid["Forge.rec1"]: nid["T.rec_1"]}

    def rw(e, memo):
        if e in memo:
            return memo[e]
        x = E[e]
        out = e
        if "const" in x and x["const"]["name"] in ren:
            out = mk({"const": dict(x["const"], name=ren[x["const"]["name"]])})
        else:
            for kind, keys in KIDS:
                if kind in x:
                    sub = {k: rw(x[kind][k], memo) for k in keys}
                    if any(sub[k] != x[kind][k] for k in keys):
                        d = dict(x[kind])
                        d.update(sub)
                        out = mk({kind: d})
        memo[e] = out
        return out

    defs = {names[r["def"]["name"]]: r["def"] for r in recs if "def" in r}
    ind = [r["inductive"] for r in recs if "inductive" in r
           and any(names[t["name"]] == "T" for t in r["inductive"]["types"])][0]
    byname = {names[x["name"]]: x for x in ind["recs"]}
    memo = {}
    r0, r1 = byname["T.rec"], byname["T.rec_1"]
    for x, d in ((r0, "Forge.rec0"), (r1, "Forge.rec1")):
        x.update(type=defs[d]["type"], numMotives=2, numMinors=3)
    r0["rules"] = [dict(r0["rules"][0], rhs=rw(defs["Forge.rhs0"]["value"], memo))]
    r1["rules"] = [dict(r1["rules"][0], rhs=rw(defs["Forge.rhs1a"]["value"], memo)),
                   dict(r1["rules"][1], rhs=rw(defs["Forge.rhs1c"]["value"], memo))]
    ind["recs"] = [x for x in ind["recs"] if names[x["name"]] != "T.rec_2"]
    terms = [r for r in recs if any(k in r for k in ("ie", "in", "il"))] + new
    decls = [r for r in recs if not any(k in r for k in ("ie", "in", "il", "meta"))
             and not ("def" in r and names[r["def"]["name"]].startswith("Forge."))]
    meta = [r for r in recs if "meta" in r]
    with open(os.path.join(E2E, dst + ".ndjson"), "w") as f:
        for r in meta + terms + decls:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")


forge("primrec_nest_with_class", "primrec_nest_missing_class")
