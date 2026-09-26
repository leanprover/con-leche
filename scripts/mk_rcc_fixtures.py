#!/usr/bin/env python3
"""Forge the RCC corner cases (lane PRIMREC/RCC, 2026-09-26) from their good
twins.  RCC: a cyclic class-graph edge whose callee key only APPEARS through
the rec check's second-stage whnf (it does not occur in the instantiated
field), `_tmp/uniform-inds/STAGEFACT.md` §5.

  corner_rcc_loop_bad     from `corner_rcc_loop` (`T π | mk : Q (T π) → T π`,
      with `Skey π = S`, `whnf S = Q S` literally).  The nested key
      `Q (T π)` becomes `Q S` everywhere (constructor type, recursor types,
      rules), and the auxiliary minor's field `a : T π` becomes `a : S`
      with its IH retargeted to the `Q S` class itself (`motive_2`,
      `T.rec_1`): the family's class `Q S` calls ITSELF on `a : S`, the
      callee key being the whnf of `S`.  Official 1 (its recursors are
      generated: "No such recursor T.rec_1").
  corner_rcc_create_prop  from `corner_rcc_expose_prop`: every `Ap L` /
      `Ap.mk L` becomes `Ap (fun α => L α)` / `Ap.mk (fun α => L α)`, so the
      class `Ap (fun α => L α) T` calls `L T` on `f A`, a key CREATED by
      the β-step (`L T` does not occur in `(fun α => L α) T`).  Official 1
      ("arg #1 of '_nested.Ap_1.mk' contains a non valid occurrence":
      `replace_all_nested` is syntactic).
  corner_rcc_create_type  the same from `corner_rcc_expose_type`.

Usage: scripts/mk_rcc_fixtures.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
E2E = os.path.join(ROOT, "tests/e2e")


class Stream:
    def __init__(self, path):
        self.recs = [json.loads(l) for l in open(path)]
        self.names = {0: ""}
        self.E = {}
        for r in self.recs:
            if "in" in r:
                k = "str" if "str" in r else "num"
                pre = self.names[r[k]["pre"]]
                s = str(r[k][k if k == "str" else "i"])
                self.names[r["in"]] = (pre + "." if pre else "") + s
            if "ie" in r:
                self.E[r["ie"]] = r
        self.nxt = max(self.E) + 1
        self.new = []

    def mk(self, body):
        r = dict(body)
        r["ie"] = self.nxt
        self.nxt += 1
        self.new.append(r)
        self.E[r["ie"]] = r
        return r["ie"]

    def const(self, n):
        c = [i for i, e in self.E.items() if "const" in e and self.names[e["const"]["name"]] == n]
        assert len(c) == 1, (n, c)
        return c[0]

    def bvar(self, i):
        for j, e in self.E.items():
            if e.get("bvar") == i:
                return j
        return self.mk({"bvar": i})

    def rebuild(self, x, sub):
        """`x`'s node with children `sub` (a dict), new only if one changed."""
        for kind in ("app", "lam", "forallE"):
            if kind in x:
                if all(sub[k] == x[kind][k] for k in sub):
                    return x["ie"]
                d = dict(x[kind])
                d.update(sub)
                return self.mk({kind: d})
        return x["ie"]

    def block(self, name):
        return [r["inductive"] for r in self.recs if "inductive" in r
                and any(self.names[t["name"]] == name for t in r["inductive"]["types"])][0]

    def write(self, path, name):
        out = []
        for r in self.recs:
            if "inductive" in r and any(self.names[t["name"]] == name for t in r["inductive"]["types"]):
                out += self.new
            out.append(r)
        with open(path, "w") as f:
            for r in out:
                f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")


KIDS = (("app", ("fn", "arg"), None), ("lam", ("type", "body"), "body"),
        ("forallE", ("type", "body"), "body"))


def forge_loop():
    s = Stream(os.path.join(E2E, "corner_rcc_loop.ndjson"))
    E, names = s.E, s.names
    cT, cQ, cQmk = s.const("T"), s.const("Q"), s.const("Q.mk")
    cRec, cRec1 = s.const("T.rec"), s.const("T.rec_1")
    skey = [r for r in s.recs if "def" in r and names[r["def"]["name"]] == "Skey"][0]
    Sb = E[skey["def"]["value"]]["lam"]["body"]   # `S` with `π` loose as bvar 0

    def subst_pi(e, X, j=0, memo=None):
        """`Sb` with its loose `π` (bvar j under j binders) read as `bvar (X + j)`."""
        memo = {} if memo is None else memo
        if (e, j) in memo:
            return memo[(e, j)]
        x = E[e]
        if "bvar" in x:
            assert x["bvar"] <= j
            out = s.bvar(X + j) if x["bvar"] == j else e
        else:
            out = e
            for kind, keys, bind in KIDS:
                if kind in x:
                    out = s.rebuild(x, {k: subst_pi(x[kind][k], X, j + (k == bind), memo) for k in keys})
        memo[(e, j)] = out
        return out

    def isT(e):
        x = E[e]
        if "app" in x and x["app"]["fn"] == cT and "bvar" in E[x["app"]["arg"]]:
            return E[x["app"]["arg"]]["bvar"]
        return None

    def rw(e, memo, in_aux_rule):
        if e in memo:
            return memo[e]
        x = E[e]
        if "app" in x and x["app"]["fn"] in (cQ, cQmk) and isT(x["app"]["arg"]) is not None:
            out = s.mk({"app": {"fn": x["app"]["fn"], "arg": subst_pi(Sb, isT(x["app"]["arg"]))}})
        elif in_aux_rule and e == cRec:
            out = cRec1
        elif ("forallE" in x and isT(x["forallE"]["type"]) is not None
              and "forallE" in E[x["forallE"]["body"]]
              and names[E[x["forallE"]["body"]]["forallE"]["name"]].startswith("a_ih")):
            # the auxiliary minor  Π (a : T π) (a_ih : motive_1 a), motive_2 (Q.mk a)
            ih = E[x["forallE"]["body"]]["forallE"]
            ihty = E[ih["type"]]["app"]
            m1 = E[ihty["fn"]]["bvar"]                  # motive_1; motive_2 is one closer
            newih = dict(ih, type=s.mk({"app": {"fn": s.bvar(m1 - 1), "arg": ihty["arg"]}}),
                         body=rw(ih["body"], memo, in_aux_rule))
            out = s.mk({"forallE": dict(x["forallE"], type=subst_pi(Sb, isT(x["forallE"]["type"])),
                                        body=s.mk({"forallE": newih}))})
        elif "lam" in x and in_aux_rule and isT(x["lam"]["type"]) is not None:
            out = s.mk({"lam": dict(x["lam"], type=subst_pi(Sb, isT(x["lam"]["type"])),
                                    body=rw(x["lam"]["body"], memo, in_aux_rule))})
        else:
            out = e
            for kind, keys, _ in KIDS:
                if kind in x:
                    out = s.rebuild(x, {k: rw(x[kind][k], memo, in_aux_rule) for k in keys})
        memo[e] = out
        return out

    ind = s.block("T")
    m0, m1 = {}, {}
    for c in ind["ctors"]:
        c["type"] = rw(c["type"], m0, False)
    for x in ind["recs"]:
        x["type"] = rw(x["type"], m0, False)
        for rl in x["rules"]:
            aux = names[rl["ctor"]] == "Q.mk"
            rl["rhs"] = rw(rl["rhs"], m1 if aux else m0, aux)
    s.write(os.path.join(E2E, "corner_rcc_loop_bad.ndjson"), "T")


def forge_create(base, dst, sort):
    s = Stream(os.path.join(E2E, base + ".ndjson"))
    E = s.E
    cL = s.const("L")
    heads = (s.const("Ap"), s.const("Ap.mk"))
    srt = [i for i, e in E.items() if e.get("sort") == sort][0]
    alpha = [i for i, n in s.names.items() if n == "α"][0]
    lamL = s.mk({"lam": {"binderInfo": "default", "name": alpha, "type": srt,
                         "body": s.mk({"app": {"fn": cL, "arg": s.bvar(0)}})}})

    def rw(e, memo):
        if e in memo:
            return memo[e]
        x = E[e]
        if "app" in x and x["app"]["fn"] in heads and x["app"]["arg"] == cL:
            out = s.mk({"app": {"fn": x["app"]["fn"], "arg": lamL}})
        else:
            out = e
            for kind, keys, _ in KIDS:
                if kind in x:
                    out = s.rebuild(x, {k: rw(x[kind][k], memo) for k in keys})
        memo[e] = out
        return out

    ind = s.block("T")
    memo = {}
    for c in ind["ctors"]:
        c["type"] = rw(c["type"], memo)
    for x in ind["recs"]:
        x["type"] = rw(x["type"], memo)
        for rl in x["rules"]:
            rl["rhs"] = rw(rl["rhs"], memo)
    s.write(os.path.join(E2E, dst + ".ndjson"), "T")


forge_loop()
forge_create("corner_rcc_expose_prop", "corner_rcc_create_prop", 0)
forge_create("corner_rcc_expose_type", "corner_rcc_create_type", 1)
