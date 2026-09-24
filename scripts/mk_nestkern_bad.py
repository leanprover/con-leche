#!/usr/bin/env python3
"""Corner case of the uniform route's elimination guard at a nested
family (lane NESTKERN, finding F4 of lane NESTIND), forged from scratch:
official's export cannot carry a recursor family official does not
generate.

  corner_nestkern_f4_prop_aux_bad   a `Prop` block `P | mk : P` (one
      constructor, no field: on its own a large eliminator is allowed —
      the subsingleton criterion) whose family carries an auxiliary
      recursor `P.rec_1` on an OUTSIDE `Prop` inductive `O | a | b`
      (same universe, so the outside-major check's Q1 lets it through),
      both eliminating into `Sort u`.  `O.a` and `O.b` are two decodings
      of the one proof of `O`, and `P.rec_1` separates them: a large
      elimination out of a two-constructor proposition, which with proof
      irrelevance proves `False`.  The elimination guard's container bit
      must hold as soon as ANY checked major is outside the block (F4:
      the target check reads it off its own resolved majors), and then
      the family eliminates only into `Prop`.  Official rejects (it
      generates only `P.rec`).  TARGET 1.

Usage: scripts/mk_nestkern_bad.py   (writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


class Stream:
    def __init__(self):
        self.out = [{"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                              "format": {"version": "3.1.0"},
                              "lean": {"githash": "forged", "version": "4.29.1"}}}]
        self.names = {"": 0}
        self.levels = {("zero",): 0}
        self.exprs = {}

    def name(self, s):
        if s in self.names:
            return self.names[s]
        pre, _, last = s.rpartition(".")
        p = self.name(pre)
        i = len(self.names)
        self.names[s] = i
        self.out.append({"in": i, "str": {"pre": p, "str": last}})
        return i

    def lvl(self, l):
        if l in self.levels:
            return self.levels[l]
        if l[0] == "param":
            rec = {"param": self.name(l[1])}
        elif l[0] == "succ":
            rec = {"succ": self.lvl(l[1])}
        elif l[0] == "max":
            rec = {"max": [self.lvl(l[1]), self.lvl(l[2])]}
        else:
            raise ValueError(l)
        i = len(self.levels)
        self.levels[l] = i
        self.out.append(dict(rec, il=i))
        return i

    def node(self, rec):
        k = json.dumps(rec, sort_keys=True)
        if k in self.exprs:
            return self.exprs[k]
        i = len(self.exprs)
        self.exprs[k] = i
        self.out.append(dict(rec, ie=i))
        return i

    def e(self, t, ctx=()):
        tag = t[0]
        if tag == "v":
            pos = len(ctx) - 1 - list(reversed(ctx)).index(t[1]) if t[1] in ctx else None
            if pos is None:
                raise ValueError("unbound " + t[1])
            return self.node({"bvar": len(ctx) - 1 - pos})
        if tag == "c":
            return self.node({"const": {"name": self.name(t[1]),
                                        "us": [self.lvl(u) for u in t[2]]}})
        if tag == "sort":
            return self.node({"sort": self.lvl(t[1])})
        if tag == "app":
            f = self.e(t[1], ctx)
            for a in t[2:]:
                f = self.node({"app": {"fn": f, "arg": self.e(a, ctx)}})
            return f
        if tag in ("pi", "lam"):
            _, x, ty, body = t[:4]
            bi = t[4] if len(t) > 4 else "default"
            k = "forallE" if tag == "pi" else "lam"
            return self.node({k: {"binderInfo": bi, "name": self.name(x),
                                  "type": self.e(ty, ctx),
                                  "body": self.e(body, ctx + (x,))}})
        raise ValueError(t)

    def inductive(self, types, ctors, recs):
        self.out.append({"inductive": {"types": types, "ctors": ctors, "recs": recs}})

    def dump(self, fname):
        p = os.path.join(ROOT, "tests/e2e", fname)
        with open(p, "w") as f:
            for r in self.out:
                f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
        print("%s: %d lines" % (fname, len(self.out)))


# --- the term language ----------------------------------------------
Z = ("zero",)
ONE = ("succ", Z)
U = ("param", "u")


def c(n, *us):
    return ("c", n, list(us))


def v(x):
    return ("v", x)


def app(f, *a):
    return ("app", f) + a


def pis(bs, body):
    for x, ty in reversed(bs):
        body = ("pi", x, ty, body)
    return body


def lams(bs, body):
    for x, ty in reversed(bs):
        body = ("lam", x, ty, body)
    return body


TYPE = ("sort", ONE)
PROP = ("sort", Z)
SORTU = ("sort", U)


def ind_type(s, name, ty, ctors, nparams=0, nested=0, isrec=False, lps=()):
    return {"all": [s.name(name)], "ctors": [s.name(x) for x in ctors], "isRec": isrec,
            "isReflexive": False, "isUnsafe": False, "levelParams": [s.name(l) for l in lps],
            "name": s.name(name), "numIndices": 0, "numNested": nested, "numParams": nparams,
            "type": s.e(ty)}


def ctor(s, ind, name, ty, cidx, nfields, nparams=0, lps=()):
    return {"cidx": cidx, "induct": s.name(ind), "isUnsafe": False,
            "levelParams": [s.name(l) for l in lps], "name": s.name(name),
            "numFields": nfields, "numParams": nparams, "type": s.e(ty)}


def rec(s, allnames, name, ty, nmot, nmin, rules, lps=("u",), nparams=0, k=False):
    return {"all": [s.name(x) for x in allnames], "isUnsafe": False, "k": k,
            "levelParams": [s.name(l) for l in lps], "name": s.name(name), "numIndices": 0,
            "numMinors": nmin, "numMotives": nmot, "numParams": nparams,
            "rules": [{"ctor": s.name(cn), "nfields": nf, "rhs": s.e(rhs)} for cn, nf, rhs in rules],
            "type": s.e(ty)}




def emit_prop_aux(s):
    # O : Prop | a | b, with its own small recursor (into Prop)
    Oc = c("O")
    opre = [("motive", pis([("t", Oc)], PROP)),
            ("a", app(v("motive"), c("O.a"))), ("b", app(v("motive"), c("O.b")))]
    s.inductive([ind_type(s, "O", PROP, ["O.a", "O.b"])],
                [ctor(s, "O", "O.a", Oc, 0, 0), ctor(s, "O", "O.b", Oc, 1, 0)],
                [rec(s, ["O"], "O.rec", pis(opre + [("t", Oc)], app(v("motive"), v("t"))),
                     1, 2, [("O.a", 0, lams(opre, v("a"))), ("O.b", 0, lams(opre, v("b")))],
                     lps=())])
    # P : Prop | mk : P, with the family P.rec (major P) and P.rec_1 (major O),
    # both into Sort u
    P = c("P")
    pre = [("motive", pis([("t", P)], SORTU)), ("motive_1", pis([("t", Oc)], SORTU)),
           ("mk", app(v("motive"), c("P.mk"))),
           ("a_1", app(v("motive_1"), c("O.a"))), ("b_1", app(v("motive_1"), c("O.b")))]
    s.inductive([ind_type(s, "P", PROP, ["P.mk"], nested=1)],
                [ctor(s, "P", "P.mk", P, 0, 0)],
                [rec(s, ["P"], "P.rec", pis(pre + [("t", P)], app(v("motive"), v("t"))), 2, 3,
                     [("P.mk", 0, lams(pre, v("mk")))]),
                 rec(s, ["P"], "P.rec_1", pis(pre + [("t", Oc)], app(v("motive_1"), v("t"))),
                     2, 3, [("O.a", 0, lams(pre, v("a_1"))), ("O.b", 0, lams(pre, v("b_1")))])])


s = Stream(); emit_prop_aux(s); s.dump("corner_nestkern_f4_prop_aux_bad.ndjson")
