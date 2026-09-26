#!/usr/bin/env python3
"""PRIMREC fixtures (lane DERCORE): recursor families official never
generates, forged from scratch (official's export cannot carry a family
it does not generate; official rejects every one of them).  The target
(`_tmp/primrec/PLAN.md`): the recursor check accepts ALL primitive-
recursive families — majors any inductive instances, calls on fields of
major type, the only soundness guard the per-major large-elimination
licence.

  primrec_extra_major_type    `B | x | y`, `T : Type | mk : B → T`; the
      family `T.rec` + `T.rec_1` (major `B`), `T.mk`'s rule calling
      `T.rec_1` on its field.  An acyclic call graph: today 0.
  primrec_extra_major_prop    `Q : Prop | intro`, `T : Prop | mk : Q → T`;
      the family `T.rec` + `T.rec_1` (major `Q`) into `Prop`.  Today 0.
  primrec_extra_major_prop_large   the same family into `Sort u`: `T` and
      `Q` each license large elimination (one constructor, only proof
      fields).  Today 1 (the block-wide guard: an outside major sets the
      container bit, and a `Prop` block with it eliminates only into
      `Prop`); TARGET 0 (the per-major guard).
  primrec_tt_true             `Tr : Prop | intro`, `T (α : Prop) : Prop |
      mk : α → T α`; the family `T.rec` + classes `T (T Tr)`, `T Tr`,
      `Tr`, calling down that chain (STAGEFACT's false cycle, acyclic
      syntactically).  Today 1 (a member major only at the block's
      parameters); TARGET 0.
  primrec_extra_major_cyclic  `N | z | s : N → N`, `T : Type | mk : N → T`;
      the family `T.rec` + `T.rec_1` (major `N`), whose `s` rule calls
      itself.  A CYCLIC call graph (a flat home, lane FLATHOME): today 1
      (checked against the walk's auxiliary types: `N` names no member);
      TARGET 0.

Usage: scripts/mk_primrec_fixtures.py   (writes under tests/e2e/)
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






def two_ctor(s, name, sort, a, b):
    """`name : sort | a | b` with its own recursor into `Sort u`
    (`Prop` at a `Prop` sort: two constructors)."""
    X = c(name)
    msort = SORTU if sort == TYPE else PROP
    lps = ("u",) if sort == TYPE else ()
    pre = [("motive", pis([("t", X)], msort)),
           (a.split(".")[-1], app(v("motive"), c(a))), (b.split(".")[-1], app(v("motive"), c(b)))]
    s.inductive([ind_type(s, name, sort, [a, b])],
                [ctor(s, name, a, X, 0, 0), ctor(s, name, b, X, 1, 0)],
                [rec(s, [name], name + ".rec", pis(pre + [("t", X)], app(v("motive"), v("t"))),
                     1, 2, [(a, 0, lams(pre, v(a.split(".")[-1]))),
                            (b, 0, lams(pre, v(b.split(".")[-1])))], lps=lps)])


def unit_prop(s, name, intro):
    """`name : Prop | intro` with its own recursor into `Sort u`."""
    X = c(name)
    pre = [("motive", pis([("t", X)], SORTU)), ("intro", app(v("motive"), c(intro)))]
    s.inductive([ind_type(s, name, PROP, [intro])],
                [ctor(s, name, intro, X, 0, 0)],
                [rec(s, [name], name + ".rec", pis(pre + [("t", X)], app(v("motive"), v("t"))),
                     1, 1, [(intro, 0, lams(pre, v("intro")))], k=True)])


def emit_extra_major_type(s):
    two_ctor(s, "B", TYPE, "B.x", "B.y")
    T, B = c("T"), c("B")
    pre = [("motive", pis([("t", T)], SORTU)), ("motive_1", pis([("t", B)], SORTU)),
           ("mk", pis([("b", B), ("ih", app(v("motive_1"), v("b")))],
                      app(v("motive"), app(c("T.mk"), v("b"))))),
           ("x", app(v("motive_1"), c("B.x"))), ("y", app(v("motive_1"), c("B.y")))]
    prev = [v(x) for x, _ in pre]
    s.inductive([ind_type(s, "T", TYPE, ["T.mk"], nested=1)],
                [ctor(s, "T", "T.mk", pis([("b", B)], T), 0, 1)],
                [rec(s, ["T"], "T.rec", pis(pre + [("t", T)], app(v("motive"), v("t"))), 2, 3,
                     [("T.mk", 1, lams(pre + [("b", B)],
                        app(v("mk"), v("b"), app(c("T.rec_1", U), *prev, v("b")))))]),
                 rec(s, ["T"], "T.rec_1", pis(pre + [("t", B)], app(v("motive_1"), v("t"))), 2, 3,
                     [("B.x", 0, lams(pre, v("x"))), ("B.y", 0, lams(pre, v("y")))])])


def emit_extra_major_prop(s, large):
    unit_prop(s, "Q", "Q.intro")
    T, Q = c("T"), c("Q")
    ms = SORTU if large else PROP
    lps = ("u",) if large else ()
    rn = (lambda n: c(n, U)) if large else (lambda n: c(n))
    pre = [("motive", pis([("t", T)], ms)), ("motive_1", pis([("t", Q)], ms)),
           ("mk", pis([("q", Q), ("ih", app(v("motive_1"), v("q")))],
                      app(v("motive"), app(c("T.mk"), v("q"))))),
           ("intro", app(v("motive_1"), c("Q.intro")))]
    prev = [v(x) for x, _ in pre]
    s.inductive([ind_type(s, "T", PROP, ["T.mk"], nested=1)],
                [ctor(s, "T", "T.mk", pis([("q", Q)], T), 0, 1)],
                [rec(s, ["T"], "T.rec", pis(pre + [("t", T)], app(v("motive"), v("t"))), 2, 2,
                     [("T.mk", 1, lams(pre + [("q", Q)],
                        app(v("mk"), v("q"), app(rn("T.rec_1"), *prev, v("q")))))], lps=lps),
                 rec(s, ["T"], "T.rec_1", pis(pre + [("t", Q)], app(v("motive_1"), v("t"))), 2, 2,
                     [("Q.intro", 0, lams(pre, v("intro")))], lps=lps)])


def emit_tt_true(s):
    X = c("Tr")
    tpre = [("motive", pis([("t", X)], PROP)), ("intro", app(v("motive"), c("Tr.intro")))]
    s.inductive([ind_type(s, "Tr", PROP, ["Tr.intro"])],
                [ctor(s, "Tr", "Tr.intro", X, 0, 0)],
                [rec(s, ["Tr"], "Tr.rec", pis(tpre + [("t", X)], app(v("motive"), v("t"))),
                     1, 1, [("Tr.intro", 0, lams(tpre, v("intro")))], lps=(), k=True)])
    Ta = lambda a: app(c("T"), a)
    mkA = lambda a, h: app(c("T.mk"), a, h)
    K1, K2 = Ta(Ta(X)), Ta(X)
    pre = [("α", PROP),
           ("motive", pis([("t", Ta(v("α")))], PROP)),
           ("motive_1", pis([("t", K1)], PROP)),
           ("motive_2", pis([("t", K2)], PROP)),
           ("motive_3", pis([("t", X)], PROP)),
           ("mk", pis([("h", v("α"))], app(v("motive"), mkA(v("α"), v("h"))))),
           ("mk_1", pis([("h", K2), ("ih", app(v("motive_2"), v("h")))],
                        app(v("motive_1"), mkA(K2, v("h"))))),
           ("mk_2", pis([("h", X), ("ih", app(v("motive_3"), v("h")))],
                        app(v("motive_2"), mkA(X, v("h"))))),
           ("intro", app(v("motive_3"), c("Tr.intro")))]
    prev = [v(x) for x, _ in pre]
    recs = [
        rec(s, ["T"], "T.rec", pis(pre + [("t", Ta(v("α")))], app(v("motive"), v("t"))), 4, 4,
            [("T.mk", 1, lams(pre + [("h", v("α"))], app(v("mk"), v("h"))))], lps=(), nparams=1),
        rec(s, ["T"], "T.rec_1", pis(pre + [("t", K1)], app(v("motive_1"), v("t"))), 4, 4,
            [("T.mk", 1, lams(pre + [("h", K2)],
               app(v("mk_1"), v("h"), app(c("T.rec_2"), *prev, v("h")))))], lps=(), nparams=1),
        rec(s, ["T"], "T.rec_2", pis(pre + [("t", K2)], app(v("motive_2"), v("t"))), 4, 4,
            [("T.mk", 1, lams(pre + [("h", X)],
               app(v("mk_2"), v("h"), app(c("T.rec_3"), *prev, v("h")))))], lps=(), nparams=1),
        rec(s, ["T"], "T.rec_3", pis(pre + [("t", X)], app(v("motive_3"), v("t"))), 4, 4,
            [("Tr.intro", 0, lams(pre, v("intro")))], lps=(), nparams=1)]
    s.inductive([ind_type(s, "T", pis([("α", PROP)], PROP), ["T.mk"], nparams=1, nested=1)],
                [ctor(s, "T", "T.mk", pis([("α", PROP), ("h", v("α"))], Ta(v("α"))), 0, 1,
                      nparams=1)],
                recs)


def emit_extra_major_cyclic(s):
    N = c("N")
    npre = [("motive", pis([("t", N)], SORTU)), ("z", app(v("motive"), c("N.z"))),
            ("s", pis([("n", N), ("ih", app(v("motive"), v("n")))],
                      app(v("motive"), app(c("N.s"), v("n")))))]
    nprev = [v(x) for x, _ in npre]
    s.inductive([ind_type(s, "N", TYPE, ["N.z", "N.s"], isrec=True)],
                [ctor(s, "N", "N.z", N, 0, 0), ctor(s, "N", "N.s", pis([("n", N)], N), 1, 1)],
                [rec(s, ["N"], "N.rec", pis(npre + [("t", N)], app(v("motive"), v("t"))), 1, 2,
                     [("N.z", 0, lams(npre, v("z"))),
                      ("N.s", 1, lams(npre + [("n", N)],
                        app(v("s"), v("n"), app(c("N.rec", U), *nprev, v("n")))))])])
    T = c("T")
    pre = [("motive", pis([("t", T)], SORTU)), ("motive_1", pis([("t", N)], SORTU)),
           ("mk", pis([("n", N), ("ih", app(v("motive_1"), v("n")))],
                      app(v("motive"), app(c("T.mk"), v("n"))))),
           ("z", app(v("motive_1"), c("N.z"))),
           ("s", pis([("n", N), ("ih", app(v("motive_1"), v("n")))],
                     app(v("motive_1"), app(c("N.s"), v("n")))))]
    prev = [v(x) for x, _ in pre]
    s.inductive([ind_type(s, "T", TYPE, ["T.mk"], nested=1)],
                [ctor(s, "T", "T.mk", pis([("n", N)], T), 0, 1)],
                [rec(s, ["T"], "T.rec", pis(pre + [("t", T)], app(v("motive"), v("t"))), 2, 3,
                     [("T.mk", 1, lams(pre + [("n", N)],
                        app(v("mk"), v("n"), app(c("T.rec_1", U), *prev, v("n")))))]),
                 rec(s, ["T"], "T.rec_1", pis(pre + [("t", N)], app(v("motive_1"), v("t"))), 2, 3,
                     [("N.z", 0, lams(pre, v("z"))),
                      ("N.s", 1, lams(pre + [("n", N)],
                        app(v("s"), v("n"), app(c("T.rec_1", U), *prev, v("n")))))])])


for fname, emit in [("primrec_extra_major_type.ndjson", emit_extra_major_type),
                    ("primrec_extra_major_prop.ndjson", lambda s: emit_extra_major_prop(s, False)),
                    ("primrec_extra_major_prop_large.ndjson",
                     lambda s: emit_extra_major_prop(s, True)),
                    ("primrec_tt_true.ndjson", emit_tt_true),
                    ("primrec_extra_major_cyclic.ndjson", emit_extra_major_cyclic)]:
    s = Stream()
    emit(s)
    s.dump(fname)
