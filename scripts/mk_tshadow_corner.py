#!/usr/bin/env python3
"""Corner cases of the TARGET recursor check (lane TSHADOW), forged from
scratch: official's export cannot carry a recursor family official does
not generate, and these are exactly such families.

Each stream is self-contained (the checker synthesises its own
prelude).  A small term language with NAMED variables is converted to
the export's de Bruijn records; expressions, levels and names are
hash-consed.

  corner_tshadow_aux_good   a NESTED block written by hand: `L α` (a
      list) and `Tr | node : L Tr → Tr` with the two-recursor family
      official generates (`Tr.rec`, `Tr.rec_1` on `L Tr`).  The target
      installer accepts it (nestPos + the classification-free check on
      the family).  TARGET 0.
  corner_tshadow_aux_nonfield_bad   the same, but `Tr.rec_1`'s `cons`
      rule recurses on `(fun x => x) t` — definitionally the field, so
      the rule types, but not the field itself: not a primitive
      recursion (the syntactic narrowing of 2026-09-22, kept).  Official rejects (the
      replay compares with the generated rule).  TARGET 1.
  corner_tshadow_aux_prop_bad   Q1 (a question for the maintainer): a
      NON-nested `Type` block `T | mk : T` whose family carries an
      auxiliary recursor `T.rec_1` on an OUTSIDE `Prop` inductive
      `P | a | b`, eliminating into `Sort u`.  The rules are primitive
      recursion on `P`'s constructors — and they are a large
      elimination out of a two-constructor proposition, which with proof
      irrelevance proves `False`.  The target check refuses an outside
      major in another universe than the block ("Q1").  Official
      rejects (it generates only `T.rec`).  TARGET 1 (by that ruling).
  corner_tshadow_aux_unreached   Q2 (a question for the maintainer):
      the same shape at an outside `Type` inductive `N | z | s (n : N)`
      the block never reaches.  Charter item 5 ("calls on fields of ANY
      inductive type") accepts it; official rejects it (not generated).
      TARGET 0 if item 5 is read literally.

Usage: scripts/mk_tshadow_corner.py   (writes under tests/e2e/)
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


# --- the list container L (α : Type) ---------------------------------
def emit_list(s):
    L = lambda a: app(c("L"), a)
    tyL = pis([("α", TYPE)], TYPE)
    nil = pis([("α", TYPE)], L(v("α")))
    cons = pis([("α", TYPE), ("head", v("α")), ("tail", L(v("α")))], L(v("α")))
    mot = pis([("t", L(v("α")))], SORTU)
    pre = [("α", TYPE), ("motive", mot),
           ("nil", app(v("motive"), app(c("L.nil"), v("α")))),
           ("cons", pis([("head", v("α")), ("tail", L(v("α"))),
                         ("tail_ih", app(v("motive"), v("tail")))],
                        app(v("motive"), app(c("L.cons"), v("α"), v("head"), v("tail")))))]
    recTy = pis(pre + [("t", L(v("α")))], app(v("motive"), v("t")))
    r_nil = lams(pre, v("nil"))
    r_cons = lams(pre + [("head", v("α")), ("tail", L(v("α")))],
                  app(v("cons"), v("head"), v("tail"),
                      app(c("L.rec", U), v("α"), v("motive"), v("nil"), v("cons"), v("tail"))))
    s.inductive([ind_type(s, "L", tyL, ["L.nil", "L.cons"], nparams=1, isrec=True)],
                [ctor(s, "L", "L.nil", nil, 0, 0, nparams=1),
                 ctor(s, "L", "L.cons", cons, 1, 2, nparams=1)],
                [rec(s, ["L"], "L.rec", recTy, 1, 2,
                     [("L.nil", 0, r_nil), ("L.cons", 2, r_cons)], nparams=1)])


# --- Tr | node : L Tr → Tr, with its two-recursor family ------------
def emit_tree(s, bad_nonfield=False):
    Tr = c("Tr")
    LTr = app(c("L"), Tr)
    pre = [("motive", pis([("t", Tr)], SORTU)),
           ("motive_1", pis([("t", LTr)], SORTU)),
           ("node", pis([("cs", LTr), ("cs_ih", app(v("motive_1"), v("cs")))],
                        app(v("motive"), app(c("Tr.node"), v("cs"))))),
           ("nil", app(v("motive_1"), app(c("L.nil"), Tr))),
           ("cons", pis([("head", Tr), ("tail", LTr),
                         ("head_ih", app(v("motive"), v("head"))),
                         ("tail_ih", app(v("motive_1"), v("tail")))],
                        app(v("motive_1"), app(c("L.cons"), Tr, v("head"), v("tail")))))]
    xs = [v(x) for x, _ in pre]
    recTy = pis(pre + [("t", Tr)], app(v("motive"), v("t")))
    rec1Ty = pis(pre + [("t", LTr)], app(v("motive_1"), v("t")))
    r_node = lams(pre + [("cs", LTr)],
                  app(v("node"), v("cs"), app(c("Tr.rec_1", U), *xs, v("cs"))))
    r_nil = lams(pre, v("nil"))
    # the bad twin recurses on `(fun x => x) tail`: definitionally the
    # field, so the rule TYPES, but not the field itself
    tail_call = app(lams([("x", LTr)], v("x")), v("tail")) if bad_nonfield else v("tail")
    r_cons = lams(pre + [("head", Tr), ("tail", LTr)],
                  app(v("cons"), v("head"), v("tail"),
                      app(c("Tr.rec", U), *xs, v("head")),
                      app(c("Tr.rec_1", U), *xs, tail_call)))
    s.inductive([ind_type(s, "Tr", TYPE, ["Tr.node"], nested=1, isrec=True)],
                [ctor(s, "Tr", "Tr.node", pis([("cs", LTr)], Tr), 0, 1)],
                [rec(s, ["Tr"], "Tr.rec", recTy, 2, 3, [("Tr.node", 1, r_node)]),
                 rec(s, ["Tr"], "Tr.rec_1", rec1Ty, 2, 3,
                     [("L.nil", 0, r_nil), ("L.cons", 2, r_cons)])])


# --- T | mk : T, with an auxiliary recursor on an OUTSIDE inductive --
def emit_outside(s, O, osort, octors):
    """`O : osort` with the given constructors `(name, fields)` (fields:
    list of (x, ty) at `O`), then `T | mk : T` with the family
    `T.rec` (major `T`) and `T.rec_1` (major `O`), both into `Sort u`."""
    # O itself, with its own (small, into Prop when O is a Prop) recursor
    Oc = c(O)
    om = [("motive", pis([("t", Oc)], PROP if osort == PROP else SORTU))]
    ominors = []
    for cn, fs in octors:
        ihs = [(x + "_ih", app(v("motive"), v(x))) for x, ty in fs if ty == Oc]
        ominors.append((cn.split(".")[-1],
                        pis(fs + ihs, app(v("motive"), app(c(cn), *[v(x) for x, _ in fs])))))
    olps = () if osort == PROP else ("u",)
    orec_us = [] if osort == PROP else [U]
    opre = om + ominors
    orules = []
    for (cn, fs), (mn, _) in zip(octors, ominors):
        calls = [app(c(O + ".rec", *orec_us), *[v(x) for x, _ in opre], v(x))
                 for x, ty in fs if ty == Oc]
        orules.append((cn, len(fs), lams(opre + fs, app(v(mn), *[v(x) for x, _ in fs], *calls))))
    s.inductive([ind_type(s, O, osort, [cn for cn, _ in octors],
                          isrec=any(ty == Oc for _, fs in octors for _, ty in fs))],
                [ctor(s, O, cn, pis(fs, Oc), i, len(fs)) for i, (cn, fs) in enumerate(octors)],
                [rec(s, [O], O + ".rec", pis(opre + [("t", Oc)], app(v("motive"), v("t"))),
                     1, len(octors), orules, lps=olps)])
    # T and its family
    T = c("T")
    pre = [("motive", pis([("t", T)], SORTU)), ("motive_1", pis([("t", Oc)], SORTU)),
           ("mk", app(v("motive"), c("T.mk")))]
    for cn, fs in octors:
        ihs = [(x + "_ih", app(v("motive_1"), v(x))) for x, ty in fs if ty == Oc]
        pre.append((cn.split(".")[-1] + "_1",
                    pis(fs + ihs, app(v("motive_1"), app(c(cn), *[v(x) for x, _ in fs])))))
    xs = [v(x) for x, _ in pre]
    rules1 = []
    for cn, fs in octors:
        calls = [app(c("T.rec_1", U), *xs, v(x)) for x, ty in fs if ty == Oc]
        rules1.append((cn, len(fs), lams(pre + fs, app(v(cn.split(".")[-1] + "_1"),
                                                      *[v(x) for x, _ in fs], *calls))))
    nmin = 1 + len(octors)
    # `numNested = 1`: the export schema counts one motive per type and
    # per auxiliary (the frontend validates `numMotives` against it)
    s.inductive([ind_type(s, "T", TYPE, ["T.mk"], nested=1)],
                [ctor(s, "T", "T.mk", T, 0, 0)],
                [rec(s, ["T"], "T.rec", pis(pre + [("t", T)], app(v("motive"), v("t"))), 2, nmin,
                     [("T.mk", 0, lams(pre, v("mk")))]),
                 rec(s, ["T"], "T.rec_1", pis(pre + [("t", Oc)], app(v("motive_1"), v("t"))), 2,
                     nmin, rules1)])


s = Stream(); emit_list(s); emit_tree(s); s.dump("corner_tshadow_aux_good.ndjson")
s = Stream(); emit_list(s); emit_tree(s, bad_nonfield=True)
s.dump("corner_tshadow_aux_nonfield_bad.ndjson")
s = Stream(); emit_outside(s, "P", PROP, [("P.a", []), ("P.b", [])])
s.dump("corner_tshadow_aux_prop_bad.ndjson")
s = Stream(); emit_outside(s, "N", TYPE, [("N.z", []), ("N.s", [("n", c("N"))])])
s.dump("corner_tshadow_aux_unreached.ndjson")
