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
      fields).  0 (the per-major guard).
  primrec_type_prop_major     `T : Type | mk : Q → T`, `Q : Prop | intro`, the
      family into `Sort u` with a `Q` class.  0 (no universe restriction on
      majors; `Q` licenses it).  Bad twin: `Q : Prop | a | b` (small): 1.
  primrec_indexed_prop_major  `E (x : B) : B → Prop | refl : E x x` (large),
      `T : Type | mk : E B.x B.x → T`, a class `E B.x i`.  0 (the rule's
      index readings tie to the ι rule's index pin).  Bad twin: `E` with a
      second constructor `refl2 : E x x` (small): 1.
  primrec_tt_true             `Tr : Prop | intro`, `T (α : Prop) : Prop |
      mk : α → T α`; the family `T.rec` + classes `T (T Tr)`, `T Tr`,
      `Tr`, calling down that chain (STAGEFACT's false cycle, acyclic
      syntactically).  Today 0 (a member at other parameters is a class
      of its own, read at the block's own recorded clause).
  primrec_tt_true_bad         the same, `T (T Tr)`'s rule calling the `Tr`
      class on its field `h : T Tr`: the call's field is not a value of the
      callee's major.  1.
  primrec_extra_major_cyclic  `N | z | s : N → N`, `T : Type | mk : N → T`;
      the family `T.rec` + `T.rec_1` (major `N`), whose `s` rule calls
      itself.  A CYCLIC call graph (a flat home, lane FLATHOME): today 1
      (checked against the walk's auxiliary types: `N` names no member);
      TARGET 0.

  primrec_member_cycle_extra_major  `B | x | y`, `L : Type | nil | cons : B →
      L → L`; the family `L.rec` + `L.rec_1` (major `B`), whose `cons` rule
      calls `L.rec_1` on its `B` field and itself on its tail — a cycle
      through the block's OWN member (lane MEMBER: the installing block is
      a flat home).  Before the lane 1 (a member cycle was checked against
      the walk's auxiliary types, and `B` is none); TARGET 0.
  primrec_member_cycle_prop  `Q : Prop | intro`, `P : N → Prop | z : Q → P
      z | s n : P n → P (s n)`, the family `P.rec` + `P.rec_1` (major `Q`)
      into `Prop`, `s` calling itself.  Before the lane 1; TARGET 0.
  primrec_member_k53    `V : N → Type | mk0 : V z | mk n : V ((fun x => x)
      n) → V (s n)`, its own recursor as official generates it (the call's
      index the field's, redex kept).  0.  Bad twin (`_bad`): the call at
      index `n`, defeq to the field's but not official's (K.53 at a member
      call, now `Conformance/K53.lean`'s): 1.

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


def ind_type(s, name, ty, ctors, nparams=0, nested=0, isrec=False, lps=(), nidx=0):
    return {"all": [s.name(name)], "ctors": [s.name(x) for x in ctors], "isRec": isrec,
            "isReflexive": False, "isUnsafe": False, "levelParams": [s.name(l) for l in lps],
            "name": s.name(name), "numIndices": nidx, "numNested": nested, "numParams": nparams,
            "type": s.e(ty)}


def ctor(s, ind, name, ty, cidx, nfields, nparams=0, lps=()):
    return {"cidx": cidx, "induct": s.name(ind), "isUnsafe": False,
            "levelParams": [s.name(l) for l in lps], "name": s.name(name),
            "numFields": nfields, "numParams": nparams, "type": s.e(ty)}


def rec(s, allnames, name, ty, nmot, nmin, rules, lps=("u",), nparams=0, k=False, nidx=0):
    return {"all": [s.name(x) for x in allnames], "isUnsafe": False, "k": k,
            "levelParams": [s.name(l) for l in lps], "name": s.name(name), "numIndices": nidx,
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


def emit_tt_true(s, bad=False):
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
               app(v("mk_1"), v("h"),
                   app(c("T.rec_3" if bad else "T.rec_2"), *prev, v("h")))))],
            lps=(), nparams=1),
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


def emit_type_prop_major(s, bad):
    """`T : Type | mk : Q → T`, family `T.rec` + `T.rec_1` (major `Q`) into
    `Sort u`; `Q` licenses large elimination (`Q : Prop | intro`), the bad
    twin's `O : Prop | a | b` does not."""
    if bad:
        two_ctor(s, "Q", PROP, "Q.a", "Q.b")
        qmin = [("a", app(v("motive_1"), c("Q.a"))), ("b", app(v("motive_1"), c("Q.b")))]
        qrules = [("Q.a", 0, None), ("Q.b", 0, None)]
    else:
        unit_prop(s, "Q", "Q.intro")
        qmin = [("intro", app(v("motive_1"), c("Q.intro")))]
        qrules = [("Q.intro", 0, None)]
    T, Q = c("T"), c("Q")
    pre = [("motive", pis([("t", T)], SORTU)), ("motive_1", pis([("t", Q)], SORTU)),
           ("mk", pis([("q", Q), ("ih", app(v("motive_1"), v("q")))],
                      app(v("motive"), app(c("T.mk"), v("q")))))] + qmin
    prev = [v(x) for x, _ in pre]
    s.inductive([ind_type(s, "T", TYPE, ["T.mk"], nested=1)],
                [ctor(s, "T", "T.mk", pis([("q", Q)], T), 0, 1)],
                [rec(s, ["T"], "T.rec", pis(pre + [("t", T)], app(v("motive"), v("t"))), 2,
                     len(pre) - 2,
                     [("T.mk", 1, lams(pre + [("q", Q)],
                        app(v("mk"), v("q"), app(c("T.rec_1", U), *prev, v("q")))))]),
                 rec(s, ["T"], "T.rec_1", pis(pre + [("t", Q)], app(v("motive_1"), v("t"))), 2,
                     len(pre) - 2,
                     [(cn, 0, lams(pre, v(x))) for (cn, _, _), (x, _) in zip(qrules, qmin)])])


def emit_indexed_prop_major(s, bad=False):
    """`E (x : B) : B → Prop | refl : E x x` (large, K), `T : Type | mk :
    E B.x B.x → T`, family `T.rec` + `T.rec_1` (major `E B.x i`).  Bad:
    `E` has a second constructor `refl2 : E x x` (small), the family the
    same with a `refl2` rule."""
    two_ctor(s, "B", TYPE, "B.x", "B.y")
    B = c("B")
    Ex = lambda x, i: app(c("E"), x, i)
    ectors = ["E.refl", "E.refl2"] if bad else ["E.refl"]
    emsort = PROP if bad else SORTU
    epre = [("x", B), ("motive", pis([("i", B), ("t", Ex(v("x"), v("i")))], emsort))] + [
        (n.split(".")[-1], app(v("motive"), v("x"), app(c(n), v("x")))) for n in ectors]
    s.inductive([ind_type(s, "E", pis([("x", B), ("i", B)], PROP), ectors, nparams=1,
                          nidx=1)],
                [ctor(s, "E", n, pis([("x", B)], Ex(v("x"), v("x"))), k, 0, nparams=1)
                 for k, n in enumerate(ectors)],
                [rec(s, ["E"], "E.rec", pis(epre + [("i", B), ("t", Ex(v("x"), v("i")))],
                                            app(v("motive"), v("i"), v("t"))), 1, len(ectors),
                     [(n, 0, lams(epre, v(n.split(".")[-1]))) for n in ectors], nparams=1,
                     k=not bad, nidx=1, lps=() if bad else ("u",))])
    T, bx = c("T"), c("B.x")
    pre = [("motive", pis([("t", T)], SORTU)),
           ("motive_1", pis([("i", B), ("t", Ex(bx, v("i")))], SORTU)),
           ("mk", pis([("h", Ex(bx, bx)), ("ih", app(v("motive_1"), bx, v("h")))],
                      app(v("motive"), app(c("T.mk"), v("h")))))] + [
        (n.split(".")[-1] + "_1", app(v("motive_1"), bx, app(c(n), bx))) for n in ectors]
    prev = [v(x) for x, _ in pre]
    nmin = 1 + len(ectors)
    s.inductive([ind_type(s, "T", TYPE, ["T.mk"], nested=1)],
                [ctor(s, "T", "T.mk", pis([("h", Ex(bx, bx))], T), 0, 1)],
                [rec(s, ["T"], "T.rec", pis(pre + [("t", T)], app(v("motive"), v("t"))), 2, nmin,
                     [("T.mk", 1, lams(pre + [("h", Ex(bx, bx))],
                        app(v("mk"), v("h"), app(c("T.rec_1", U), *prev, bx, v("h")))))]),
                 rec(s, ["T"], "T.rec_1", pis(pre + [("i", B), ("t", Ex(bx, v("i")))],
                                              app(v("motive_1"), v("i"), v("t"))), 2, nmin,
                     [(n, 0, lams(pre, v(n.split(".")[-1] + "_1"))) for n in ectors], nidx=1)])


def emit_flat_acc(s, large, bad=False):
    """An older ACC-shaped home, `A (α : Type) (r : α → α → Prop) : α → Prop |
    intro x : (∀ y, r y x → A α r y) → A α r x` (large elimination), and
    `T (α) (r) (x) : Prop | mk : A α r x → T α r x` with the family `T.rec`
    + `T.rec_1` (class `A α r a`), whose `intro` rule calls `T.rec_1` on the
    REFLEXIVE field around the home's cycle (lane FLATHOME), into `Prop`
    or (`large`) into `Sort u`.  Bad: `A` has a second constructor `stop x :
    A α r x` (small elimination), the family into `Sort u`: the class `A α r a`
    licenses no large elimination."""
    a, r, x = v("α"), v("r"), v("x")
    Rty = pis([("a1", a), ("a2", a)], PROP)
    Aa = lambda al, rr, xx: app(c("A"), al, rr, xx)
    Hty = lambda xx: pis([("w", a), ("hw", app(r, v("w"), xx))], Aa(a, r, v("w")))
    actors = ["A.intro", "A.stop"] if bad else ["A.intro"]
    amsort = PROP if bad else SORTU
    alps = () if bad else ("u",)
    arn = (lambda n: c(n)) if bad else (lambda n: c(n, U))
    imin = ("intro", pis([("x", a), ("h", Hty(x)),
                          ("ih", pis([("y", a), ("hr", app(r, v("y"), x))],
                                     app(v("motive"), v("y"), app(v("h"), v("y"), v("hr")))))],
                         app(v("motive"), x, app(c("A.intro"), a, r, x, v("h")))))
    smin = ("stop", pis([("x", a)], app(v("motive"), x, app(c("A.stop"), a, r, x))))
    epre = [("α", TYPE), ("r", Rty), ("motive", pis([("i", a), ("t", Aa(a, r, v("i")))], amsort)),
            imin] + ([smin] if bad else [])
    eprev = [v(n) for n, _ in epre]
    arules = [("A.intro", 2, lams(epre + [("x", a), ("h", Hty(x))],
               app(v("intro"), x, v("h"),
                   lams([("y", a), ("hr", app(r, v("y"), x))],
                        app(arn("A.rec"), *eprev, v("y"), app(v("h"), v("y"), v("hr")))))))]
    if bad:
        arules.append(("A.stop", 1, lams(epre + [("x", a)], app(v("stop"), x))))
    s.inductive([ind_type(s, "A", pis([("α", TYPE), ("r", Rty), ("i", a)], PROP), actors,
                          nparams=2, nidx=1, isrec=True)],
                [ctor(s, "A", "A.intro", pis([("α", TYPE), ("r", Rty), ("x", a), ("h", Hty(x))],
                                             Aa(a, r, x)), 0, 2, nparams=2)] +
                ([ctor(s, "A", "A.stop", pis([("α", TYPE), ("r", Rty), ("x", a)], Aa(a, r, x)),
                       1, 1, nparams=2)] if bad else []),
                [rec(s, ["A"], "A.rec", pis(epre + [("i", a), ("t", Aa(a, r, v("i")))],
                                            app(v("motive"), v("i"), v("t"))), 1, len(actors),
                     arules, lps=alps, nparams=2, nidx=1)])
    Tx = app(c("T"), a, r, x)
    ms = SORTU if large else PROP
    lps = ("u",) if large else ()
    rn = (lambda n: c(n, U)) if large else (lambda n: c(n))
    mins = [("mk", pis([("h", Aa(a, r, x)), ("ih", app(v("motive_1"), x, v("h")))],
                       app(v("motive"), app(c("T.mk"), a, r, x, v("h"))))),
            ("intro", pis([("y", a), ("h", Hty(v("y"))),
                           ("ih", pis([("z", a), ("hr", app(r, v("z"), v("y")))],
                                      app(v("motive_1"), v("z"), app(v("h"), v("z"), v("hr")))))],
                          app(v("motive_1"), v("y"), app(c("A.intro"), a, r, v("y"), v("h")))))]
    if bad:
        mins.append(("stop", pis([("y", a)], app(v("motive_1"), v("y"),
                                                 app(c("A.stop"), a, r, v("y"))))))
    pre = [("α", TYPE), ("r", Rty), ("x", a), ("motive", pis([("t", Tx)], ms)),
           ("motive_1", pis([("i", a), ("t", Aa(a, r, v("i")))], ms))] + mins
    prev = [v(n) for n, _ in pre]
    r1 = [("A.intro", 2, lams(pre + [("y", a), ("h", Hty(v("y")))],
           app(v("intro"), v("y"), v("h"),
               lams([("z", a), ("hr", app(r, v("z"), v("y")))],
                    app(rn("T.rec_1"), *prev, v("z"), app(v("h"), v("z"), v("hr")))))))]
    if bad:
        r1.append(("A.stop", 1, lams(pre + [("y", a)], app(v("stop"), v("y")))))
    s.inductive([ind_type(s, "T", pis([("α", TYPE), ("r", Rty), ("x", a)], PROP), ["T.mk"],
                          nparams=3, nested=1)],
                [ctor(s, "T", "T.mk", pis([("α", TYPE), ("r", Rty), ("x", a), ("h", Aa(a, r, x))],
                                          Tx), 0, 1, nparams=3)],
                [rec(s, ["T"], "T.rec", pis(pre + [("t", Tx)], app(v("motive"), v("t"))), 2,
                     len(mins),
                     [("T.mk", 1, lams(pre + [("h", Aa(a, r, x))],
                        app(v("mk"), v("h"), app(rn("T.rec_1"), *prev, x, v("h")))))],
                     lps=lps, nparams=3),
                 rec(s, ["T"], "T.rec_1", pis(pre + [("i", a), ("t", Aa(a, r, v("i")))],
                                              app(v("motive_1"), v("i"), v("t"))), 2, len(mins),
                     r1, lps=lps, nparams=3, nidx=1)])


def emit_flat_mutual(s):
    """An older MUTUAL Prop block `Ev Od : N → Prop | ez : Ev z | es i : Od
    i → Ev (s i) | os i : Ev i → Od (s i)` with its own recursors, and `T (n
    : N) : Prop | mk : Ev n → T n` with the family `T.rec` + `T.rec_1`
    (class `Ev i`) + `T.rec_2` (class `Od i`), whose rules call around the
    older block's cycle (lane FLATHOME), into `Prop`."""
    N, z, sN = c("N"), c("N.z"), (lambda n: app(c("N.s"), n))
    npre = [("motive", pis([("t", N)], SORTU)), ("z", app(v("motive"), z)),
            ("s", pis([("n", N), ("ih", app(v("motive"), v("n")))],
                      app(v("motive"), sN(v("n")))))]
    nprev = [v(x) for x, _ in npre]
    s.inductive([ind_type(s, "N", TYPE, ["N.z", "N.s"], isrec=True)],
                [ctor(s, "N", "N.z", N, 0, 0), ctor(s, "N", "N.s", pis([("n", N)], N), 1, 1)],
                [rec(s, ["N"], "N.rec", pis(npre + [("t", N)], app(v("motive"), v("t"))), 1, 2,
                     [("N.z", 0, lams(npre, v("z"))),
                      ("N.s", 1, lams(npre + [("n", N)],
                        app(v("s"), v("n"), app(c("N.rec", U), *nprev, v("n")))))])])
    Ev, Od = (lambda i: app(c("Ev"), i)), (lambda i: app(c("Od"), i))
    m1, m2 = v("motive_1"), v("motive_2")
    mins = [("ez", app(m1, z, c("Ev.ez"))),
            ("es", pis([("i", N), ("h", Od(v("i"))), ("ih", app(m2, v("i"), v("h")))],
                       app(m1, sN(v("i")), app(c("Ev.es"), v("i"), v("h"))))),
            ("os", pis([("i", N), ("h", Ev(v("i"))), ("ih", app(m1, v("i"), v("h")))],
                       app(m2, sN(v("i")), app(c("Od.os"), v("i"), v("h")))))]
    mots = [("motive_1", pis([("i", N), ("t", Ev(v("i")))], PROP)),
            ("motive_2", pis([("i", N), ("t", Od(v("i")))], PROP))]
    epre = mots + mins
    eprev = [v(n) for n, _ in epre]
    ti = [ind_type(s, "Ev", pis([("i", N)], PROP), ["Ev.ez", "Ev.es"], nidx=1, isrec=True),
          ind_type(s, "Od", pis([("i", N)], PROP), ["Od.os"], nidx=1, isrec=True)]
    for t in ti:
        t["all"] = [s.name("Ev"), s.name("Od")]
    s.inductive(ti,
                [ctor(s, "Ev", "Ev.ez", Ev(z), 0, 0),
                 ctor(s, "Ev", "Ev.es", pis([("i", N), ("h", Od(v("i")))], Ev(sN(v("i")))), 1, 2),
                 ctor(s, "Od", "Od.os", pis([("i", N), ("h", Ev(v("i")))], Od(sN(v("i")))), 0, 2)],
                [rec(s, ["Ev", "Od"], "Ev.rec", pis(epre + [("i", N), ("t", Ev(v("i")))],
                                                    app(m1, v("i"), v("t"))), 2, 3,
                     [("Ev.ez", 0, lams(epre, v("ez"))),
                      ("Ev.es", 2, lams(epre + [("i", N), ("h", Od(v("i")))],
                        app(v("es"), v("i"), v("h"), app(c("Od.rec"), *eprev, v("i"), v("h")))))],
                     lps=(), nidx=1),
                 rec(s, ["Ev", "Od"], "Od.rec", pis(epre + [("i", N), ("t", Od(v("i")))],
                                                    app(m2, v("i"), v("t"))), 2, 3,
                     [("Od.os", 2, lams(epre + [("i", N), ("h", Ev(v("i")))],
                        app(v("os"), v("i"), v("h"), app(c("Ev.rec"), *eprev, v("i"), v("h")))))],
                     lps=(), nidx=1)])
    n = v("n")
    Tn = app(c("T"), n)
    pre = [("n", N), ("motive", pis([("t", Tn)], PROP))] + mots + [
        ("mk", pis([("h", Ev(n)), ("ih", app(m1, n, v("h")))],
                   app(v("motive"), app(c("T.mk"), n, v("h")))))] + mins
    prev = [v(x) for x, _ in pre]
    s.inductive([ind_type(s, "T", pis([("n", N)], PROP), ["T.mk"], nparams=1, nested=2)],
                [ctor(s, "T", "T.mk", pis([("n", N), ("h", Ev(n))], Tn), 0, 1, nparams=1)],
                [rec(s, ["T"], "T.rec", pis(pre + [("t", Tn)], app(v("motive"), v("t"))), 3, 4,
                     [("T.mk", 1, lams(pre + [("h", Ev(n))],
                        app(v("mk"), v("h"), app(c("T.rec_1"), *prev, n, v("h")))))],
                     lps=(), nparams=1),
                 rec(s, ["T"], "T.rec_1", pis(pre + [("i", N), ("t", Ev(v("i")))],
                                              app(m1, v("i"), v("t"))), 3, 4,
                     [("Ev.ez", 0, lams(pre, v("ez"))),
                      ("Ev.es", 2, lams(pre + [("i", N), ("h", Od(v("i")))],
                        app(v("es"), v("i"), v("h"), app(c("T.rec_2"), *prev, v("i"), v("h")))))],
                     lps=(), nparams=1, nidx=1),
                 rec(s, ["T"], "T.rec_2", pis(pre + [("i", N), ("t", Od(v("i")))],
                                              app(m2, v("i"), v("t"))), 3, 4,
                     [("Od.os", 2, lams(pre + [("i", N), ("h", Ev(v("i")))],
                        app(v("os"), v("i"), v("h"), app(c("T.rec_1"), *prev, v("i"), v("h")))))],
                     lps=(), nparams=1, nidx=1)])


def emit_nat(s):
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


def emit_member_cycle_extra_major(s):
    two_ctor(s, "B", TYPE, "B.x", "B.y")
    L, B = c("L"), c("B")
    pre = [("motive", pis([("t", L)], SORTU)), ("motive_1", pis([("t", B)], SORTU)),
           ("nil", app(v("motive"), c("L.nil"))),
           ("cons", pis([("b", B), ("l", L), ("ih_b", app(v("motive_1"), v("b"))),
                         ("ih", app(v("motive"), v("l")))],
                        app(v("motive"), app(c("L.cons"), v("b"), v("l"))))),
           ("x", app(v("motive_1"), c("B.x"))), ("y", app(v("motive_1"), c("B.y")))]
    prev = [v(x) for x, _ in pre]
    s.inductive([ind_type(s, "L", TYPE, ["L.nil", "L.cons"], isrec=True, nested=1)],
                [ctor(s, "L", "L.nil", L, 0, 0),
                 ctor(s, "L", "L.cons", pis([("b", B), ("l", L)], L), 1, 2)],
                [rec(s, ["L"], "L.rec", pis(pre + [("t", L)], app(v("motive"), v("t"))), 2, 4,
                     [("L.nil", 0, lams(pre, v("nil"))),
                      ("L.cons", 2, lams(pre + [("b", B), ("l", L)],
                        app(v("cons"), v("b"), v("l"), app(c("L.rec_1", U), *prev, v("b")),
                            app(c("L.rec", U), *prev, v("l")))))]),
                 rec(s, ["L"], "L.rec_1", pis(pre + [("t", B)], app(v("motive_1"), v("t"))), 2, 4,
                     [("B.x", 0, lams(pre, v("x"))), ("B.y", 0, lams(pre, v("y")))])])


def emit_member_cycle_prop(s):
    emit_nat(s)
    unit_prop(s, "Q", "Q.intro")
    N, Q = c("N"), c("Q")
    Pn = lambda i: app(c("P"), i)
    m, m1 = v("motive"), v("motive_1")
    pre = [("motive", pis([("i", N), ("t", Pn(v("i")))], PROP)),
           ("motive_1", pis([("t", Q)], PROP)),
           ("z", pis([("q", Q), ("ih", app(m1, v("q")))],
                     app(m, c("N.z"), app(c("P.z"), v("q"))))),
           ("s", pis([("n", N), ("h", Pn(v("n"))), ("ih", app(m, v("n"), v("h")))],
                     app(m, app(c("N.s"), v("n")), app(c("P.s"), v("n"), v("h"))))),
           ("intro", app(m1, c("Q.intro")))]
    prev = [v(x) for x, _ in pre]
    s.inductive([ind_type(s, "P", pis([("i", N)], PROP), ["P.z", "P.s"], nidx=1, isrec=True,
                          nested=1)],
                [ctor(s, "P", "P.z", pis([("q", Q)], Pn(c("N.z"))), 0, 1),
                 ctor(s, "P", "P.s", pis([("n", N), ("h", Pn(v("n")))],
                                         Pn(app(c("N.s"), v("n")))), 1, 2)],
                [rec(s, ["P"], "P.rec", pis(pre + [("i", N), ("t", Pn(v("i")))],
                                            app(m, v("i"), v("t"))), 2, 3,
                     [("P.z", 1, lams(pre + [("q", Q)],
                        app(v("z"), v("q"), app(c("P.rec_1"), *prev, v("q"))))),
                      ("P.s", 2, lams(pre + [("n", N), ("h", Pn(v("n")))],
                        app(v("s"), v("n"), v("h"), app(c("P.rec"), *prev, v("n"), v("h")))))],
                     lps=(), nidx=1),
                 rec(s, ["P"], "P.rec_1", pis(pre + [("t", Q)], app(m1, v("t"))), 2, 3,
                     [("Q.intro", 0, lams(pre, v("intro")))], lps=())])


def emit_member_k53(s, bad=False):
    emit_nat(s)
    N = c("N")
    Vn = lambda i: app(c("V"), i)
    red = lambda n: app(("lam", "x", N, v("x")), n)
    m = v("motive")
    pre = [("motive", pis([("i", N), ("t", Vn(v("i")))], SORTU)),
           ("mk0", app(m, c("N.z"), c("V.mk0"))),
           ("mk", pis([("n", N), ("h", Vn(red(v("n")))), ("ih", app(m, red(v("n")), v("h")))],
                      app(m, app(c("N.s"), v("n")), app(c("V.mk"), v("n"), v("h")))))]
    prev = [v(x) for x, _ in pre]
    idx = v("n") if bad else red(v("n"))
    s.inductive([ind_type(s, "V", pis([("i", N)], TYPE), ["V.mk0", "V.mk"], nidx=1, isrec=True)],
                [ctor(s, "V", "V.mk0", Vn(c("N.z")), 0, 0),
                 ctor(s, "V", "V.mk", pis([("n", N), ("h", Vn(red(v("n"))))],
                                          Vn(app(c("N.s"), v("n")))), 1, 2)],
                [rec(s, ["V"], "V.rec", pis(pre + [("i", N), ("t", Vn(v("i")))],
                                            app(m, v("i"), v("t"))), 1, 2,
                     [("V.mk0", 0, lams(pre, v("mk0"))),
                      ("V.mk", 2, lams(pre + [("n", N), ("h", Vn(red(v("n"))))],
                        app(v("mk"), v("n"), v("h"), app(c("V.rec", U), *prev, idx, v("h")))))],
                     nidx=1)])


for fname, emit in [("primrec_extra_major_type.ndjson", emit_extra_major_type),
                    ("primrec_extra_major_prop.ndjson", lambda s: emit_extra_major_prop(s, False)),
                    ("primrec_extra_major_prop_large.ndjson",
                     lambda s: emit_extra_major_prop(s, True)),
                    ("primrec_tt_true.ndjson", emit_tt_true),
                    ("primrec_tt_true_bad.ndjson", lambda s: emit_tt_true(s, True)),
                    ("primrec_extra_major_cyclic.ndjson", emit_extra_major_cyclic),
                    ("primrec_type_prop_major.ndjson", lambda s: emit_type_prop_major(s, False)),
                    ("primrec_type_prop_major_bad.ndjson",
                     lambda s: emit_type_prop_major(s, True)),
                    ("primrec_indexed_prop_major.ndjson", emit_indexed_prop_major),
                    ("primrec_indexed_prop_major_bad.ndjson",
                     lambda s: emit_indexed_prop_major(s, True)),
                    ("primrec_flat_acc_prop.ndjson", lambda s: emit_flat_acc(s, False)),
                    ("primrec_flat_acc_large.ndjson", lambda s: emit_flat_acc(s, True)),
                    ("primrec_flat_acc_large_bad.ndjson",
                     lambda s: emit_flat_acc(s, True, True)),
                    ("primrec_flat_mutual_prop.ndjson", emit_flat_mutual),
                    ("primrec_member_cycle_extra_major.ndjson", emit_member_cycle_extra_major),
                    ("primrec_member_cycle_prop.ndjson", emit_member_cycle_prop),
                    ("primrec_member_k53.ndjson", emit_member_k53),
                    ("primrec_member_k53_bad.ndjson", lambda s: emit_member_k53(s, True))]:
    s = Stream()
    emit(s)
    s.dump(fname)
