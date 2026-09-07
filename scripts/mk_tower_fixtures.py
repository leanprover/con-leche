#!/usr/bin/env python3
"""Task #215: the adversarial DAG-tower fixtures that replaced the
frontend tree-size budget.

Each fixture puts a *shared* tower of depth 60 — about 2^60 nodes with
the sharing expanded, ~190 entries as a DAG — into one record kind the
frontend reads.  An unmemoized walk over any of them never finishes, so
the fixture is a gate on the walkers, not a limit on the user: a
regression makes a test hang instead of making a legitimate Mathlib
declaration decline.

The tower is `T_0 = Nat.zero`, `T_{k+1} = (K T_k) T_k` with
`K = fun (a b : Nat) => a`, so every `T_k` is defeq to `Nat.zero` and
the block really installs; only its *unshared* size explodes.

Usage: scripts/mk_tower_fixtures.py
"""
import gzip, json, os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
DEPTH = 60


class Stream:
    def __init__(self):
        self.L = [json.dumps({"meta": {"exporter": {"name": "mk_tower_fixtures.py",
                                                    "version": "1"}}})]
        self.N = {0: ""}
        self.nc = 0
        self.ec = 0
        self.lc = 0

    def name(self, pre, last):
        self.nc += 1
        self.L.append(json.dumps({"in": self.nc, "str": {"pre": pre, "str": last}}))
        return self.nc

    def lvl(self, obj):
        self.lc += 1
        self.L.append(json.dumps(dict(obj, il=self.lc)))
        return self.lc

    def ex(self, obj):
        self.ec += 1
        self.L.append(json.dumps(dict(obj, ie=self.ec)))
        return self.ec

    def write(self, path):
        p = os.path.join(ROOT, path)
        open(p, "w").write("\n".join(self.L) + "\n")
        print(f"{p}: {len(self.L)} lines")


def base(s, tyname="Big"):
    """Prelude names, the `Nat` tower, and `Sort` constants."""
    n = {}
    n["Eq"] = s.name(0, "Eq")
    n["Nat"] = s.name(0, "Nat")
    n["Nat.zero"] = s.name(n["Nat"], "zero")
    n["Eq.refl"] = s.name(n["Eq"], "refl")
    n["Quot"] = s.name(0, "Quot")
    n["Quot.sound"] = s.name(n["Quot"], "sound")
    n["T"] = s.name(0, tyname)
    n["T.mk"] = s.name(n["T"], "mk")
    n["T.rec"] = s.name(n["T"], "rec")
    n["u"] = s.name(0, "u")
    n["thm"] = s.name(0, "towerThm")
    lU = s.lvl({"param": n["u"]})
    lOne = s.lvl({"succ": 0})
    e = {}
    e["Prop"] = s.ex({"sort": 0})
    e["Type"] = s.ex({"sort": lOne})
    e["SortU"] = s.ex({"sort": lU})
    e["Nat"] = s.ex({"const": {"name": n["Nat"], "us": []}})
    e["zero"] = s.ex({"const": {"name": n["Nat.zero"], "us": []}})
    e["Eq"] = s.ex({"const": {"name": n["Eq"], "us": [lOne]}})
    b1 = s.ex({"bvar": 1})
    inner = s.ex({"lam": {"binderInfo": "default", "name": 0, "type": e["Nat"],
                          "body": b1}})
    e["K"] = s.ex({"lam": {"binderInfo": "default", "name": 0, "type": e["Nat"],
                           "body": inner}})
    t = e["zero"]
    for _ in range(DEPTH):
        half = s.ex({"app": {"fn": e["K"], "arg": t}})
        t = s.ex({"app": {"fn": half, "arg": t}})
    e["T"] = t
    # `@Eq Nat T T`, a Prop carrying the tower twice
    a1 = s.ex({"app": {"fn": e["Eq"], "arg": e["Nat"]}})
    a2 = s.ex({"app": {"fn": a1, "arg": t}})
    e["eqTy"] = s.ex({"app": {"fn": a2, "arg": t}})
    return n, e, lU, lOne


def block(s, n, e, lU, name_T, name_mk, name_rec):
    """`inductive T where | mk : (h : @Eq Nat T60 T60) → T`, with its
    recursor and iota rule — the field type carries the tower."""
    eT = s.ex({"const": {"name": name_T, "us": []}})
    eMkTy = s.ex({"forallE": {"binderInfo": "default", "name": 0,
                              "type": e["eqTy"], "body": eT}})
    eB0 = s.ex({"bvar": 0})
    eMotiveTy = s.ex({"forallE": {"binderInfo": "default", "name": 0,
                                  "type": eT, "body": e["SortU"]}})
    eMkC = s.ex({"const": {"name": name_mk, "us": []}})
    eMinor = s.ex({"forallE": {"binderInfo": "default", "name": 0,
                               "type": e["eqTy"],
                               "body": s.ex({"app": {"fn": s.ex({"bvar": 1}),
                                   "arg": s.ex({"app": {"fn": eMkC, "arg": eB0}})}})}})
    eRecTy = s.ex({"forallE": {"binderInfo": "implicit", "name": 0, "type": eMotiveTy,
        "body": s.ex({"forallE": {"binderInfo": "default", "name": 0, "type": eMinor,
        "body": s.ex({"forallE": {"binderInfo": "default", "name": 0, "type": eT,
        "body": s.ex({"app": {"fn": s.ex({"bvar": 2}), "arg": eB0}})}})}})}})
    eRhs = s.ex({"lam": {"binderInfo": "implicit", "name": 0, "type": eMotiveTy,
        "body": s.ex({"lam": {"binderInfo": "default", "name": 0, "type": eMinor,
        "body": s.ex({"lam": {"binderInfo": "default", "name": 0, "type": e["eqTy"],
        "body": s.ex({"app": {"fn": s.ex({"bvar": 1}), "arg": eB0}})}})}})}})
    s.L.append(json.dumps({"inductive": {
        "types": [{"name": name_T, "levelParams": [], "type": e["Type"],
                   "numParams": 0, "numIndices": 0, "numNested": 0,
                   "ctors": [name_mk], "isRec": False, "isUnsafe": False,
                   "isReflexive": False, "all": [name_T]}],
        "ctors": [{"name": name_mk, "levelParams": [], "type": eMkTy,
                   "numParams": 0, "numFields": 1, "cidx": 0, "induct": name_T,
                   "isUnsafe": False}],
        "recs": [{"name": name_rec, "levelParams": [n["u"]], "type": eRecTy,
                  "numParams": 0, "numMotives": 1, "numMinors": 1,
                  "numIndices": 0, "k": False, "isUnsafe": False,
                  "all": [name_T],
                  "rules": [{"ctor": name_mk, "nfields": 1, "rhs": eRhs}]}],
        "isUnsafe": False, "all": [name_T]}}))


def mk_struct():
    """The tower in a constructor FIELD TYPE of a structure block."""
    s = Stream(); n, e, lU, _ = base(s)
    block(s, n, e, lU, n["T"], n["T.mk"], n["T.rec"])
    s.write("tests/e2e/tower_struct.ndjson")


def mk_thm():
    """The tower in a THEOREM's type and value: `@Eq.refl Nat T60`."""
    s = Stream(); n, e, lU, lOne = base(s)
    eRefl = s.ex({"const": {"name": n["Eq.refl"], "us": [lOne]}})
    v1 = s.ex({"app": {"fn": eRefl, "arg": e["Nat"]}})
    v = s.ex({"app": {"fn": v1, "arg": e["T"]}})
    s.L.append(json.dumps({"thm": {"name": n["thm"], "levelParams": [],
                                   "type": e["eqTy"], "value": v,
                                   "all": [n["thm"]]}}))
    s.write("tests/e2e/tower_thm.ndjson")


def mk_prelude():
    """A record under a BUILT-IN PRELUDE name that differs from the
    prelude's — an inductive block named `Bool` whose constructor field
    type is the tower.  The prelude dedupe (`DeclC.sameCanon`) must
    reach its DECLINE without walking the tower."""
    s = Stream(); n, e, lU, _ = base(s, tyname="Bool")
    block(s, n, e, lU, n["T"], n["T.mk"], n["T.rec"])
    s.write("tests/e2e/tower_prelude.ndjson")


def mk_axiom():
    """The tower in an AXIOM's type, under the pinned name `Quot.sound`
    (a non-pinned axiom is declined on the name alone, so only a pinned
    one reaches `Expr.erasePw`/`ConstantInfo.canon`).  Must DECLINE."""
    s = Stream(); n, e, _, _ = base(s)
    s.L.append(json.dumps({"axiom": {"name": n["Quot.sound"], "levelParams": [],
                                     "type": e["eqTy"], "isUnsafe": False}}))
    s.write("tests/e2e/tower_axiom.ndjson")


def mk_quot():
    """The tower in a QUOTIENT record's type.  Must DECLINE (it is not
    the pinned `Quot`) without walking."""
    s = Stream(); n, e, _, _ = base(s)
    s.L.append(json.dumps({"quot": {"name": n["Quot"], "levelParams": [],
                                    "type": e["eqTy"], "kind": "type"}}))
    s.write("tests/e2e/tower_quot.ndjson")


def promote_budget_block():
    """`budget_block` was the depth-12 shape; the tower fixtures make it
    redundant, but keep it at depth 60 under its own name."""
    pass


mk_struct()
mk_thm()
mk_prelude()
mk_axiom()
mk_quot()
