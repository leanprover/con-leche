#!/usr/bin/env python3
"""Forge streams that exhaust the level comparison's fuel
(`Level.defaultFuel`, `ConLeche/Kernel/Level.lean`).

`leqCore` takes fuel because its termination argument is nontrivial;
running out is OUR resource limit, so it must DECLINE (exit 2), never
reject (charter item 9).  The comparison peels one `max` per unit of
fuel along its left spine, so a level

    M = max (max (… (max u u) …) u) u        (FUEL + 1 nested `max`)

which `simplify` leaves alone (it only merges `succ`s) and which official
normalises to `u` (`level.cpp`, `normalize` flattens, sorts and dedups
`max` arguments) exhausts it at `isEquiv M u`.

  level_fuel_const   `inductive A.{u} : Type | mk : A`, then
      `def d.{u} : A.{M} := A.mk.{u}` — the defeq `A.{u} =?= A.{M}` is
      decided on the heads' level lists (A does not unfold).
  level_fuel_sort    `def s.{u} : Sort (M + 1) := Sort u` — the defeq
      `Sort (u+1) =?= Sort (M+1)` of two sorts.
  level_fuel_mutual  twin of `ind_mutual_sort_defeq`: `MD`'s sort
      `max v u` becomes the same value spelled `max (… (max v u) …) u`,
      so the block's universe agreement `isEquiv (max u v) L` (member
      0's sort against `MD`'s) exhausts the fuel.  Before lane SMALLFIX
      this was the one comparison whose exhaustion REJECTED (the check
      read `none` as "not equivalent"); the other two errored (exit 3).

Official (v4.34.0, `addDecl`, `_tmp/uniform-inds/SMALLFIX/probe/Fuel.lean`)
accepts all three.  TARGET 2.

Usage: scripts/mk_level_fuel.py   (writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
FUEL = 10000  # `Level.defaultFuel`
META = {"meta": {"exporter": {"name": "lean4export", "version": "3.1.0"},
                 "format": {"version": "3.1.0"},
                 "lean": {"githash": "f72c35b3f637c8c6571d353742168ab66cc22c00",
                          "version": "4.29.1"}}}


def dump(name, recs):
    p = os.path.join(ROOT, "tests/e2e", name)
    with open(p, "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s: %d lines" % (name, len(recs)))


class S:
    def __init__(self):
        self.recs = [META]
        self.n = 0
        self.l = 0
        self.e = -1

    def name(self, s, pre=0):
        self.n += 1
        self.recs.append({"in": self.n, "str": {"pre": pre, "str": s}})
        return self.n

    def lvl(self, **k):
        self.l += 1
        self.recs.append(dict({"il": self.l}, **k))
        return self.l

    def ex(self, **k):
        self.e += 1
        self.recs.append(dict(k, ie=self.e))
        return self.e

    def deep_max(self, u):
        m = self.lvl(max=[u, u])
        for _ in range(FUEL):
            m = self.lvl(max=[m, u])
        return m


def level_fuel_const():
    s = S()
    A = s.name("A")
    mk = s.name("mk", A)
    rec = s.name("rec", A)
    d = s.name("d")
    u = s.name("u")
    v = s.name("v")
    motive = s.name("motive")
    t = s.name("t")
    one = s.lvl(succ=0)
    lu = s.lvl(param=u)
    lv = s.lvl(param=v)
    ty = s.ex(sort=one)
    Au = s.ex(const={"name": A, "us": [lu]})
    mku = s.ex(const={"name": mk, "us": [lu]})
    sv = s.ex(sort=lv)
    mot_ty = s.ex(forallE={"binderInfo": "default", "name": t, "type": Au, "body": sv})
    b0 = s.ex(bvar=0)
    mot_mk = s.ex(app={"fn": b0, "arg": mku})
    b2 = s.ex(bvar=2)
    mot_t = s.ex(app={"fn": b2, "arg": b0})
    f_t = s.ex(forallE={"binderInfo": "default", "name": t, "type": Au, "body": mot_t})
    f_mk = s.ex(forallE={"binderInfo": "default", "name": mk, "type": mot_mk, "body": f_t})
    rec_ty = s.ex(forallE={"binderInfo": "implicit", "name": motive, "type": mot_ty,
                           "body": f_mk})
    l_mk = s.ex(lam={"binderInfo": "default", "name": mk, "type": mot_mk, "body": b0})
    rhs = s.ex(lam={"binderInfo": "default", "name": motive, "type": mot_ty, "body": l_mk})
    s.recs.append({"inductive": {
        "ctors": [{"cidx": 0, "induct": A, "isUnsafe": False, "levelParams": [u],
                   "name": mk, "numFields": 0, "numParams": 0, "type": Au}],
        "recs": [{"all": [A], "isUnsafe": False, "k": False, "levelParams": [v, u],
                  "name": rec, "numIndices": 0, "numMinors": 1, "numMotives": 1,
                  "numParams": 0, "rules": [{"ctor": mk, "nfields": 0, "rhs": rhs}],
                  "type": rec_ty}],
        "types": [{"all": [A], "ctors": [mk], "isRec": False, "isReflexive": False,
                   "isUnsafe": False, "levelParams": [u], "name": A, "numIndices": 0,
                   "numNested": 0, "numParams": 0, "type": ty}]}})
    m = s.deep_max(lu)
    AM = s.ex(const={"name": A, "us": [m]})
    s.recs.append({"def": {"all": [d], "hints": {"regular": 1}, "levelParams": [u],
                           "name": d, "safety": "safe", "type": AM, "value": mku}})
    dump("level_fuel_const.ndjson", s.recs)


def level_fuel_sort():
    s = S()
    d = s.name("s")
    u = s.name("u")
    lu = s.lvl(param=u)
    m = s.deep_max(lu)
    m1 = s.lvl(succ=m)
    ty = s.ex(sort=m1)
    val = s.ex(sort=lu)
    s.recs.append({"def": {"all": [d], "hints": {"regular": 1}, "levelParams": [u],
                           "name": d, "safety": "safe", "type": ty, "value": val}})
    dump("level_fuel_sort.ndjson", s.recs)


def level_fuel_mutual():
    src = os.path.join(ROOT, "tests/e2e/ind_mutual_sort_defeq.ndjson")
    recs = [json.loads(l) for l in open(src).read().splitlines()]
    i = next(k for k, r in enumerate(recs) if r.get("il") == 4)
    assert recs[i] == {"il": 4, "max": [2, 1]}, "MD's sort is no longer `max v u`"
    base = max(r["il"] for r in recs if "il" in r) + 1
    chain = [{"il": base, "max": [2, 1]}]
    for j in range(FUEL):
        chain.append({"il": base + 1 + j, "max": [base + j, 1]})
    recs[i] = {"il": 4, "max": [base + FUEL, 1]}
    recs[i:i] = chain
    dump("level_fuel_mutual.ndjson", recs)


if __name__ == "__main__":
    level_fuel_const()
    level_fuel_sort()
    level_fuel_mutual()
