#!/usr/bin/env python3
"""Generator for asymptotic-scalability test streams (task #56).

Emits lean4export ndjson (format 3.1.0, same as tests/e2e/*.ndjson) on
stdout, parameterized by a size n.  Each shape stresses a distinct
checker subsystem; a scalable checker handles all of them in roughly
linear time (see tests/scale.sh for the doubling-n harness).

Shapes:
  chain n      n defs  d_0 : Type := Prop,  d_i : Type := d_{i-1},
               plus  top : d_n := (forall p : Prop, p -> p).
               Checking `top` forces defeq  d_n == Prop, i.e. a delta
               chain of n unfoldings (env growth + unfold path).
  spine n      f : Prop -> ... -> Prop  (n arrows)  := fun x1...xn => xn,
               a : Prop := forall p, p -> p,
               s : Prop := f a a ... a  (left-nested spine of n apps;
               stresses app-spine walking and Pi-type stepping).
  many n       n independent tiny defs  m_i : Prop := forall p, p -> p
               (env insertion / lookup, per-decl setup).
  telescope n  one def whose type is the dependent Pi-telescope
               p : Prop, h1 ... hn : p |- p  and whose value is the
               matching lambda-telescope returning h1 (binder opening
               and instantiation).

Usage: gen.py SHAPE N > out.ndjson
"""

import json
import sys


class Emit:
    """Tiny writer for the export tables.  Indices are allocated in
    emission order, so every node is defined before use."""

    def __init__(self, out):
        self.out = out
        self.next_name = 1   # 0 = anonymous
        self.next_level = 1  # 0 = level zero
        self.next_expr = 0

    def _w(self, obj):
        self.out.write(json.dumps(obj, separators=(",", ":")) + "\n")

    def meta(self):
        self._w({"meta": {"exporter": {"name": "setlec-scale-gen",
                                       "version": "3.1.0"},
                          "format": {"version": "3.1.0"},
                          "lean": {"githash": "0" * 40,
                                   "version": "4.29.1"}}})

    def name(self, s, pre=0):
        i = self.next_name
        self.next_name += 1
        self._w({"in": i, "str": {"pre": pre, "str": s}})
        return i

    def level_succ(self, l):
        i = self.next_level
        self.next_level += 1
        self._w({"il": i, "succ": l})
        return i

    def expr(self, payload):
        i = self.next_expr
        self.next_expr += 1
        rec = {"ie": i}
        rec.update(payload)
        self._w(rec)
        return i

    def sort(self, l):
        return self.expr({"sort": l})

    def bvar(self, i):
        return self.expr({"bvar": i})

    def const(self, name, us=()):
        return self.expr({"const": {"name": name, "us": list(us)}})

    def app(self, fn, arg):
        return self.expr({"app": {"fn": fn, "arg": arg}})

    def pi(self, name, ty, body):
        return self.expr({"forallE": {"binderInfo": "default", "body": body,
                                      "name": name, "type": ty}})

    def lam(self, name, ty, body):
        return self.expr({"lam": {"binderInfo": "default", "body": body,
                                  "name": name, "type": ty}})

    def defn(self, name, ty, value, height):
        self._w({"def": {"all": [name], "hints": {"regular": height},
                         "levelParams": [], "name": name, "safety": "safe",
                         "type": ty, "value": value}})


def true_prop(e, prop):
    """forall (p : Prop), p -> p  — a closed inhabitant of Prop."""
    p = e.name("p")
    b0 = e.bvar(0)
    b1 = e.bvar(1)
    inner = e.pi(0, b0, b1)          # p -> p
    return e.pi(p, prop, inner)      # forall p : Prop, ...


def gen_chain(e, n):
    one = e.level_succ(0)
    ty = e.sort(one)                 # Type
    prop = e.sort(0)                 # Prop
    prev = None
    for i in range(n + 1):
        nm = e.name(f"d_{i}")
        val = prop if i == 0 else e.const(prev)
        e.defn(nm, ty, val, i + 1)
        prev = nm
    top = e.name("top")
    e.defn(top, e.const(prev), true_prop(e, prop), n + 2)


def gen_spine(e, n):
    prop = e.sort(0)
    x = e.name("x")
    # f : Prop -> ... -> Prop (n arrows) := fun x1...xn => xn
    fty = prop
    fval = e.bvar(0)
    for _ in range(n):
        fty = e.pi(x, prop, fty)
        fval = e.lam(x, prop, fval)
    f = e.name("f")
    e.defn(f, fty, fval, 1)
    a = e.name("a")
    e.defn(a, prop, true_prop(e, prop), 1)
    # s : Prop := f a a ... a
    spine = e.const(f)
    ca = e.const(a)
    for _ in range(n):
        spine = e.app(spine, ca)
    s = e.name("s")
    e.defn(s, prop, spine, 2)


def gen_many(e, n):
    prop = e.sort(0)
    val = true_prop(e, prop)
    for i in range(n):
        nm = e.name(f"m_{i}")
        e.defn(nm, prop, val, 1)


def gen_telescope(e, n):
    prop = e.sort(0)
    p = e.name("p")
    h = e.name("h")
    bvars = [e.bvar(i) for i in range(n + 1)]
    # type:  forall (p : Prop) (h1 ... hn : p), p
    ty = bvars[n]                    # innermost body: p = bvar n
    for k in range(n, 0, -1):        # binder h_k has type p = bvar (k-1)
        ty = e.pi(h, bvars[k - 1], ty)
    ty = e.pi(p, prop, ty)
    # value: fun (p : Prop) (h1 ... hn : p) => h1
    val = bvars[n - 1]               # h1 = bvar (n-1)
    for k in range(n, 0, -1):
        val = e.lam(h, bvars[k - 1], val)
    val = e.lam(p, prop, val)
    e.defn(e.name("tele"), ty, val, 1)


SHAPES = {"chain": gen_chain, "spine": gen_spine,
          "many": gen_many, "telescope": gen_telescope}


def main():
    if len(sys.argv) != 3 or sys.argv[1] not in SHAPES:
        sys.exit(f"usage: gen.py {{{'|'.join(SHAPES)}}} N")
    n = int(sys.argv[2])
    if n < 1:
        sys.exit("N must be >= 1")
    e = Emit(sys.stdout)
    e.meta()
    SHAPES[sys.argv[1]](e, n)


if __name__ == "__main__":
    main()
