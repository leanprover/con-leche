#!/usr/bin/env python3
"""Generator for asymptotic-scalability test streams (tasks #56, #98).

Emits lean4export ndjson (format 3.1.0, same as tests/e2e/*.ndjson) on
stdout, parameterized by a size n.  Each shape stresses a distinct
checker subsystem; a scalable checker handles all of them in roughly
linear time (see tests/scale.sh for the doubling-n harness).

The emitter hash-conses every name/level/expr table entry: real
lean4export never emits two structurally identical entries, and
downstream consumers (notably upstream nanoda) crash or misbehave on
duplicate entries.  Do NOT bypass the dedup — deduplicated streams are
part of the format contract.

Shapes (SHAPES below has the one-line summaries):
  chain      n defs  d_0 : Type := Prop,  d_i : Type := d_{i-1},
             plus  top : d_n := (forall p : Prop, p -> p).
             Checking `top` forces defeq  d_n == Prop, i.e. a delta
             chain of n unfoldings (env growth + unfold path).
  spine      f : Prop -> ... -> Prop  (n arrows)  := fun x1...xn => xn,
             a : Prop := forall p, p -> p,
             s : Prop := f a a ... a  (left-nested spine of n apps;
             stresses app-spine walking and Pi-type stepping).
  many       n independent tiny defs  m_i : Prop := forall p, p -> p
             (env insertion / lookup, per-decl setup).
  telescope  one def whose type is the dependent Pi-telescope
             p : Prop, h1 ... hn : p |- p  and whose value is the
             matching lambda-telescope returning h1 (binder opening
             and instantiation).
  dag        one def whose value is a perfectly shared binary DAG of
             depth n:  e_0 = base,  e_{i+1} = g e_i e_i  for a 2-ary
             g : Prop -> Prop -> Prop.  The expr table has O(n)
             entries; any unmemoized structural traversal is O(2^n)
             (the no-unmemoized-traversals invariant) and shows up as
             a catastrophic exponent immediately.
  delta      n defs  d_i : Prop := (fun x : Prop => x) d_{i-1}  over
             d_0 : Prop := forall p, p -> p, plus a *proof*
             top : d_n := fun p h => h  whose check whnfs d_n through
             n delta+beta steps (value-level unfolding, cf. chain's
             type-level chain).
  ctors      one inductive enum  E  with n constructors, a recursor
             with n rules, and a use that forces one iota step through
             the n-minor rec application.  Carries an `inductive`
             record; the checker installs it through the direct sum
             route (before task #207 this shape was fed to the
             external preprocessor and measured the modeled pipeline
             end to end).
  fields     one structure  S  with n Prop fields (single ctor,
             recursor, rule) plus a use projecting every field
             (.proj exprs): the direct simple-structure install.
  fanout     n tiny defs plus one def whose body references all n
             predecessors (n const lookups in one declaration; guards
             per-lookup env-index rebuild bugs).
  lets       one def whose value is an n-deep letE chain
             let x0 := A; let x_i := x_{i-1}; ...; x_{n-1}
             (lazy-zeta / let-binder handling).
  lparams    one def with n universe params  u_1 ... u_n, of type
             Sort (max u* + 1) with value Sort (max u*), plus a use
             instantiating all of them at 0 (level instantiation and
             n-ary max normalization).
  thm        one theorem whose proof value has size ~n:
             idp applied n times to (fun p h => h)  (thm-decl checking
             with a large proof term).

Usage: gen.py SHAPE N > out.ndjson
"""

import json
import sys


class Emit:
    """Writer for the export tables with structural hash-consing:
    emitting the same name/level/expr payload twice returns the first
    index and writes nothing (matching real lean4export, which never
    duplicates a table entry — duplicate entries crash or mislead
    downstream consumers such as upstream nanoda)."""

    def __init__(self, out):
        self.out = out
        self.next_name = 1   # 0 = anonymous
        self.next_level = 1  # 0 = level zero
        self.next_expr = 0
        self.names = {}
        self.levels = {}
        self.exprs = {}

    def _w(self, obj):
        self.out.write(json.dumps(obj, separators=(",", ":")) + "\n")

    def meta(self):
        self._w({"meta": {"exporter": {"name": "con-leche-scale-gen",
                                       "version": "3.1.0"},
                          "format": {"version": "3.1.0"},
                          "lean": {"githash": "0" * 40,
                                   "version": "4.29.1"}}})

    def name(self, s, pre=0):
        key = (pre, s)
        if key in self.names:
            return self.names[key]
        i = self.next_name
        self.next_name += 1
        self.names[key] = i
        self._w({"in": i, "str": {"pre": pre, "str": s}})
        return i

    def _level(self, kind, payload):
        key = json.dumps({kind: payload}, sort_keys=True)
        if key in self.levels:
            return self.levels[key]
        i = self.next_level
        self.next_level += 1
        self.levels[key] = i
        self._w({"il": i, kind: payload})
        return i

    def level_succ(self, l):
        return self._level("succ", l)

    def level_max(self, a, b):
        return self._level("max", [a, b])

    def level_param(self, nm):
        return self._level("param", nm)

    def expr(self, payload):
        key = json.dumps(payload, sort_keys=True)
        if key in self.exprs:
            return self.exprs[key]
        i = self.next_expr
        self.next_expr += 1
        self.exprs[key] = i
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

    def pi(self, name, ty, body, bi="default"):
        return self.expr({"forallE": {"binderInfo": bi, "body": body,
                                      "name": name, "type": ty}})

    def lam(self, name, ty, body, bi="default"):
        return self.expr({"lam": {"binderInfo": bi, "body": body,
                                  "name": name, "type": ty}})

    def letE(self, name, ty, value, body, nondep=False):
        return self.expr({"letE": {"body": body, "name": name,
                                   "nondep": nondep, "type": ty,
                                   "value": value}})

    def proj(self, type_name, idx, struct):
        return self.expr({"proj": {"idx": idx, "struct": struct,
                                   "typeName": type_name}})

    def defn(self, name, ty, value, height, lparams=()):
        self._w({"def": {"all": [name], "hints": {"regular": height},
                         "levelParams": list(lparams), "name": name,
                         "safety": "safe", "type": ty, "value": value}})

    def thm(self, name, ty, value, lparams=()):
        self._w({"thm": {"all": [name], "levelParams": list(lparams),
                         "name": name, "type": ty, "value": value}})


def true_prop(e, prop):
    """forall (p : Prop), p -> p  — a closed inhabitant of Prop."""
    p = e.name("p")
    b0 = e.bvar(0)
    b1 = e.bvar(1)
    inner = e.pi(0, b0, b1)          # p -> p
    return e.pi(p, prop, inner)      # forall p : Prop, ...


def id_proof(e, prop):
    """fun (p : Prop) (h : p) => h  — a proof of true_prop."""
    return e.lam(e.name("p"), prop,
                 e.lam(e.name("h"), e.bvar(0), e.bvar(0)))


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


def gen_dag(e, n):
    prop = e.sort(0)
    # g : Prop -> Prop -> Prop := fun a b => a -> b
    a = e.name("a")
    b = e.name("b")
    gty = e.pi(a, prop, e.pi(b, prop, prop))
    gval = e.lam(a, prop, e.lam(b, prop, e.pi(0, e.bvar(1), e.bvar(1))))
    g = e.name("g")
    e.defn(g, gty, gval, 1)
    base = e.name("base")
    e.defn(base, prop, true_prop(e, prop), 1)
    # dag : Prop := g (g ...) (g ...)  — shared binary DAG of depth n
    cg = e.const(g)
    node = e.const(base)
    for _ in range(n):
        node = e.app(e.app(cg, node), node)
    e.defn(e.name("dag"), prop, node, 2)


def gen_delta(e, n):
    prop = e.sort(0)
    x = e.name("x")
    idlam = e.lam(x, prop, e.bvar(0))    # fun x : Prop => x
    prev = e.name("d_0")
    e.defn(prev, prop, true_prop(e, prop), 1)
    for i in range(1, n + 1):
        nm = e.name(f"d_{i}")
        e.defn(nm, prop, e.app(idlam, e.const(prev)), i + 1)
        prev = nm
    # top : d_n := fun p h => h — checking whnfs d_n down to
    # forall p, p -> p through n delta+beta steps
    e.defn(e.name("top"), e.const(prev), id_proof(e, prop), n + 2)


def gen_ctors(e, n):
    """Enum E with n constructors + a use forcing one iota step."""
    type1 = e.sort(e.level_succ(0))      # Sort 1
    prop = e.sort(0)
    En = e.name("E")
    cE = e.const(En)
    ctor_names = [e.name(f"c_{i}", pre=En) for i in range(n)]
    rec_name = e.name("rec", pre=En)
    u = e.name("u")
    lu = e.level_param(u)
    sort_u = e.sort(lu)
    motive_nm = e.name("motive")
    t_nm = e.name("t")
    motive_ty = e.pi(t_nm, cE, sort_u)   # E -> Sort u
    # rec type: {motive : E -> Sort u} -> (motive c_0) -> ... ->
    #           (t : E) -> motive t
    body = e.app(e.bvar(n + 1), e.bvar(0))       # motive t
    rty = e.pi(t_nm, cE, body)
    for i in range(n - 1, -1, -1):
        # minor i sits under binders motive, m_0..m_{i-1}: motive = bvar i
        minor_ty = e.app(e.bvar(i), e.const(ctor_names[i]))
        rty = e.pi(ctor_names[i], minor_ty, rty)
    rty = e.pi(motive_nm, motive_ty, rty, bi="implicit")
    # rule rhs_i = fun motive m_0 ... m_{n-1} => m_i
    rules = []
    for i in range(n):
        rhs = e.bvar(n - 1 - i)
        for j in range(n - 1, -1, -1):
            minor_ty = e.app(e.bvar(j), e.const(ctor_names[j]))
            rhs = e.lam(ctor_names[j], minor_ty, rhs)
        rhs = e.lam(motive_nm, motive_ty, rhs)
        rules.append({"ctor": ctor_names[i], "nfields": 0, "rhs": rhs})
    e._w({"inductive": {
        "ctors": [{"cidx": i, "induct": En, "isUnsafe": False,
                   "levelParams": [], "name": ctor_names[i],
                   "numFields": 0, "numParams": 0, "type": cE}
                  for i in range(n)],
        "recs": [{"all": [En], "isUnsafe": False, "k": False,
                  "levelParams": [u], "name": rec_name,
                  "numIndices": 0, "numMinors": n, "numMotives": 1,
                  "numParams": 0, "rules": rules, "type": rty}],
        "types": [{"all": [En], "ctors": ctor_names, "isRec": False,
                   "isReflexive": False, "isUnsafe": False,
                   "levelParams": [], "name": En, "numIndices": 0,
                   "numNested": 0, "numParams": 0, "type": type1}]}})
    # use : (E.rec (motive := fun _ => Prop) A ... A c_{n-1}) :=
    #   fun p h => h — checking the proof whnfs the rec application,
    # firing iota through the n-minor spine.
    one = e.level_succ(0)
    a = true_prop(e, prop)
    use_ty = e.const(rec_name, us=[one])
    use_ty = e.app(use_ty, e.lam(t_nm, cE, prop))
    for _ in range(n):
        use_ty = e.app(use_ty, a)
    use_ty = e.app(use_ty, e.const(ctor_names[n - 1]))
    e.defn(e.name("use"), use_ty, id_proof(e, prop), 1)


def gen_fields(e, n):
    """Structure S with n Prop fields + a use projecting every field.

    The block matches the checker's direct simple-structure shape
    (ConLeche/Kernel/Direct.lean) exactly, so the run takes the direct
    install path."""
    type1 = e.sort(e.level_succ(0))      # Sort 1
    prop = e.sort(0)
    Sn = e.name("S")
    cS = e.const(Sn)
    mk = e.name("mk", pre=Sn)
    rec_name = e.name("rec", pre=Sn)
    u = e.name("u")
    lu = e.level_param(u)
    sort_u = e.sort(lu)
    f_nm = e.name("f")
    motive_nm = e.name("motive")
    t_nm = e.name("t")
    # mk : Prop -> ... -> Prop -> S   (n fields)
    cty = cS
    for _ in range(n):
        cty = e.pi(f_nm, prop, cty)
    motive_ty = e.pi(t_nm, cS, sort_u)   # S -> Sort u
    # minor : forall (f_0 ... f_{n-1} : Prop), motive (mk f_0 ... f_{n-1})
    spine = e.const(mk)
    for j in range(n):
        spine = e.app(spine, e.bvar(n - 1 - j))
    minor_ty = e.app(e.bvar(n), spine)   # motive = bvar n under the fields
    for _ in range(n):
        minor_ty = e.pi(f_nm, prop, minor_ty)
    # rec type: {motive} -> minor -> (t : S) -> motive t
    rty = e.pi(t_nm, cS, e.app(e.bvar(2), e.bvar(0)))
    rty = e.pi(mk, minor_ty, rty)
    rty = e.pi(motive_nm, motive_ty, rty, bi="implicit")
    # rule rhs = fun motive minor f_0 ... f_{n-1} => minor f_0 ... f_{n-1}
    rhs = e.bvar(n)
    for j in range(n):
        rhs = e.app(rhs, e.bvar(n - 1 - j))
    for _ in range(n):
        rhs = e.lam(f_nm, prop, rhs)
    rhs = e.lam(mk, minor_ty, rhs)
    rhs = e.lam(motive_nm, motive_ty, rhs)
    e._w({"inductive": {
        "ctors": [{"cidx": 0, "induct": Sn, "isUnsafe": False,
                   "levelParams": [], "name": mk, "numFields": n,
                   "numParams": 0, "type": cty}],
        "recs": [{"all": [Sn], "isUnsafe": False, "k": False,
                  "levelParams": [u], "name": rec_name,
                  "numIndices": 0, "numMinors": 1, "numMotives": 1,
                  "numParams": 0,
                  "rules": [{"ctor": mk, "nfields": n, "rhs": rhs}],
                  "type": rty}],
        "types": [{"all": [Sn], "ctors": [mk], "isRec": False,
                   "isReflexive": False, "isUnsafe": False,
                   "levelParams": [], "name": Sn, "numIndices": 0,
                   "numNested": 0, "numParams": 0, "type": type1}]}})
    # s0 : S := mk A ... A;  use : Prop := s0.0 -> s0.1 -> ... -> A
    a = true_prop(e, prop)
    v = e.const(mk)
    for _ in range(n):
        v = e.app(v, a)
    s0 = e.name("s0")
    e.defn(s0, cS, v, 1)
    body = a
    cs0 = e.const(s0)
    for j in range(n - 1, -1, -1):
        body = e.pi(0, e.proj(Sn, j, cs0), body)
    e.defn(e.name("use"), prop, body, 2)


def gen_fanout(e, n):
    prop = e.sort(0)
    val = true_prop(e, prop)
    names = []
    for i in range(n):
        nm = e.name(f"m_{i}")
        e.defn(nm, prop, val, 1)
        names.append(nm)
    # top : Prop := m_0 -> m_1 -> ... -> m_{n-1} -> m_0
    body = e.const(names[0])
    for i in range(n - 1, -1, -1):
        body = e.pi(0, e.const(names[i]), body)
    e.defn(e.name("top"), prop, body, 2)


def gen_lets(e, n):
    prop = e.sort(0)
    x = e.name("x")
    # let x0 : Prop := A; let x_i : Prop := x_{i-1}; ...; x_{n-1}
    body = e.bvar(0)
    for _ in range(n - 1):
        body = e.letE(x, prop, e.bvar(0), body)
    body = e.letE(x, prop, true_prop(e, prop), body)
    e.defn(e.name("lets"), prop, body, 1)


def gen_lparams(e, n):
    us = [e.name(f"u_{i}") for i in range(n)]
    lmax = e.level_param(us[n - 1])
    for i in range(n - 2, -1, -1):
        lmax = e.level_max(e.level_param(us[i]), lmax)
    # poly.{u_1 ... u_n} : Sort (max u* + 1) := Sort (max u*)
    poly = e.name("poly")
    e.defn(poly, e.sort(e.level_succ(lmax)), e.sort(lmax), 1, lparams=us)
    # use : Sort 1 := poly.{0, ..., 0} — forces level instantiation and
    # defeq  Sort (max 0 ... 0 + 1) == Sort 1
    e.defn(e.name("use"), e.sort(e.level_succ(0)),
           e.const(poly, us=[0] * n), 2)


def gen_thm(e, n):
    prop = e.sort(0)
    tp = true_prop(e, prop)
    idp = e.name("idp")
    e.defn(idp, tp, id_proof(e, prop), 1)
    # t : true_prop := idp TP (idp TP (... (fun p h => h)))
    idp_tp = e.app(e.const(idp), tp)     # idp TP : TP -> TP  (shared)
    pf = id_proof(e, prop)
    for _ in range(n):
        pf = e.app(idp_tp, pf)
    e.thm(e.name("t"), tp, pf)


SHAPES = {"chain": gen_chain, "spine": gen_spine,
          "many": gen_many, "telescope": gen_telescope,
          "dag": gen_dag, "delta": gen_delta,
          "ctors": gen_ctors, "fields": gen_fields,
          "fanout": gen_fanout, "lets": gen_lets,
          "lparams": gen_lparams, "thm": gen_thm}


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
