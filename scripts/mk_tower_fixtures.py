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


def block(s, n, e, lU, name_T, name_mk, name_rec, nF=1, ftys=None):
    """`inductive T where | mk : (h_1 … h_nF : @Eq Nat T60 T60) → T`,
    with its recursor and iota rule — every field type carries the
    tower.  `nF = 1` is the constructor-field-type shape; `nF = 2` also
    exercises the PROJECTION BODIES, which substitute `T.field_0` into
    the remaining telescope (`structProjBodies`).

    `ftys` overrides the field types, outermost first — each written in
    the scope of the fields BEFORE it (so field `j`'s type sees field
    `k < j` at `bvar (j - 1 - k)`), and mentioning nothing above them.
    That is what lets the same expressions serve as the constructor's
    domains, the minor premise's and the rule rhs' λ-domains, which sit
    under one extra binder each but never look past the fields."""
    eT = s.ex({"const": {"name": name_T, "us": []}})
    eB0 = s.ex({"bvar": 0})
    eMkC = s.ex({"const": {"name": name_mk, "us": []}})

    def pi(ty, body, bi="default"):
        return s.ex({"forallE": {"binderInfo": bi, "name": 0, "type": ty,
                                 "body": body}})

    def lam(ty, body, bi="default"):
        return s.ex({"lam": {"binderInfo": bi, "name": 0, "type": ty,
                             "body": body}})

    def bv(i):
        return eB0 if i == 0 else s.ex({"bvar": i})

    def app(f, a):
        return s.ex({"app": {"fn": f, "arg": a}})

    tys = ftys if ftys is not None else [e["eqTy"]] * nF
    assert len(tys) == nF

    def fields(inner, mk=None):
        """wrap `inner` in the nF field binders (`pi` or `lam`)"""
        mk = mk or pi
        for j in range(nF - 1, -1, -1):
            inner = mk(tys[j], inner)
        return inner

    def mk_applied():
        """`T.mk h_1 … h_nF` where the innermost field is `bvar 0`"""
        r = eMkC
        for j in range(1, nF + 1):
            r = app(r, bv(nF - j))
        return r

    eMkTy = fields(eT)
    eMotiveTy = pi(eT, e["SortU"])
    # the minor premise, in the `motive` context: motive is `bvar nF`
    # under the nF field binders
    eMinor = fields(app(bv(nF), mk_applied()))
    eRecTy = pi(eMotiveTy, pi(eMinor, pi(eT, app(bv(2), bv(0)))), "implicit")
    # the rule's rhs: `fun {motive} minor h_1 … h_nF => minor h_1 … h_nF`
    rhsBody = bv(nF)
    for j in range(1, nF + 1):
        rhsBody = app(rhsBody, bv(nF - j))
    rhsBody = fields(rhsBody, lam)
    eRhs = lam(eMotiveTy, lam(eMinor, rhsBody), "implicit")
    s.L.append(json.dumps({"inductive": {
        "types": [{"name": name_T, "levelParams": [], "type": e["Type"],
                   "numParams": 0, "numIndices": 0, "numNested": 0,
                   "ctors": [name_mk], "isRec": False, "isUnsafe": False,
                   "isReflexive": False, "all": [name_T]}],
        "ctors": [{"name": name_mk, "levelParams": [], "type": eMkTy,
                   "numParams": 0, "numFields": nF, "cidx": 0, "induct": name_T,
                   "isUnsafe": False}],
        "recs": [{"name": name_rec, "levelParams": [n["u"]], "type": eRecTy,
                  "numParams": 0, "numMotives": 1, "numMinors": 1,
                  "numIndices": 0, "k": False, "isUnsafe": False,
                  "all": [name_T],
                  "rules": [{"ctor": name_mk, "nfields": nF, "rhs": eRhs}]}],
        "isUnsafe": False, "all": [name_T]}}))


def iff_family(s, n, e):
    """The `Iff` block, spelled exactly as `ConLeche/Kernel/StdAxioms.lean`
    pins it (`iffRaw`/`iffIntroRaw`/`iffRecRaw`) and as `lean4export`
    writes it.  `stdAxiomOk`'s `propext` arm reaches
    `ConstantVal.matchesPin` on the axiom's own type only over a
    standardly-shaped stored `Iff` family, so the tower fixture needs
    this block in front of it."""
    n["Iff"] = s.name(0, "Iff")
    n["Iff.intro"] = s.name(n["Iff"], "intro")
    n["Iff.rec"] = s.name(n["Iff"], "rec")

    def pi(ty, body, bi="default"):
        return s.ex({"forallE": {"binderInfo": bi, "name": 0, "type": ty,
                                 "body": body}})

    def lam(ty, body, bi="default"):
        return s.ex({"lam": {"binderInfo": bi, "name": 0, "type": ty,
                             "body": body}})

    def bv(i):
        return s.ex({"bvar": i})

    def app(f, a):
        return s.ex({"app": {"fn": f, "arg": a}})

    def apps(f, *args):
        for a in args:
            f = app(f, a)
        return f

    P = e["Prop"]
    eIff = s.ex({"const": {"name": n["Iff"], "us": []}})
    eIntro = s.ex({"const": {"name": n["Iff.intro"], "us": []}})
    # `Iff : Prop → Prop → Prop`
    iffTy = pi(P, pi(P, P))
    # `Iff.intro (a b : Prop) (mp : a → b) (mpr : b → a) : Iff a b`
    introTy = pi(P, pi(P, pi(pi(bv(1), bv(1)), pi(pi(bv(1), bv(3)),
        apps(eIff, bv(3), bv(2))))))
    # `Iff.rec.{u} (a b : Prop) (motive : Iff a b → Sort u)
    #   (intro : ∀ mp mpr, motive (Iff.intro a b mp mpr)) (t : Iff a b) : motive t`
    motiveTy = pi(apps(eIff, bv(1), bv(0)), e["SortU"])
    minor = pi(pi(bv(2), bv(2)),
               pi(pi(bv(2), bv(4)),
                  app(bv(2), apps(eIntro, bv(4), bv(3), bv(1), bv(0)))))
    recTy = pi(P, pi(P, pi(motiveTy, pi(minor,
        pi(apps(eIff, bv(3), bv(2)), app(bv(2), bv(0)))))))
    rhs = lam(P, lam(P, lam(motiveTy, lam(minor,
        lam(pi(bv(3), bv(3)), lam(pi(bv(3), bv(5)),
            apps(bv(2), bv(1), bv(0))))))))
    s.L.append(json.dumps({"inductive": {
        "types": [{"name": n["Iff"], "levelParams": [], "type": iffTy,
                   "numParams": 2, "numIndices": 0, "numNested": 0,
                   "ctors": [n["Iff.intro"]], "isRec": False, "isUnsafe": False,
                   "isReflexive": False, "all": [n["Iff"]]}],
        "ctors": [{"name": n["Iff.intro"], "levelParams": [], "type": introTy,
                   "numParams": 2, "numFields": 2, "cidx": 0,
                   "induct": n["Iff"], "isUnsafe": False}],
        "recs": [{"name": n["Iff.rec"], "levelParams": [n["u"]], "type": recTy,
                  "numParams": 2, "numMotives": 1, "numMinors": 1,
                  "numIndices": 0, "k": False, "isUnsafe": False,
                  "all": [n["Iff"]],
                  "rules": [{"ctor": n["Iff.intro"], "nfields": 2,
                             "rhs": rhs}]}],
        "isUnsafe": False, "all": [n["Iff"]]}}))


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


def mk_proj():
    """The tower in the field types of a TWO-field structure: the
    projection bodies substitute `T.field_0` into the rest of the
    constructor's telescope (`structProjBodies` /
    `Cached.structProjBodiesC`, task #210 Part B / #214 P4), so the
    substitution walks a field type that carries the tower.  Accepts."""
    s = Stream(); n, e, lU, _ = base(s, tyname="Pair")
    block(s, n, e, lU, n["T"], n["T.mk"], n["T.rec"], nF=2)
    s.write("tests/e2e/tower_proj.ndjson")


def mk_usedlater():
    """The tower under `structUsedLater` (task #233): a THREE-field
    structure whose LAST field's type is a tower built on the FIRST
    field's variable — `t_0 = x`, `t_{k+1} = (K t_k) t_k`, the type
    `@Eq Nat t_60 Nat.zero`, still defeq to `@Eq Nat x Nat.zero`.

    `structProjGuards` asks `structUsedLater cty 0 j` for every earlier
    field `j`, i.e. "does the constructor telescope's remainder after
    binder `j` contain `bvar 0`?".  At `j = 1` (the second field, `y`)
    that remainder is `(h : @Eq Nat t_60[x] Nat.zero) → T`, where the
    tower mentions `x` — `bvar 1` there — and NOT `y`.  So the answer
    is **false** while the packed bound is 2 at every tower node: the
    `bvarB ≤ i` cutoff (task #210 Part B) cannot fire, `||` cannot
    short-circuit on a `true`, and the plain tree recursion visits each
    shared node once per path — `2^60`.

    This is why the earlier tower fixtures do not reach it: their
    towers are CLOSED (`t_0 = Nat.zero`), so the cutoff stops the walk
    at the first tower node.  The cutoff covers "the variable cannot
    occur"; the memo covers "the variable does not occur but a loose
    variable above it does".  Accepts."""
    s = Stream(); n, e, lU, _ = base(s, tyname="Used")

    def app(f, a):
        return s.ex({"app": {"fn": f, "arg": a}})

    # the tower on the FIRST field's variable: inside the third field's
    # type the fields are `y = bvar 0`, `x = bvar 1`
    t = s.ex({"bvar": 1})
    for _ in range(DEPTH):
        t = app(app(e["K"], t), t)
    eEqNat = s.ex({"app": {"fn": e["Eq"], "arg": e["Nat"]}})
    fTy = app(app(eEqNat, t), e["zero"])
    block(s, n, e, lU, n["T"], n["T.mk"], n["T.rec"], nF=3,
          ftys=[e["Nat"], e["Nat"], fTy])
    s.write("tests/e2e/tower_usedlater.ndjson")


def mk_axiom_pin():
    """The tower in the type of an axiom under the PINNED name
    `propext`, over a standardly-shaped stored `Iff` family — the one
    shape that reaches `ConstantVal.matchesPin` / `Expr.erasePw`
    (`stdAxiomOk`'s guards short-circuit on the family otherwise).
    Must DECLINE as a divergent pin."""
    s = Stream(); n, e, _, _ = base(s)
    iff_family(s, n, e)
    n["propext"] = s.name(0, "propext")
    s.L.append(json.dumps({"axiom": {"name": n["propext"], "levelParams": [],
                                     "type": e["eqTy"], "isUnsafe": False}}))
    s.write("tests/e2e/tower_axiom_pin.ndjson")


def mk_axiom_nonstd():
    """The tower in the type of an axiom under a NON-pinned name: the
    positive decline ("non-standard axiom") is on the name alone, so
    no pin comparison is reached at all.  The type is still checked, so
    this is also a gate on the annotation pass's DAG-safety."""
    s = Stream(); n, e, _, _ = base(s)
    n["ax"] = s.name(0, "towerAxiom")
    s.L.append(json.dumps({"axiom": {"name": n["ax"], "levelParams": [],
                                     "type": e["eqTy"], "isUnsafe": False}}))
    s.write("tests/e2e/tower_axiom_nonstd.ndjson")


mk_struct()
mk_thm()
mk_prelude()
mk_axiom()
mk_quot()
mk_proj()
mk_axiom_pin()
mk_axiom_nonstd()
mk_usedlater()
