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
    type is the tower.  The prelude dedupe (`Declaration.sameCanon`) must
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


def mk_beqpair():
    """The tower under the EQUALITY memo (task #240): two structurally
    equal towers that are not the same objects, in the shape that makes
    one node's memo entry ALTERNATE between two partners.

    `Expr.beq`'s memoized descent is what keeps a comparison `O(DAG)`,
    and until #240 it keyed an entry on `addr a` alone with `addr b` as
    the value — one partner per node.  A node compared against two
    partners in turn then invalidates its own entry on every visit,
    nothing below it stays memoized, and the walk falls back to the
    unshared tree on exactly the DAG the memo exists for.

    The shape.  `G = fun (a b c : Nat) => a`, and `g x y z = G x y z`,
    defeq to `x`, so every tower below is defeq to `Nat.zero` and all
    of them are structurally equal — they differ only in WHICH nodes
    they share:

    * a SHARED tower `S_{k+1} = g S_k S_k S_k`, one chain of nodes;
    * an ALTERNATING pair `P_{k+1} = g P_k Q_k P_k`,
      `Q_{k+1} = g Q_k P_k Q_k`.

    **THREE arguments, not two, is what makes it bite.**  Comparing
    `S_n` with `P_n` asks `(S, P)`, `(S, Q)`, `(S, P)` one level down:
    with a memo keyed on the left node the third query finds the entry
    holding `Q` and re-walks, and so does every level below it, so the
    cost is `3^n` — 3^60 here.  At two arguments the queries are
    `(S,P), (S,Q)` and the entries left behind by the first walk still
    serve the second at every level but the top, which is only
    quadratic and would pass unnoticed.  Keyed on the PAIR the same
    comparison is 2 entries per level, `O(n)`.

    Both ORIENTATIONS are here, because which side of a declaration's
    defeq check is the memo's key side is the checker's business and
    not the fixture's.  `beqPairA` puts the alternating pair in the
    theorem's TYPE and the shared tower in its value, so the bad
    direction is "inferred type on the left"; `beqPairB` is the other
    way round.  Exactly one of the two is the exponential one under a
    left-keyed memo, whichever order the checker uses.  Accepts."""
    s = Stream(); n, e, lU, lOne = base(s)

    def app(f, a):
        return s.ex({"app": {"fn": f, "arg": a}})

    def zero():
        return s.ex({"const": {"name": n["Nat.zero"], "us": []}})

    # `G = fun (a b c : Nat) => a`
    gb = s.ex({"bvar": 2})
    for _ in range(3):
        gb = s.ex({"lam": {"binderInfo": "default", "name": 0,
                           "type": e["Nat"], "body": gb}})
    eG = gb

    def g3(x, y, z):
        return app(app(app(eG, x), y), z)

    def shared():
        t = zero()
        for _ in range(DEPTH):
            t = g3(t, t, t)
        return t

    def alternating():
        p, q = zero(), zero()
        for _ in range(DEPTH):
            p, q = g3(p, q, p), g3(q, p, q)
        return p, q

    eRefl = s.ex({"const": {"name": n["Eq.refl"], "us": [lOne]}})
    eEqNat = app(e["Eq"], e["Nat"])

    def thm(nm, ty, val):
        s.L.append(json.dumps({"thm": {"name": nm, "levelParams": [],
                                       "type": ty, "value": val,
                                       "all": [nm]}}))

    # A: the alternating pair is the TYPE's two arguments
    n["thmA"] = s.name(0, "beqPairA")
    pA, qA = alternating()
    thm(n["thmA"], app(app(eEqNat, pA), qA),
        app(app(eRefl, e["Nat"]), shared()))
    # B: the alternating pair is what the VALUE's inferred type carries
    n["thmB"] = s.name(0, "beqPairB")
    sB = shared()
    pB, _ = alternating()
    thm(n["thmB"], app(app(eEqNat, sB), sB),
        app(app(eRefl, e["Nat"]), pB))
    s.write("tests/e2e/tower_beqpair.ndjson")


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



def _ops(s):
    """The raw builders every hand-written block below shares."""
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

    def lams(tys, body):
        for ty in reversed(tys):
            body = lam(ty, body)
        return body

    def pis(tys, body):
        for ty in reversed(tys):
            body = pi(ty, body)
        return body

    return pi, lam, bv, app, apps, lams, pis


def open_tower(s, e, i):
    """`@Eq Nat t_60 Nat.zero` with `t_0 = bvar i` and
    `t_{k+1} = (K t_k) t_k` — the depth-60 tower over the binder `i`
    steps below, still defeq to `@Eq Nat (bvar i) Nat.zero`.  Written
    at the frame of the field it is a domain of, which is the SAME
    frame in the constructor, in the minor premise and in the rule's
    λ-telescope, so the three records share one entry."""
    def app(f, a):
        return s.ex({"app": {"fn": f, "arg": a}})

    t = s.ex({"bvar": i})
    for _ in range(DEPTH):
        t = app(app(e["K"], t), t)
    return app(app(app(e["Eq"], e["Nat"]), t), e["zero"])


def mk_recfield():
    """The tower under `Expr.mentionsFvar` (`Expr.fvarLeaves`): a
    RECURSIVE structure whose field after the recursive one is a tower
    over the FIRST field's variable.

        inductive RecF where
          | mk : (x : Nat) → (r : RecF) → (h : @Eq Nat t_60[x] Nat.zero) → RecF

    `nativeOpenedOk`/`nativeOpenedOkF` re-check the recogniser's kinds
    on the constructor type OPENED at variables, and at a `.recursive`
    field `i` they ask that the field's variable occur in no LATER
    field's domain — `!(xFvs.drop (i+1)).any (·.fvarTypeD.mentionsFvar
    (nP + i))`.  Here field 1 is the recursive one and field 2's domain
    is the tower, built over field 0's variable, so the query is about
    a variable the tower does not mention: nothing short-circuits and
    the answer needs the whole open subgraph.  The earlier fixtures do
    not reach it — `tower_usedlater`'s fields are all ordinary, so no
    recursive arm is entered, and none of the closed towers is walked
    for a variable at all.  Accepts."""
    s = Stream(); n, e, lU, _ = base(s, tyname="RecF")
    pi, lam, bv, app, apps, lams, pis = _ops(s)
    eT = s.ex({"const": {"name": n["T"], "us": []}})
    eMk = s.ex({"const": {"name": n["T.mk"], "us": []}})
    eRec = s.ex({"const": {"name": n["T.rec"], "us": [lU]}})
    # the third field's domain, at the frame where `x` is `bvar 1`
    fTy = open_tower(s, e, 1)
    eMkTy = pi(e["Nat"], pi(eT, pi(fTy, eT)))
    eMotiveTy = pi(eT, e["SortU"])
    # the minor: the fields, then the recursive field's ih, then the
    # conclusion — `∀ x r h, motive r → motive (RecF.mk x r h)`
    eMinor = pi(e["Nat"], pi(eT, pi(fTy,
        pi(app(bv(3), bv(1)),
           app(bv(4), apps(eMk, bv(3), bv(2), bv(1)))))))
    eRecTy = pi(eMotiveTy, pi(eMinor, pi(eT, app(bv(2), bv(0)))), "implicit")
    # `fun motive minor x r h => minor x r h (RecF.rec motive minor r)`
    eRhs = lams([eMotiveTy, eMinor, e["Nat"], eT, fTy],
        app(apps(bv(3), bv(2), bv(1), bv(0)),
            apps(eRec, bv(4), bv(3), bv(1))))
    s.L.append(json.dumps({"inductive": {
        "types": [{"name": n["T"], "levelParams": [], "type": e["Type"],
                   "numParams": 0, "numIndices": 0, "numNested": 0,
                   "ctors": [n["T.mk"]], "isRec": True, "isUnsafe": False,
                   "isReflexive": False, "all": [n["T"]]}],
        "ctors": [{"name": n["T.mk"], "levelParams": [], "type": eMkTy,
                   "numParams": 0, "numFields": 3, "cidx": 0,
                   "induct": n["T"], "isUnsafe": False}],
        "recs": [{"name": n["T.rec"], "levelParams": [n["u"]], "type": eRecTy,
                  "numParams": 0, "numMotives": 1, "numMinors": 1,
                  "numIndices": 0, "k": False, "isUnsafe": False,
                  "all": [n["T"]],
                  "rules": [{"ctor": n["T.mk"], "nfields": 3, "rhs": eRhs}]}],
        "isUnsafe": False, "all": [n["T"]]}}))
    s.write("tests/e2e/tower_recfield.ndjson")


def mk_mutual():
    """The tower under the in-process modeller's MUTUAL rung
    (`ConLeche/Frontend/InModel/{Kit,Mutual}.lean`): a two-member
    mutual block whose first constructor carries a tower field.

        mutual
          inductive MutA where
            | mk : (x : Nat) → (h : @Eq Nat t_60[x] Nat.zero) → MutB → MutA
          inductive MutB where
            | mk : MutA → MutB
        end

    A mutual block goes to the MODELED route, so the frontend
    generates its `_model` family in-process; `classifyCtor` asks
    `Kit.mentionsAny memberNames d` of every ORDINARY field domain,
    and `Kit.hintFor`/`Kit.maxHeight` walks every generated value —
    both plain `Expr` recursions with no cutoff and nothing to
    short-circuit on (the domain mentions neither member, and the
    tower's constants all have height 0).  Every earlier tower fixture
    is a single non-mutual block, so the modeller is never entered.
    Accepts."""
    s = Stream(); n, e, lU, _ = base(s, tyname="MutA")
    pi, lam, bv, app, apps, lams, pis = _ops(s)
    n["B"] = s.name(0, "MutB")
    n["B.mk"] = s.name(n["B"], "mk")
    n["B.rec"] = s.name(n["B"], "rec")
    eA = s.ex({"const": {"name": n["T"], "us": []}})
    eB = s.ex({"const": {"name": n["B"], "us": []}})
    eAmk = s.ex({"const": {"name": n["T.mk"], "us": []}})
    eBmk = s.ex({"const": {"name": n["B.mk"], "us": []}})
    eArec = s.ex({"const": {"name": n["T.rec"], "us": [lU]}})
    eBrec = s.ex({"const": {"name": n["B.rec"], "us": [lU]}})
    # the second field's domain, at the frame where `x` is `bvar 0`
    fTy = open_tower(s, e, 0)
    eAmkTy = pi(e["Nat"], pi(fTy, pi(eB, eA)))
    eBmkTy = pi(eA, eB)
    mA = pi(eA, e["SortU"])          # motive_A
    mB = pi(eB, e["SortU"])          # motive_B
    # minor_A : ∀ x h (b : MutB), motive_B b → motive_A (MutA.mk x h b)
    minA = pi(e["Nat"], pi(fTy, pi(eB,
        pi(app(bv(3), bv(0)), app(bv(5), apps(eAmk, bv(3), bv(2), bv(1)))))))
    # minor_B : ∀ (a : MutA), motive_A a → motive_B (MutB.mk a)
    minB = pi(eA, pi(app(bv(3), bv(0)), app(bv(3), app(eBmk, bv(1)))))
    eArecTy = pi(mA, pi(mB, pis([minA, minB],
        pi(eA, app(bv(4), bv(0)))), "implicit"), "implicit")
    eBrecTy = pi(mA, pi(mB, pis([minA, minB],
        pi(eB, app(bv(3), bv(0)))), "implicit"), "implicit")
    # `fun mA mB minA minB x h b => minA x h b (MutB.rec mA mB minA minB b)`
    eArhs = lams([mA, mB, minA, minB, e["Nat"], fTy, eB],
        app(apps(bv(4), bv(2), bv(1), bv(0)),
            apps(eBrec, bv(6), bv(5), bv(4), bv(3), bv(0))))
    # `fun mA mB minA minB a => minB a (MutA.rec mA mB minA minB a)`
    eBrhs = lams([mA, mB, minA, minB, eA],
        app(app(bv(1), bv(0)),
            apps(eArec, bv(4), bv(3), bv(2), bv(1), bv(0))))
    tys = [{"name": nm, "levelParams": [], "type": e["Type"],
            "numParams": 0, "numIndices": 0, "numNested": 0,
            "ctors": [ct], "isRec": True, "isUnsafe": False,
            "isReflexive": False, "all": [n["T"], n["B"]]}
           for nm, ct in [(n["T"], n["T.mk"]), (n["B"], n["B.mk"])]]
    s.L.append(json.dumps({"inductive": {
        "types": tys,
        "ctors": [{"name": n["T.mk"], "levelParams": [], "type": eAmkTy,
                   "numParams": 0, "numFields": 3, "cidx": 0,
                   "induct": n["T"], "isUnsafe": False},
                  {"name": n["B.mk"], "levelParams": [], "type": eBmkTy,
                   "numParams": 0, "numFields": 1, "cidx": 0,
                   "induct": n["B"], "isUnsafe": False}],
        "recs": [{"name": n["T.rec"], "levelParams": [n["u"]],
                  "type": eArecTy, "numParams": 0, "numMotives": 2,
                  "numMinors": 2, "numIndices": 0, "k": False,
                  "isUnsafe": False, "all": [n["T"], n["B"]],
                  "rules": [{"ctor": n["T.mk"], "nfields": 3,
                             "rhs": eArhs}]},
                 {"name": n["B.rec"], "levelParams": [n["u"]],
                  "type": eBrecTy, "numParams": 0, "numMotives": 2,
                  "numMinors": 2, "numIndices": 0, "k": False,
                  "isUnsafe": False, "all": [n["T"], n["B"]],
                  "rules": [{"ctor": n["B.mk"], "nfields": 1,
                             "rhs": eBrhs}]}],
        "isUnsafe": False, "all": [n["T"], n["B"]]}}))
    s.write("tests/e2e/tower_mutual.ndjson")


def mk_nested():
    """The tower under the in-process modeller's NESTED rung
    (`ConLeche/Frontend/InModel/Nested.lean`, and `Expr.lowerBVars`,
    which lowers the generated pins and domains out of the rule-prefix
    context):

        inductive NBox (α : Type) where
          | nil : NBox α
          | cons : α → NBox α → NBox α

        inductive NTow where
          | node : (x : Nat) → (h : @Eq Nat t_60[x] Nat.zero) → NBox NTow → NTow

    The container is an ordinary block on the fixpoint route; the
    nested block that follows is modeled, so the nested rung reads the
    container's shape, specialises it, and moves every domain — the
    tower among them — with `Expr.lowerBVars`, a plain rebuild with no
    memo.  Accepts."""
    s = Stream(); n, e, lU, _ = base(s, tyname="NTow")
    pi, lam, bv, app, apps, lams, pis = _ops(s)
    n["L"] = s.name(0, "NBox")
    n["L.nil"] = s.name(n["L"], "nil")
    n["L.cons"] = s.name(n["L"], "cons")
    n["L.rec"] = s.name(n["L"], "rec")
    n["T.rec1"] = s.name(n["T"], "rec_1")
    eL = s.ex({"const": {"name": n["L"], "us": []}})
    eLnil = s.ex({"const": {"name": n["L.nil"], "us": []}})
    eLcons = s.ex({"const": {"name": n["L.cons"], "us": []}})
    eLrec = s.ex({"const": {"name": n["L.rec"], "us": [lU]}})
    eT = s.ex({"const": {"name": n["T"], "us": []}})
    eNode = s.ex({"const": {"name": n["T.mk"], "us": []}})
    eTrec = s.ex({"const": {"name": n["T.rec"], "us": [lU]}})
    eTrec1 = s.ex({"const": {"name": n["T.rec1"], "us": [lU]}})

    # --- the container `NBox`, exactly as the elaborator generates it
    eNilTy = pi(e["Type"], app(eL, bv(0)), "implicit")
    eConsTy = pi(e["Type"], pi(bv(0), pi(app(eL, bv(1)), app(eL, bv(2)))),
                 "implicit")
    lMotive = pi(app(eL, bv(0)), e["SortU"])
    lMinNil = app(bv(0), app(eLnil, bv(1)))
    lMinCons = pi(bv(2), pi(app(eL, bv(3)), pi(app(bv(3), bv(0)),
        app(bv(4), apps(eLcons, bv(5), bv(2), bv(1))))))
    eLrecTy = pi(e["Type"], pi(lMotive, pis([lMinNil, lMinCons],
        pi(app(eL, bv(3)), app(bv(3), bv(0)))), "implicit"), "implicit")
    eLnilRhs = lams([e["Type"], lMotive, lMinNil, lMinCons], bv(1))
    eLconsRhs = lams([e["Type"], lMotive, lMinNil, lMinCons],
        lam(bv(3), lam(app(eL, bv(4)),
            app(apps(bv(2), bv(1), bv(0)),
                apps(eLrec, bv(5), bv(4), bv(3), bv(2), bv(0))))))
    s.L.append(json.dumps({"inductive": {
        "types": [{"name": n["L"], "levelParams": [],
                   "type": pi(e["Type"], e["Type"]),
                   "numParams": 1, "numIndices": 0, "numNested": 0,
                   "ctors": [n["L.nil"], n["L.cons"]], "isRec": True,
                   "isUnsafe": False, "isReflexive": False, "all": [n["L"]]}],
        "ctors": [{"name": n["L.nil"], "levelParams": [], "type": eNilTy,
                   "numParams": 1, "numFields": 0, "cidx": 0,
                   "induct": n["L"], "isUnsafe": False},
                  {"name": n["L.cons"], "levelParams": [], "type": eConsTy,
                   "numParams": 1, "numFields": 2, "cidx": 1,
                   "induct": n["L"], "isUnsafe": False}],
        "recs": [{"name": n["L.rec"], "levelParams": [n["u"]],
                  "type": eLrecTy, "numParams": 1, "numMotives": 1,
                  "numMinors": 2, "numIndices": 0, "k": False,
                  "isUnsafe": False, "all": [n["L"]],
                  "rules": [{"ctor": n["L.nil"], "nfields": 0,
                             "rhs": eLnilRhs},
                            {"ctor": n["L.cons"], "nfields": 2,
                             "rhs": eLconsRhs}]}],
        "isUnsafe": False, "all": [n["L"]]}}))

    # --- the nested block `NTow`
    eLT = app(eL, eT)                       # `NBox NTow`
    fTy = open_tower(s, e, 0)               # the tower field, `x = bvar 0`
    eNodeTy = pi(e["Nat"], pi(fTy, pi(eLT, eT)))
    mT = pi(eT, e["SortU"])                 # motive for `NTow`
    mL = pi(eLT, e["SortU"])                # motive for `NBox NTow`
    # minor_node : ∀ x h (l : NBox NTow), motive_L l → motive_T (node x h l)
    minNode = pi(e["Nat"], pi(fTy, pi(eLT,
        pi(app(bv(3), bv(0)), app(bv(5), apps(eNode, bv(3), bv(2), bv(1)))))))
    minNil = app(bv(1), app(eLnil, eT))
    minCons = pi(eT, pi(eLT, pi(app(bv(5), bv(1)), pi(app(bv(5), bv(1)),
        app(bv(6), apps(eLcons, eT, bv(3), bv(2)))))))
    eTrecTy = pi(mT, pi(mL, pis([minNode, minNil, minCons],
        pi(eT, app(bv(5), bv(0)))), "implicit"), "implicit")
    eTrec1Ty = pi(mT, pi(mL, pis([minNode, minNil, minCons],
        pi(eLT, app(bv(4), bv(0)))), "implicit"), "implicit")
    # `fun mT mL minNode minNil minCons x h l =>
    #     minNode x h l (NTow.rec_1 mT mL minNode minNil minCons l)`
    eNodeRhs = lams([mT, mL, minNode, minNil, minCons, e["Nat"], fTy, eLT],
        app(apps(bv(5), bv(2), bv(1), bv(0)),
            apps(eTrec1, bv(7), bv(6), bv(5), bv(4), bv(3), bv(0))))
    eNilRhs = lams([mT, mL, minNode, minNil, minCons], bv(1))
    eConsRhs = lams([mT, mL, minNode, minNil, minCons, eT, eLT],
        app(app(apps(bv(2), bv(1), bv(0)),
                apps(eTrec, bv(6), bv(5), bv(4), bv(3), bv(2), bv(1))),
            apps(eTrec1, bv(6), bv(5), bv(4), bv(3), bv(2), bv(0))))
    prefixR = {"levelParams": [n["u"]], "numParams": 0, "numMotives": 2,
               "numMinors": 3, "numIndices": 0, "k": False,
               "isUnsafe": False, "all": [n["T"]]}
    s.L.append(json.dumps({"inductive": {
        "types": [{"name": n["T"], "levelParams": [], "type": e["Type"],
                   "numParams": 0, "numIndices": 0, "numNested": 1,
                   "ctors": [n["T.mk"]], "isRec": True, "isUnsafe": False,
                   "isReflexive": False, "all": [n["T"]]}],
        "ctors": [{"name": n["T.mk"], "levelParams": [], "type": eNodeTy,
                   "numParams": 0, "numFields": 3, "cidx": 0,
                   "induct": n["T"], "isUnsafe": False}],
        "recs": [dict(prefixR, name=n["T.rec1"], type=eTrec1Ty,
                      rules=[{"ctor": n["L.nil"], "nfields": 0,
                              "rhs": eNilRhs},
                             {"ctor": n["L.cons"], "nfields": 2,
                              "rhs": eConsRhs}]),
                 dict(prefixR, name=n["T.rec"], type=eTrecTy,
                      rules=[{"ctor": n["T.mk"], "nfields": 3,
                              "rhs": eNodeRhs}])],
        "isUnsafe": False, "all": [n["T"]]}}))
    s.write("tests/e2e/tower_nested.ndjson")


mk_struct()
mk_thm()
mk_prelude()
mk_axiom()
mk_quot()
mk_proj()
mk_axiom_pin()
mk_axiom_nonstd()
mk_usedlater()
mk_beqpair()
mk_recfield()
mk_mutual()
mk_nested()
