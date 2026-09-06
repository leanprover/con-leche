#!/usr/bin/env python3
"""Build the proof-irrelevance COMMIT-vs-fall-through fixture.

Task #161 residual round 2.  Appends to the arena's
alg-conv-trans-acc-left stream (which already declares Acc, Eq, Nat) a
single theorem whose check forces a defeq step at which

  * proof irrelevance FAILS (the two comparands are proofs of NON-defeq
    propositions: a stuck `Acc.rec` application and its iota reduct's
    spelling), and
  * the very next rule, spine congruence, SUCCEEDS (same free-variable
    head `F`; the argument pair is `a` vs `Acc.intro x g`, two proofs of
    the *same* proposition `Acc r x`, which proof irrelevance equates in
    every kernel).

The official kernel COMMITS at the proof-irrelevance failure
(`type_checker.cpp:1202-1203`: a `l_false` from `is_def_eq_proof_irrel`
returns from `is_def_eq_core` outright), so it never reaches the
congruence and REJECTS.  lech's `proofIrrel` returns a `Bool` and a
`false` falls through to the rest of the cascade, which accepts.

  python3 scripts/mk_irrel_commit.py \
      _tmp/arena-tests/good/undecidability/alg-conv-trans-acc-left.ndjson \
      tests/e2e/irrel_commit.ndjson --minimal

usage: mk_irrel_commit.py <base.ndjson> <out.ndjson> [--minimal] [--type-motive]
   --minimal:      keep only the Acc and Eq inductive blocks
   --type-motive:  the DISCRIMINATING CONTROL — the identical shape with
                   a `Type`-valued motive, so the comparands are not
                   proofs, proof irrelevance never fires and no kernel
                   commits.  Official ACCEPTS this one (exit 0), which
                   is what isolates the divergence to the commit.
"""
import json, sys

base, out = sys.argv[1], sys.argv[2]
TYPEMOT = '--type-motive' in sys.argv
MINIMAL = '--minimal' in sys.argv

lines = [l.rstrip('\n') for l in open(base) if l.strip()]

names = {0: '_root_'}
maxn = maxe = maxl = 0
levels = {}
for l in lines:
    d = json.loads(l)
    if 'in' in d:
        i = d['in']; maxn = max(maxn, i)
        if 'str' in d:
            p = d['str']['pre']; names[i] = (names[p] + '.' if p else '') + d['str']['str']
        else:
            p = d['num']['pre']; names[i] = (names[p] + '.' if p else '') + str(d['num']['i'])
    if 'ie' in d: maxe = max(maxe, d['ie'])
    if 'il' in d:
        maxl = max(maxl, d['il'])
        levels[d['il']] = d

byname = {v: k for k, v in names.items()}
N_Eq = byname['Eq']; N_EqRefl = byname['Eq.refl']
N_Acc = byname['Acc']; N_AccIntro = byname['Acc.intro']; N_AccRec = byname['Acc.rec']

new = []
nctr = [maxn]; ectr = [maxe]; lctr = [maxl]

def nm(s, pre=0):
    nctr[0] += 1; i = nctr[0]
    new.append({"in": i, "str": {"pre": pre, "str": s}})
    return i

def lv(d):
    lctr[0] += 1; i = lctr[0]
    d = dict(d); d['il'] = i
    new.append(d)
    return i

def ex(d):
    ectr[0] += 1; i = ectr[0]
    d = dict(d); d['ie'] = i
    new.append(d)
    return i

L1 = lv({"succ": 0})
L2 = lv({"succ": L1})

def const(n, us=()):  return ex({"const": {"name": n, "us": list(us)}})
def app(f, a):        return ex({"app": {"fn": f, "arg": a}})
def appN(f, *args):
    for a in args: f = app(f, a)
    return f
def sort(l):          return ex({"sort": l})
def bvar(k):          return ex({"bvar": k})
def forallE(n, t, b): return ex({"forallE": {"binderInfo": "default", "name": n, "type": t, "body": b}})
def lam(n, t, b):     return ex({"lam": {"binderInfo": "default", "name": n, "type": t, "body": b}})

# ---- binder names
nThm = nm("irrelCommitControl" if TYPEMOT else "irrelCommit")
nA = nm("α'"); nR = nm("r'"); nX = nm("x'"); nPs = nm("Ps'"); nG = nm("g'")
nF = nm("F'"); nGG = nm("G'"); nAa = nm("a'")
nY = nm("y'"); nT = nm("t'"); nZ = nm("z'"); nHh = nm("hh'"); nIh = nm("ih'")
nP = nm("p'"); nHr = nm("hr'"); nQ = nm("q'")

SORT1 = sort(L1)
PROP = sort(0)

# The motive's VALUE: `Prop` (the divergence) or `Type` = `Sort 1` (the
# control).  `Ps : α → CODOM`.  The recursor's motive universe is the
# level of the motive's codomain, i.e. one above: `Prop : Sort 1`,
# `Type : Sort 2`.
def CODOM():
    return SORT1 if TYPEMOT else PROP
MOTLEVEL = L2 if TYPEMOT else L1

# de Bruijn helper: `env` is a list of binder names, innermost LAST.
def V(env, name):
    return bvar(len(env) - 1 - env.index(name))

def AccT(env, aT, rT, yT):
    """Acc.{1} α r y"""
    return appN(const(N_Acc, [L1]), aT, rT, yT)

def rApp(env, rT, y, x):
    return appN(rT, y, x)

def M(env, pT):
    """Acc.rec.{MOTLEVEL,1} α r (fun y t => CODOM) (fun z hh ih => Ps z) x p"""
    a = V(env, nA); r = V(env, nR); x = V(env, nX)
    e1 = env + [nY]
    mot = lam(nY, V(env, nA),
              lam(nT, AccT(e1, V(e1, nA), V(e1, nR), V(e1, nY)), CODOM()))
    ez = env + [nZ]
    ezy = ez + [nY]
    hhty = forallE(nY, V(ez, nA),
                   forallE(nHr, rApp(ezy, V(ezy, nR), V(ezy, nY), V(ezy, nZ)),
                           AccT(ezy + [nHr], V(ezy + [nHr], nA), V(ezy + [nHr], nR),
                                V(ezy + [nHr], nY))))
    ezh = ez + [nHh]
    ezhy = ezh + [nY]
    ihty = forallE(nY, V(ezh, nA),
                   forallE(nHr, rApp(ezhy, V(ezhy, nR), V(ezhy, nY), V(ezhy, nZ)), CODOM()))
    ezhi = ezh + [nIh]
    minor = lam(nZ, V(env, nA),
                lam(nHh, hhty,
                    lam(nIh, ihty, app(V(ezhi, nPs), V(ezhi, nZ)))))
    return appN(const(N_AccRec, [MOTLEVEL, L1]), a, r, mot, minor, x, pT)

# ---- the statement
# ∀ (α : Sort 1) (r : α → α → Prop) (x : α) (Ps : α → CODOM)
#   (g : (y:α) → r y x → Acc α r y)
#   (F : (p : Acc α r x) → M x p)
#   (G : (p : Acc α r x) → M x p → α)
#   (a : Acc α r x),
#   Eq.{1} α (G a (F a)) (G (Acc.intro α r x g) (F (Acc.intro α r x g)))

def build():
    e = [nA, nR, nX, nPs, nG, nF, nGG, nAa]

    intro = appN(const(N_AccIntro, [L1]), V(e, nA), V(e, nR), V(e, nX), V(e, nG))
    lhs = appN(V(e, nGG), V(e, nAa), app(V(e, nF), V(e, nAa)))
    rhs = appN(V(e, nGG), intro, app(V(e, nF), intro))
    body = appN(const(N_Eq, [L1]), V(e, nA), lhs, rhs)

    # a : Acc α r x
    e7 = e[:7]
    Aty = AccT(e7, V(e7, nA), V(e7, nR), V(e7, nX))
    t7 = forallE(nAa, Aty, body)
    # G : (p : Acc α r x) → M x p → α
    e6 = e[:6]
    e6p = e6 + [nP]
    GGty = forallE(nP, AccT(e6, V(e6, nA), V(e6, nR), V(e6, nX)),
                   forallE(nQ, M(e6p, V(e6p, nP)), V(e6p + [nQ], nA)))
    t6 = forallE(nGG, GGty, t7)
    # F : (p : Acc α r x) → M x p
    e5 = e[:5]
    e5p = e5 + [nP]
    Fty = forallE(nP, AccT(e5, V(e5, nA), V(e5, nR), V(e5, nX)),
                  M(e5p, V(e5p, nP)))
    t5 = forallE(nF, Fty, t6)
    # g : (y:α) → r y x → Acc α r y
    e4 = e[:4]
    e4y = e4 + [nY]
    e4yh = e4y + [nHr]
    gty = forallE(nY, V(e4, nA),
                  forallE(nHr, rApp(e4y, V(e4y, nR), V(e4y, nY), V(e4y, nX)),
                          AccT(e4yh, V(e4yh, nA), V(e4yh, nR), V(e4yh, nY))))
    t4 = forallE(nG, gty, t5)
    # Ps : α → CODOM
    e3 = e[:3]
    Psty = forallE(nY, V(e3, nA), CODOM())
    t3 = forallE(nPs, Psty, t4)
    # x : α
    e2 = e[:2]
    t2 = forallE(nX, V(e2, nA), t3)
    # r : α → α → Prop
    e1 = e[:1]
    rty = forallE(nY, V(e1, nA), forallE(nT, V(e1 + [nY], nA), PROP))
    t1 = forallE(nR, rty, t2)
    t0 = forallE(nA, SORT1, t1)

    # value: fun α r x Ps g F G a => Eq.refl.{1} α (G a (F a))
    v = appN(const(N_EqRefl, [L1]), V(e, nA),
             appN(V(e, nGG), V(e, nAa), app(V(e, nF), V(e, nAa))))
    doms = [(nAa, Aty), (nGG, GGty), (nF, Fty), (nG, gty), (nPs, Psty),
            (nX, V(e2, nA)), (nR, rty), (nA, SORT1)]
    for (n, ty) in doms:
        v = lam(n, ty, v)
    return t0, v

ty, val = build()
new.append({"thm": {"all": [nThm], "levelParams": [], "name": nThm, "type": ty, "value": val}})

KEEP = {'Acc', 'Eq'}
def keep(l):
    d = json.loads(l)
    if 'meta' in d or 'in' in d or 'il' in d or 'ie' in d: return True
    if not MINIMAL: return True
    if 'inductive' in d:
        return names[d['inductive']['types'][0]['name']] in KEEP
    return False

with open(out, 'w') as f:
    for l in lines:
        if keep(l): f.write(l + '\n')
    for d in new: f.write(json.dumps(d, separators=(',', ':')) + '\n')
print(f"wrote {out}: +{len(new)} records (thm {names.get(nThm, nThm)})")
