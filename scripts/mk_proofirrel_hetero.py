#!/usr/bin/env python3
"""Build the proof-irrelevance heterogeneity fixture.

Appends to the arena's alg-conv-trans-acc-left stream (which already
declares Acc, Eq, Nat) a single theorem whose check forces setlec's
`proofIrrel` to compare two proofs of NON-defeq propositions:

  h1 : Acc.rec (fun _ _ => Prop) (fun z _ _ => Ps z) x a     -- stuck (a is a variable)
  h2 : Ps x                                                   -- the iota reduct's spelling

Both are Prop-sorted, so setlec's proofIrrel returns true without ever
comparing the two types; the official kernel's is_def_eq(t_type,s_type)
compares them, fails (the left one is a stuck Acc.rec), and REJECTS.

The shipped fixture is built from the arena's
`good/undecidability/alg-conv-trans-acc-left.ndjson` snapshot with
`--minimal` (every declaration but the `Acc` and `Eq` inductive blocks
dropped; the sparse name/level/expr tables are kept as-is):

  python3 scripts/mk_proofirrel_hetero.py \
      _tmp/arena-tests/good/undecidability/alg-conv-trans-acc-left.ndjson \
      tests/e2e/proof_irrel_hetero.ndjson --minimal

usage: mk_proofirrel_hetero.py <base.ndjson> <out.ndjson> [--minimal] [--same-type]
   --minimal:   keep only the Acc and Eq inductive blocks
   --same-type: variant with h2 : M x a (rejected by both kernels for a
                DIFFERENT reason — whnfCore reduces the constructor side
                before congruence can run, so it is not a control)
"""
import json, sys

base, out = sys.argv[1], sys.argv[2]
SAME = '--same-type' in sys.argv
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

# level 1 = succ 0
L1 = lv({"succ": 0})

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
nDiv = nm("propIrrelHetero")
nA = nm("α'"); nR = nm("r'"); nX = nm("x'"); nPs = nm("Ps"); nG = nm("g'")
nE = nm("E'"); nAa = nm("a'"); nH1 = nm("h1'"); nH2 = nm("h2'")
nY = nm("y'"); nT = nm("t'"); nZ = nm("z'"); nHh = nm("hh'"); nIh = nm("ih'")
nP = nm("p'"); nHr = nm("hr'")

SORT1 = sort(L1)
PROP = sort(0)

# de Bruijn helper: `env` is a list of binder names, innermost LAST.
def V(env, name):
    return bvar(len(env) - 1 - env.index(name))

def AccT(env, aT, rT, yT):
    """Acc.{1} α r y"""
    return appN(const(N_Acc, [L1]), aT, rT, yT)

def rApp(env, rT, y, x):
    return appN(rT, y, x)

def M(env, pT):
    """Acc.rec.{1,1} α r (fun y t => Prop) (fun z hh ih => Ps z) x p"""
    a = V(env, nA); r = V(env, nR); x = V(env, nX)
    # motive : (y : α) -> (t : Acc α r y) -> Sort 1   [value Prop]
    e1 = env + [nY]
    mot = lam(nY, V(env, nA),
              lam(nT, AccT(e1, V(e1, nA), V(e1, nR), V(e1, nY)), PROP))
    # minor : (z : α) -> (hh : (y:α) -> r y z -> Acc α r y)
    #                 -> (ih : (y:α) -> r y z -> Prop) -> Prop  [value Ps z]
    ez = env + [nZ]
    ezy = ez + [nY]
    hhty = forallE(nY, V(ez, nA),
                   forallE(nHr, rApp(ezy, V(ezy, nR), V(ezy, nY), V(ezy, nZ)),
                           AccT(ezy + [nHr], V(ezy + [nHr], nA), V(ezy + [nHr], nR),
                                V(ezy + [nHr], nY))))
    ezh = ez + [nHh]
    ezhy = ezh + [nY]
    ihty = forallE(nY, V(ezh, nA),
                   forallE(nHr, rApp(ezhy, V(ezhy, nR), V(ezhy, nY), V(ezhy, nZ)), PROP))
    ezhi = ezh + [nIh]
    minor = lam(nZ, V(env, nA),
                lam(nHh, hhty,
                    lam(nIh, ihty, app(V(ezhi, nPs), V(ezhi, nZ)))))
    return appN(const(N_AccRec, [L1, L1]), a, r, mot, minor, x, pT)

# ---- the statement
# ∀ (α : Sort 1) (r : α → α → Prop) (x : α) (Ps : α → Prop)
#   (g : (y:α) → r y x → Acc α r y)
#   (E : (p : Acc α r x) → M x p → α)
#   (a : Acc α r x) (h1 : M x a) (h2 : Ps x),
#   Eq.{1} α (E a h1) (E (Acc.intro α r x g) h2)

def build(env_out):
    e = [nA, nR, nX, nPs, nG, nE, nAa, nH1, nH2]
    a = lambda en: V(en, nA)
    # body
    Ea_h1 = appN(V(e, nE), V(e, nAa), V(e, nH1))
    intro = appN(const(N_AccIntro, [L1]), V(e, nA), V(e, nR), V(e, nX), V(e, nG))
    Eb_h2 = appN(V(e, nE), intro, V(e, nH2))
    body = appN(const(N_Eq, [L1]), V(e, nA), Ea_h1, Eb_h2)

    # h2 : Ps x   (or M x a for the control)
    e8 = e[:8]
    h2ty = app(V(e8, nPs), V(e8, nX)) if not SAME else M(e8, V(e8, nAa))
    t8 = forallE(nH2, h2ty, body)
    # h1 : M x a
    e7 = e[:7]
    t7 = forallE(nH1, M(e7, V(e7, nAa)), t8)
    # a : Acc α r x
    e6 = e[:6]
    t6 = forallE(nAa, AccT(e6, V(e6, nA), V(e6, nR), V(e6, nX)), t7)
    # E : (p : Acc α r x) → M x p → α
    e5 = e[:5]
    e5p = e5 + [nP]
    Ety = forallE(nP, AccT(e5, V(e5, nA), V(e5, nR), V(e5, nX)),
                  forallE(nH1, M(e5p, V(e5p, nP)), V(e5p + [nH1], nA)))
    t5 = forallE(nE, Ety, t6)
    # g : (y:α) → r y x → Acc α r y
    e4 = e[:4]
    e4y = e4 + [nY]
    e4yh = e4y + [nHr]
    gty = forallE(nY, V(e4, nA),
                  forallE(nHr, rApp(e4y, V(e4y, nR), V(e4y, nY), V(e4y, nX)),
                          AccT(e4yh, V(e4yh, nA), V(e4yh, nR), V(e4yh, nY))))
    t4 = forallE(nG, gty, t5)
    # Ps : α → Prop
    e3 = e[:3]
    t3 = forallE(nPs, forallE(nY, V(e3, nA), PROP), t4)
    # x : α
    e2 = e[:2]
    t2 = forallE(nX, V(e2, nA), t3)
    # r : α → α → Prop
    e1 = e[:1]
    rty = forallE(nY, V(e1, nA), forallE(nT, V(e1 + [nY], nA), PROP))
    t1 = forallE(nR, rty, t2)
    t0 = forallE(nA, SORT1, t1)

    # value: fun α r x Ps g E a h1 h2 => Eq.refl.{1} α (E a h1)
    v9 = appN(const(N_EqRefl, [L1]), V(e, nA), appN(V(e, nE), V(e, nAa), V(e, nH1)))
    v = v9
    # rebuild the lambda telescope with the same domains
    doms = [(nH2, h2ty, e8), (nH1, M(e7, V(e7, nAa)), e7),
            (nAa, AccT(e6, V(e6, nA), V(e6, nR), V(e6, nX)), e6),
            (nE, Ety, e5), (nG, gty, e4),
            (nPs, forallE(nY, V(e3, nA), PROP), e3),
            (nX, V(e2, nA), e2), (nR, rty, e1), (nA, SORT1, [])]
    for (n, ty, _) in doms:
        v = lam(n, ty, v)
    return t0, v

ty, val = build(None)
new.append({"thm": {"all": [nDiv], "levelParams": [], "name": nDiv, "type": ty, "value": val}})

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
print(f"wrote {out}: +{len(new)} records (thm {names.get(nDiv, 'propIrrelHetero')})")
