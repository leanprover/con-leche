#!/usr/bin/env python3
"""Phase 3's plan: which import edges may stop being `public`.

TWO constraints, both of them about the PUBLIC closure — a private import
gives the importer the imported module's public interface and nothing more:

  coverage   for every constant a module mentions ANYWHERE (proof terms
             included), some DIRECT import of it must carry that constant
             publicly.  This is what the first attempt missed: demoting an
             edge three tiers down breaks a module that never mentions it.
  publicness a module's import must be PUBLIC when the module's own public
             interface (scripts/pub-iface.lean) needs something that import
             carries.

Everything starts public; an edge is demoted only when neither constraint
breaks anywhere.  The build is the confirmation, not the search.
"""
import re, subprocess, json, collections

files=[f for f in subprocess.check_output(['git','ls-files','*.lean']).decode().split()
       if not f.startswith(('tests/e2e/src/','tests/trust-surface/','_probe/','bridge/','scripts/'))]
mod=lambda f: f[:-5].replace('/','.')
fileof={mod(f):f for f in files}
UMBRELLA={'ConLeche.lean','ConLeche/Term.lean','ConLeche/SetModel.lean','ConLeche/Semantics.lean',
          'ConLeche/Model.lean','ConLeche/Verify/Cached.lean','ConLeche/Verify/Denote.lean',
          'ConLeche/Kernel/Basis.lean'}
# frozen: the umbrellas exist to re-export, the classic roots have no `public`
# keyword, `tests/*` and the PinGen generator are outside the census roots.
CLASSIC={'tests/ProofDeps.lean','PinDump.lean'}
FROZEN_PREFIX=('tests/','ConLeche/PinGen/','ConLeche/Challenge.lean','ConLeche/PinGen.lean')
EXT=('Std','Lean','Init')

def imports(f):
    out=[]
    for i,l in enumerate(open(f).read().split('\n')):
        m=re.match(r'^(public\s+)?(meta\s+)?import\s+(all\s+)?([A-Za-z0-9_.]+)\s*$', l)
        if m and not m.group(3):
            out.append((i, bool(m.group(1)), bool(m.group(2)), m.group(4)))
    return out

mods=sorted(fileof)
idx={m:i for i,m in enumerate(mods)}
bit={m:1<<i for m,i in idx.items()}

# --- the graph: every non-meta, non-external import edge
D={m:[] for m in mods}
for m in mods:
    for _,_,ismeta,t in imports(fileof[m]):
        if ismeta or t.startswith(EXT): continue
        if t in idx: D[m].append(t)

# --- reach: every module whose constants this module mentions at all
declmod={}
deps=collections.defaultdict(set)
for line in open('_tmp/m3/census.tsv'):
    p=line.rstrip('\n').split('\t')
    if len(p)<3: continue
    declmod[p[0]]=p[1]
for line in open('_tmp/m3/census.tsv'):
    p=line.rstrip('\n').split('\t')
    if len(p)<4: continue
    for c in p[3].split():
        dm=declmod.get(c)
        if dm and dm in idx and dm!=p[1]: deps[p[1]].add(dm)
reach={m: 0 for m in mods}
for m,s in deps.items():
    if m in idx: reach[m]=sum(bit[x] for x in s if x in idx)

# --- opens: a bare `open N` needs N to EXIST in this module's view, which
# means some module in its cover must declare a constant under that prefix.
# (DESIGN #223 records this as the criterion `shake` misses.)
nsmods=collections.defaultdict(set)
for n,dm in declmod.items():
    parts=n.split('.')
    for k in range(1,len(parts)):
        nsmods['.'.join(parts[:k])].add(dm)
opens={}
for m in mods:
    src=open(fileof[m]).read()
    ns=set()
    for mm in re.finditer(r'^\s*open\s+([^\n]*)', src, re.M):
        seg=mm.group(1).split('--')[0]
        seg=re.sub(r'\(.*?\)','',seg)
        for tok in seg.replace(' in','').split():
            if re.fullmatch(r'[A-Za-z_][A-Za-z0-9_.]*', tok) and tok not in ('in','scoped'):
                ns.add(tok)
    opens[m]=[sum(bit[x] for x in nsmods.get(n,()) if x in idx) for n in sorted(ns)]
    opens[m]=[b for b in opens[m] if b]

# --- source identifiers: a lemma named in a TACTIC argument (`simp [f]`,
# `exact h`, …) need not appear in the resulting proof term, so the census
# does not see it.  Add every identifier the source mentions whose name has a
# unique declaring module.  This can only keep MORE imports public, never
# fewer — soundness over aggressiveness.
sufmods=collections.defaultdict(set)
for n,dm in declmod.items():
    if dm not in idx: continue
    parts=n.split('.')
    for k in range(len(parts)):
        sufmods['.'.join(parts[k:])].add(dm)
srcneed={}
for m in mods:
    src=open(fileof[m]).read()
    acc=0
    for tok in set(re.findall(r"[A-Za-z_][A-Za-z0-9_.'!?]*", src)):
        ms=sufmods.get(tok)
        if ms and len(ms)==1:
            d=next(iter(ms))
            if d!=m: acc |= bit[d]
    srcneed[m]=acc

need={m:0 for m in mods}
for line in open('_tmp/m3/pub.tsv'):
    if '\t' not in line: continue
    m,rest=line.rstrip('\n').split('\t',1)
    if m in idx: need[m]=sum(bit[x] for x in rest.split() if x in idx)

# --- topological order
order=[]; seen=set()
def visit(m, st=()):
    if m in seen or m in st: return
    for t in D[m]: visit(t, st+(m,))
    seen.add(m); order.append(m)
for m in mods: visit(m)

# A module can only depend on what it imports.  The census walks the FINAL
# environment and adds `@[csimp]`/`@[implemented_by]` edges, which an attribute
# in a LATER module can create — those are not import edges and show up as
# impossible backwards dependencies (`Kernel/ExprOps` "needing" `Verify/Level`).
# Restrict both sets to each module's real transitive import closure.
allcl={}
for m in order:
    acc=bit[m]
    for t in D[m]: acc |= allcl.get(t, bit.get(t,0))
    allcl[m]=acc
for m in mods:
    reach[m] = (reach[m] | srcneed[m]) & allcl[m]
    need[m]  &= allcl[m]

P={m:set(D[m]) for m in mods}                    # public imports; start: all

def closures():
    cl={}
    for m in order:
        acc=bit[m]
        for t in P[m]:
            acc |= cl.get(t, bit.get(t,0))
        cl[m]=acc
    return cl

_OKBASE=set()

def ok(cl):
    for m in mods:
        cov=bit[m]
        pubcov=0
        for t in D[m]:
            cov |= cl[t]
            if t in P[m]: pubcov |= cl[t]
        if reach[m] & ~cov: return False
        if need[m] & ~pubcov: return False
        for j,b in enumerate(opens[m]):
            if (m,j) in _OKBASE: continue
            if not (b & cov): return False
    return True

# The all-public tree is correct by construction, so anything the model
# reports there is the MODEL's imprecision (an `open` picked out of a
# docstring line, say).  Record those and require only that nothing gets
# worse — the model is a filter on candidate demotions, never a claim.
_cl=closures()
_base=set()
for m in mods:
    cov=bit[m]
    for t in D[m]: cov |= _cl[t]
    for j,b in enumerate(opens[m]):
        if not (b & cov): _base.add((m,j))
if _base: print('model imprecision at baseline (ignored):', sorted(_base))
_OKBASE=_base

frozen={m for m in mods
        if fileof[m] in UMBRELLA or fileof[m] in CLASSIC
        or fileof[m].startswith(FROZEN_PREFIX)}
# every module we are allowed to narrow MUST be covered by the census, or its
# dependency set is silently empty and the fixpoint will happily strip it bare
# (that is what an incomplete root list did on the first run: the whole
# `Frontend/*` cone had no rows and lost every re-export).
seen_mods={l.split('\t')[1] for l in open('_tmp/m3/census.tsv') if '\t' in l}
missing=[m for m in mods if m not in frozen and m not in seen_mods]
assert not missing, f'census does not cover: {missing[:6]} ({len(missing)} modules)'
changed=True
while changed:
    changed=False
    for m in reversed(order):                    # importers first
        if m in frozen: continue
        for t in sorted(P[m]):
            P[m].discard(t)
            if ok(closures()):
                changed=True
            else:
                P[m].add(t)
tot=sum(len(D[m]) for m in mods)
pub=sum(len(P[m]) for m in mods)
print(f'{pub} of {tot} in-tree import edges must stay public  ->  {tot-pub} narrow')
json.dump({m:sorted(P[m]) for m in mods}, open('_tmp/m3/plan.json','w'))
