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

TWO MODES.

    scripts/pub-import-plan.py            the PLAN: run the fixpoint from the
                                          all-public tree and write
                                          $PUBPLAN_DIR/plan.json for
                                          scripts/pub-import-apply.py.
    scripts/pub-import-plan.py --check    the GATE (task #235): start from the
                                          tree's ACTUAL `public import` set
                                          and report every edge that is
                                          individually demotable.  Exit 1 if
                                          any is — the tree is then not at a
                                          local minimum.

The gate deliberately does NOT compare against a freshly computed plan: the
fixpoint is greedy, so its result depends on the order it tries edges in, and
a plan edge that is plain here and public there is not a finding.  "No public
import can be demoted on its own" is order-independent.

Inputs (regenerate with `tests/shake.sh`, which is this script's caller in the
standard battery):

    $PUBPLAN_DIR/census.tsv   lake env lean --run scripts/dead-census.lean <mods>
    $PUBPLAN_DIR/pub.tsv      lake env lean --run scripts/pub-iface.lean   <mods>

`$PUBPLAN_DIR` defaults to `_tmp/m3`.
"""
import re, subprocess, json, collections, os, sys

CHECK = '--check' in sys.argv[1:]
DIR   = os.environ.get('PUBPLAN_DIR', '_tmp/m3')

# THE PER-FILE FALLBACK (task #231 phase 3, kept by task #235).  The model is
# a filter on candidate demotions, never a claim, and two files' re-exports
# are reached by DOT-NOTATION, which no census row and no source-identifier
# scan can attribute to a module: `RecCtorsStored.cons` in Model/Install and
# a lemma of the Denote tier in Semantics/IndRecsCore.  Demoting these builds
# a tree whose `rfl`s stop closing, so they stay public and the gate must not
# ask for them again.
FALLBACK = {
    ('ConLeche.Model.Install',        'ConLeche.Model.Annot.BitExtend'),
    ('ConLeche.Model.Install',        'ConLeche.Semantics.ConstsBound'),
    ('ConLeche.Model.Install',        'ConLeche.Verify.Extend.Sibs'),
    ('ConLeche.Semantics.IndRecsCore','ConLeche.Verify.Denote.EnvExt'),
    ('ConLeche.Semantics.IndRecsCore','ConLeche.Verify.Denote.Levels'),
    # task #253: `PushChain` is an exposed `def … : Prop` whose BODY names
    # `NodupNames` (EnvBound); the model reads statements, not exposed
    # bodies, and the compiler wants the re-export.
    ('ConLeche.Verify.Cached.PushChain','ConLeche.Verify.EnvBound'),
    # task #285: `BasisGen` declares the `#annotate_basis` COMMAND, and
    # `TrustAxioms` invokes it through `BasisA`'s re-export.  A command
    # elaborator is registered, not named, so no census row attributes it —
    # demoting the line makes `TrustAxioms` fail to parse (`unexpected
    # token '#'`), which is task #235's third blind class seen from the
    # other side.  (The fixpoint is order-dependent: this edge became a
    # demotion candidate only when #285 changed the graph around it.)
    ('ConLeche.Kernel.BasisA','ConLeche.Kernel.BasisGen'),
}

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
for line in open(DIR+'/census.tsv'):
    p=line.rstrip('\n').split('\t')
    if len(p)<3: continue
    declmod[p[0]]=p[1]
for line in open(DIR+'/census.tsv'):
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
for line in open(DIR+'/pub.tsv'):
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

def violations(cl):
    """Every constraint the configuration `P` breaks, as a set of tokens."""
    out=set()
    for m in mods:
        cov=bit[m]
        pubcov=0
        for t in D[m]:
            cov |= cl[t]
            if t in P[m]: pubcov |= cl[t]
        if reach[m] & ~cov: out.add(('cover', m))
        if need[m] & ~pubcov: out.add(('pub', m))
        for j,b in enumerate(opens[m]):
            if not (b & cov): out.add(('open', m, j))
    return out

def ok(cl):
    return violations(cl) <= _OKBASE

# The STARTING tree is correct by construction — it is the tree that builds —
# so anything the model reports there is the MODEL's imprecision (an `open`
# picked out of a docstring line; a match auxiliary the census attributes to
# the module that first generated it).  Record those and require only that
# nothing gets worse — the model is a filter on candidate demotions, never a
# claim.
def _rebase(label):
    global _OKBASE
    _OKBASE=set()
    b=violations(closures())
    if b: print(f'model imprecision at {label} (ignored):', sorted(b))
    _OKBASE=b

_rebase('baseline')

frozen={m for m in mods
        if fileof[m] in UMBRELLA or fileof[m] in CLASSIC
        or fileof[m].startswith(FROZEN_PREFIX)}
# every module we are allowed to narrow MUST be covered by the census, or its
# dependency set is silently empty and the fixpoint will happily strip it bare
# (that is what an incomplete root list did on the first run: the whole
# `Frontend/*` cone had no rows and lost every re-export).
seen_mods={l.split('\t')[1] for l in open(DIR+'/census.tsv') if '\t' in l}
missing=[m for m in mods if m not in frozen and m not in seen_mods]
assert not missing, f'census does not cover: {missing[:6]} ({len(missing)} modules)'
tot=sum(len(D[m]) for m in mods)

if CHECK:
    # The tree as it stands: an edge is public iff its line says `public`.
    for m in mods:
        pubs=set()
        for _,ispub,ismeta,t in imports(fileof[m]):
            if ismeta or t.startswith(EXT) or t not in idx: continue
            if ispub: pubs.add(t)
        P[m]=pubs & set(D[m])
    _rebase('the tree as it stands')
    bad=[]
    for m in mods:
        if m in frozen: continue
        for t in sorted(P[m]):
            if (m,t) in FALLBACK: continue
            P[m].discard(t)
            if ok(closures()): bad.append((m,t))
            P[m].add(t)
    pub=sum(len(P[m]) for m in mods)
    if bad:
        print(f'DEMOTABLE `public import` ({len(bad)}) — `public import X` is for a '
              're-export something else\'s PUBLIC statement needs:')
        for m,t in bad: print(f'  {fileof[m]}: public import {t}')
        raise SystemExit(1)
    print(f'pub-imports: {pub} of {tot} in-tree edges public, none demotable '
          f'({len(FALLBACK)} dot-notation fallbacks)')
    raise SystemExit(0)

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
pub=sum(len(P[m]) for m in mods)
print(f'{pub} of {tot} in-tree import edges must stay public  ->  {tot-pub} narrow')
json.dump({m:sorted(P[m]) for m in mods}, open(DIR+'/plan.json','w'))
