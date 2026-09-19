#!/usr/bin/env bash
# tests/layering.sh — THE LAYERING GATE (task #161, S1; re-cut at the
# SetR removal, 2026-09-05).
#
# WHAT IT ENFORCED, AND WHAT IT ENFORCES NOW.  The gate was born as THE
# SEPARATION's fence: the user's ruling for campaign (B) was that the
# collapsed-model tree (`EnvS`, the R capstones) and the graded-model
# tree (the P capstone) be disjoint subtrees, no imports across in
# either direction, over a shared base.  The campaign closed at S8 with
# the whitelist EMPTY — zero P→R edges, zero R→P — and the user's
# 2026-09-05 ruling ("do remove the SetR tier, for more focus") then
# removed the collapsed lane outright.  **The disjointness is what made
# that removal a clean cut**: with no edge in either direction, deleting
# `ConLeche/SetR/*` touched exactly two consumers in the whole tree.
#
# With one model lane there is no cross-lane edge to gate, so the two
# lane clauses retire WITH THEIR SUBJECT (a row whose subject no longer
# exists is not a loosening).  What survives is the part of the fence
# that was never about the R/P split:
#   * any base→lane edge         (BASE PURITY — `ConLeche/{Kernel,Verify,
#     SetTheory,Term,SetModel,Semantics}/*` stand BELOW the model lane and may not
#     import `ConLeche/Model/*`), AND
#   * any implementation→theory edge   (the CLAUDE.md rule:
#     `ConLeche/{Kernel,Cached,Frontend}/*` and `Main.lean` may never
#     import `ConLeche/{SetTheory,SetModel,Semantics,Model,Verify}/*`).
# Both were always the load-bearing half.  Until task #305 a fourth
# instrument, `tests/proofdeps.sh`, pinned the module closure of the
# capstones' PROOF TERMS, on the reasoning that an import gate measures
# where code sits and only the proof term measures what a theorem uses.
# Under the module system that distinction is computable from source:
# the environment a proof elaborates in is exactly its module's direct
# imports plus, transitively, their `public import`s, so a proof term
# cannot reach a module outside that closure — the CLOSURE clause below
# (task #305 closing) states the bound the pin measured, and the pin
# retired with its 4,500-row expectation.
#
# WHY A SCRIPT AND NOT THE BUILD.  The design census proposed separate
# `lean_lib` targets as the fence ("cross-import = build error").  That
# is not what Lake does: import resolution is per *package*, so any
# module of the `con-leche` package may import any other regardless of
# which `lean_lib` roots it (today `ConLeche.Model.*` imports
# `ConLeche.Kernel.*` across exactly such a boundary, and builds).  A hard
# build error would need the lanes to become separate Lake *packages*.
# The lib split in `lakefile.toml` is therefore the LAYOUT; this gate is
# the FENCE.  It runs in the standard battery (`tests/arena.sh`), so the
# battery fails if the boundary rots.
#
# Usage: tests/layering.sh [--list]   (--list prints the current
# base→lane edges, i.e. the gate's live rot channel, then every rules
# module's elaboration closure with its doors marked `!`, and one
# witnessing chain per door).
set -u
cd "$(dirname "$0")/.."
exec python3 - "$@" <<'PYEOF'
import os, re, sys

# `public import X`, `meta import X` and `import all X` are all edges: the
# module system's visibility keywords change what an importer SEES, never
# whether it depends on the module, and `import all` is the WIDEST edge of
# the three (it pulls the private scope too), so the fence must count it.
IMP = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)

# --------------------------------------------------------------- the
# module graph.
mods = {}
for dirpath, _, files in os.walk('ConLeche'):
    for f in sorted(files):
        if f.endswith('.lean'):
            rel = os.path.join(dirpath, f)
            mods[rel[:-5].replace('/', '.')] = rel
for extra in ('ConLeche.lean', 'Main.lean'):
    if os.path.exists(extra):
        mods[extra[:-5]] = extra

edges = {}
for name, rel in mods.items():
    src = re.sub(r'/-.*?-/', '', open(rel).read(), flags=re.S)   # strip block comments
    edges[name] = [m for m in IMP.findall(src) if m in mods]

# --------------------------------------------------------------- the
# classification.  **BY PATH ALONE** since S2's `ConLeche/Model/*` move,
# and since the SetR removal there is no closure left to compute:
# `ConLeche/Model{,/*}` is the lane, `ConLeche/Verify/Cached{,/*}` is the
# capstone assembly, `ConLeche.lean` is the base umbrella, everything else
# is base.  (The old `neutral` class — a module under `ConLeche/SetR/`
# that no R capstone reached — retired with that directory.)
IMPL_DIRS   = ('ConLeche/Kernel/', 'ConLeche/Cached/', 'ConLeche/Frontend/')
IMPL_ROOTS  = ('Main',)
THEORY_PFX  = ('ConLeche.Verify.', 'ConLeche.SetTheory.',
               'ConLeche.Model.', 'ConLeche.SetModel.', 'ConLeche.Semantics.',
               'ConLeche.Term.')
CAPS        = {'ConLeche.Verify.Cached.MainC', 'ConLeche.Verify.Cached',
               'ConLeche.MainTheorem'}
UMBRELLAS   = {'ConLeche'}                  # `ConLeche.Model` is gated as the model lane

def lane(m):
    rel = mods[m]
    if m in CAPS:      return 'caps'
    if m in UMBRELLAS: return 'umbrella'
    if rel == 'ConLeche/Model.lean' or rel.startswith('ConLeche/Model/'): return 'model'
    return 'base'

LANE = {m: lane(m) for m in mods}

basev = sorted((a, b) for a in mods for b in edges[a]
               if LANE[a] == 'base' and LANE[b] == 'P')
implv = sorted((a, b) for a in mods for b in edges[a]
               if (mods[a].startswith(IMPL_DIRS) or a in IMPL_ROOTS)
               and b.startswith(THEORY_PFX))
# THE RULES FENCE (task #305).  The rules tier — the relational
# description of the core checker (`ConLeche/Rules/*`) and the soundness
# of its derivations (`ConLeche/Model/Rules/*`) — is stated over the
# checker's Expr syntax and its fuel-free helpers (`Kernel/CoreDefs`)
# and must not import the pure implementation: the bodies and the knot
# (`Kernel/Core`), the fueled entry points (`Kernel/TypeChecker`,
# `Kernel/CoreIO`), the declaration checker (`Kernel/Checker*`,
# `Kernel/DeclCheck`) or the cached tier (`Cached/*`).  The bridge
# (`ConLeche/Verify/Rules/*`) and the recomposition
# (`ConLeche/Model/Rules/Recompose.lean`) are the two places that see
# both sides, and are exempt by name.  A DIRECT-import fence, like the
# two above; the closure clause below is its transitive form.
RULES_DIRS  = ('ConLeche/Rules/', 'ConLeche/Model/Rules/')
RULES_EXEMPT = {'ConLeche.Model.Rules.Recompose'}
def impl_mod(b):
    return (b in ('ConLeche.Kernel.Core', 'ConLeche.Kernel.TypeChecker',
                  'ConLeche.Kernel.CoreIO', 'ConLeche.Kernel.DeclCheck',
                  'ConLeche.Cached')
            or b.startswith('ConLeche.Kernel.Checker')
            or b.startswith('ConLeche.Cached.'))
rulesv = sorted((a, b) for a in mods for b in edges[a]
                if mods[a].startswith(RULES_DIRS) and a not in RULES_EXEMPT
                and impl_mod(b))

# THE RULES FENCE, CLOSURE FORM (task #305 closing).  Under the module
# system the environment a module ELABORATES IN — what a statement or a
# proof term in it can mention — is its direct imports plus, transitively,
# their `public import`s (`import all` is a direct edge; a `meta import`
# is elaboration-time only and invisible to a proof).  The closure of a
# rules module along those edges is therefore the exact bound on what its
# proofs can reach, computed from source.  The clause: for every module
# under `ConLeche/Rules/` and `ConLeche/Model/Rules/` (the recomposition
# exempt as above) that closure contains no `Kernel/Core`,
# `Kernel/TypeChecker`, `Kernel/CoreIO`, `Kernel/Checker*`,
# `Kernel/DeclCheck`, `Cached/*` — EXCEPT the doors listed in
# RULES_CLOSURE_DOORS, which are the impl modules the base tiers' own
# public re-exports still carry into every model module (measured at the
# closing: `Model/Annot/EnvModel` → `Verify/EnvWF` →(public) `Kernel/Core`,
# `Verify/Denote` →(public) `Kernel/Checker`, `EnvModelM` → `Verify/ProjTele`
# → `ProjSlots` → `Abstract` → `Knot` →(public) `Kernel/CoreIO`, …; the
# DESIGN record of task #305's closing holds the full chain list and the
# repointing campaign that removes them).  The residue is EXACT in both
# directions: a door not listed is a regression and fails; a listed door
# no longer reached is progress that must be recorded by deleting its
# line, and also fails.  `--list` prints each rules module's closure with
# its doors marked, and one witnessing chain per door.
PUBIMP = re.compile(r'^\s*(?:public\s+)+import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)
DIRIMP = re.compile(r'^\s*(?:public\s+|private\s+)*import\s+(?:all\s+)?([A-Za-z0-9_.]+)', re.M)
pubedges, diredges = {}, {}
for name, rel in mods.items():
    src = re.sub(r'/-.*?-/', '', open(rel).read(), flags=re.S)
    pubedges[name] = [m for m in PUBIMP.findall(src) if m in mods]
    diredges[name] = [m for m in DIRIMP.findall(src) if m in mods]

def closure_with_parents(m):
    """the elaboration environment of `m`, and for each member the edge it
    entered through (first hop: any non-meta import; later hops: public
    imports only)"""
    parent, todo = {}, []
    for x in diredges[m]:
        if x not in parent: parent[x] = m; todo.append(x)
    while todo:
        x = todo.pop()
        for y in pubedges[x]:
            if y not in parent: parent[y] = x; todo.append(y)
    return parent

def chain_to(parent, m, t):
    ch = [t]
    while ch[-1] != m: ch.append(parent[ch[-1]])
    return ' <- '.join(ch)

RULES_CLOSURE_DOORS = {
    'ConLeche.Kernel.Core',
    'ConLeche.Kernel.TypeChecker',
    'ConLeche.Kernel.CoreIO',
    'ConLeche.Kernel.Checker',
    'ConLeche.Kernel.CheckerBase',
}
rules_mods = sorted(m for m in mods if mods[m].startswith(RULES_DIRS)
                    and m not in RULES_EXEMPT)
rules_closure = {m: closure_with_parents(m) for m in rules_mods}
doors_seen = {}
for m in rules_mods:
    for t in rules_closure[m]:
        if impl_mod(t):
            doors_seen.setdefault(t, (m, chain_to(rules_closure[m], m, t)))
new_doors  = sorted(t for t in doors_seen if t not in RULES_CLOSURE_DOORS)
gone_doors = sorted(t for t in RULES_CLOSURE_DOORS if t not in doors_seen)

if '--list' in sys.argv[1:]:
    for a, b in basev:
        print(f'{a} -> {b}')
    for m in rules_mods:
        par = rules_closure[m]
        marks = ' '.join(('!' if impl_mod(x) else '') + x for x in sorted(par))
        print(f'closure {m} ({len(par)}): {marks}')
    for t, (m, ch) in sorted(doors_seen.items()):
        print(f'door {t}: {ch}')
    sys.exit(0)

fail = 0
def report(title, items, hint):
    global fail
    if items:
        fail = 1
        print(f'LAYERING FAIL — {title} ({len(items)}):')
        for a, b in items:
            print(f'    {a} -> {b}')
        print(f'    {hint}')

report('base module importing the model lane', basev,
       'ConLeche/{Kernel,Verify,SetTheory,Term,SetModel,Semantics}/* stand BELOW the '
       'lane; nothing there may import ConLeche/Model/*.')
report('implementation importing theory', implv,
       'CLAUDE.md: ConLeche/Kernel/*, Main.lean must never import '
       'ConLeche/{SetTheory,SetModel,Semantics,Model,Verify}/*.')
report('rules tier importing the pure implementation', rulesv,
       'task #305: ConLeche/Rules/* and ConLeche/Model/Rules/* are stated '
       'over Kernel/CoreDefs and may not import Kernel/{Core,TypeChecker,'
       'CoreIO,Checker*,DeclCheck} or Cached/*.')
report('rules tier CLOSURE reaching an unlisted implementation module',
       [(doors_seen[t][0], t) for t in new_doors] +
       [('  via', doors_seen[t][1]) for t in new_doors],
       'task #305 closing: a new public re-export carries the impl into the '
       'rules tier\'s elaboration environment; repoint it (see --list).')
report('rules tier CLOSURE door no longer reached (record the progress)',
       [('RULES_CLOSURE_DOORS', t) for t in gone_doors],
       'delete the door from RULES_CLOSURE_DOORS in this script and say so '
       'in the DESIGN record.')

n = {l: sum(1 for m in LANE if LANE[m] == l)
     for l in ("base", "model", "caps", "umbrella")}
if not fail:
    print(f'layering: base {n["base"]} / model {n["model"]} / caps {n["caps"]} / '
          f'umbrella {n["umbrella"]} modules; '
          f'{len(basev)} base->lane edges, {len(implv)} impl->theory, '
          f'{len(rulesv)} rules->impl; rules closure: {len(rules_mods)} modules, '
          f'{len(doors_seen)} doors as listed')
sys.exit(fail)
PYEOF
