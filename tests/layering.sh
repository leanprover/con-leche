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
# lane clauses retire WITH THEIR SUBJECT (the same ratchet rule the
# proofdeps pin states: a row whose subject no longer exists is not a
# loosening).  What survives is the part of the fence that was never
# about the R/P split:
#   * any base→lane edge         (BASE PURITY — `ConLeche/{Kernel,Verify,
#     SetTheory,Term,SetModel,Semantics}/*` stand BELOW the model lane and may not
#     import `ConLeche/Model/*`), AND
#   * any implementation→theory edge   (the CLAUDE.md rule:
#     `ConLeche/{Kernel,Cached,Frontend}/*` and `Main.lean` may never
#     import `ConLeche/{SetTheory,SetModel,Semantics,Model,Verify}/*`).
# Both were always the load-bearing half — S9's finding was precisely
# that the R/P clause measured where code SITS, and only
# `tests/proofdeps.sh` (the proof-term criterion) certifies a proof-path
# property.  That gate is unchanged by the removal.
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
# base→lane edges, i.e. the gate's live rot channel).
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

if '--list' in sys.argv[1:]:
    for a, b in basev:
        print(f'{a} -> {b}')
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

n = {l: sum(1 for m in LANE if LANE[m] == l)
     for l in ("base", "model", "caps", "umbrella")}
if not fail:
    print(f'layering: base {n["base"]} / model {n["model"]} / caps {n["caps"]} / '
          f'umbrella {n["umbrella"]} modules; '
          f'{len(basev)} base->lane edges, {len(implv)} impl->theory')
sys.exit(fail)
PYEOF
