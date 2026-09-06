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
# `Setlec/SetR/*` touched exactly two consumers in the whole tree.
#
# With one model lane there is no cross-lane edge to gate, so the two
# lane clauses retire WITH THEIR SUBJECT (the same ratchet rule the
# proofdeps pin states: a row whose subject no longer exists is not a
# loosening).  What survives is the part of the fence that was never
# about the R/P split:
#   * any base→lane edge         (BASE PURITY — `Setlec/{Kernel,Verify,
#     SetTheory,TT,SetModel,Semantics}/*` stand BELOW the model lane and may not
#     import `Setlec/SetP/*`), AND
#   * any implementation→theory edge   (the CLAUDE.md rule:
#     `Setlec/{Kernel,Cached,Frontend}/*` and `Main.lean` may never
#     import `Setlec/{SetTheory,SetModel,Semantics,SetP,Verify}/*`).
# Both were always the load-bearing half — S9's finding was precisely
# that the R/P clause measured where code SITS, and only
# `tests/proofdeps.sh` (the proof-term criterion) certifies a proof-path
# property.  That gate is unchanged by the removal.
#
# WHY A SCRIPT AND NOT THE BUILD.  The design census proposed separate
# `lean_lib` targets as the fence ("cross-import = build error").  That
# is not what Lake does: import resolution is per *package*, so any
# module of the `setlec` package may import any other regardless of
# which `lean_lib` roots it (today `Setlec.SetP.*` imports
# `Setlec.Kernel.*` across exactly such a boundary, and builds).  A hard
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

IMP = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+([A-Za-z0-9_.]+)', re.M)

# --------------------------------------------------------------- the
# module graph.
mods = {}
for dirpath, _, files in os.walk('Setlec'):
    for f in sorted(files):
        if f.endswith('.lean'):
            rel = os.path.join(dirpath, f)
            mods[rel[:-5].replace('/', '.')] = rel
for extra in ('Setlec.lean', 'Main.lean'):
    if os.path.exists(extra):
        mods[extra[:-5]] = extra

edges = {}
for name, rel in mods.items():
    src = re.sub(r'/-.*?-/', '', open(rel).read(), flags=re.S)   # strip block comments
    edges[name] = [m for m in IMP.findall(src) if m in mods]

# --------------------------------------------------------------- the
# classification.  **BY PATH ALONE** since S2's `Setlec/SetP/*` move,
# and since the SetR removal there is no closure left to compute:
# `Setlec/SetP{,/*}` is the lane, `Setlec/Verify/Cached{,/*}` is the
# capstone assembly, `Setlec.lean` is the base umbrella, everything else
# is base.  (The old `neutral` class — a module under `Setlec/SetR/`
# that no R capstone reached — retired with that directory.)
IMPL_DIRS   = ('Setlec/Kernel/', 'Setlec/Cached/', 'Setlec/Frontend/')
IMPL_ROOTS  = ('Main',)
THEORY_PFX  = ('Setlec.Verify.', 'Setlec.SetTheory.',
               'Setlec.SetP.', 'Setlec.SetModel.', 'Setlec.Semantics.',
               'Setlec.TT.')
CAPS        = {'Setlec.Verify.Cached.MainC', 'Setlec.Verify.Cached'}
UMBRELLAS   = {'Setlec'}                  # `Setlec.SetP` is gated as P

def lane(m):
    rel = mods[m]
    if m in CAPS:      return 'caps'
    if m in UMBRELLAS: return 'umbrella'
    if rel == 'Setlec/SetP.lean' or rel.startswith('Setlec/SetP/'): return 'P'
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
       'Setlec/{Kernel,Verify,SetTheory,TT,SetModel,Semantics}/* stand BELOW the '
       'lane; nothing there may import Setlec/SetP/*.')
report('implementation importing theory', implv,
       'CLAUDE.md: Setlec/Kernel/*, Main.lean must never import '
       'Setlec/{SetTheory,SetModel,Semantics,SetP,Verify}/*.')

n = {l: sum(1 for m in LANE if LANE[m] == l)
     for l in ("base", "P", "caps", "umbrella")}
if not fail:
    print(f'layering: base {n["base"]} / P {n["P"]} / caps {n["caps"]} / '
          f'umbrella {n["umbrella"]} modules; '
          f'{len(basev)} base->lane edges, {len(implv)} impl->theory')
sys.exit(fail)
PYEOF
