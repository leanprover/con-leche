#!/usr/bin/env bash
# tests/layering.sh — THE SEPARATION's layering gate (task #161, S1).
#
# The user's ruling for campaign (B): the collapsed-model tree (`EnvS`,
# the R capstones) and the graded-model tree (the P capstone) are
# disjoint subtrees, NO imports across in either direction, over a
# shared base.  This script is that boundary's ENFORCEMENT.
#
# WHY A SCRIPT AND NOT THE BUILD.  The design census proposed separate
# `lean_lib` targets as the fence ("cross-import = build error").  That
# is not what Lake does: import resolution is per *package*, so any
# module of the `setlec` package may import any other regardless of
# which `lean_lib` roots it (today `Setlec.SetR.*` imports
# `Setlec.Kernel.*` across exactly such a boundary, and builds).  A hard
# build error would need the lanes to become separate Lake *packages*.
# The lib split in `lakefile.toml` is therefore the LAYOUT; this gate is
# the FENCE.  It runs in the standard battery (`tests/arena.sh`), so the
# battery fails if the boundary rots.
#
# THE RATCHET.  The separation lands over batches S1–S5, so a number of
# P→R edges still exist.  They are listed below, each tagged with the
# batch that removes it.  The gate fails on
#   * any P→R edge that is NOT on the whitelist   (new rot), AND
#   * any whitelist entry whose edge is GONE      (stale ledger —
#     delete the line in the batch that killed it), AND
#   * any R→P edge at all                          (zero since S1), AND
#   * any base→lane edge                           (base purity), AND
#   * any implementation→theory edge               (the CLAUDE.md rule).
# The whitelist may only ever shrink.
#
# Usage: tests/layering.sh [--list]   (--list prints the current edges
# in whitelist syntax, for updating the table after a batch).
set -u
cd "$(dirname "$0")/.."
exec python3 - "$@" <<'PYEOF'
import os, re, sys

# ---------------------------------------------------------------- the
# whitelist: P→R edges that still exist, each tagged with the batch that
# removes it.  Format: "<importer> -> <imported>  # <batch>: <why>".
WHITELIST = """
# --- the 2U/denote2 lane: ALL FIFTEEN EDGES CLOSED BY S2.  The ruling
# (design review pt 1) was that the 2U lane goes to R whole, so every
# P-quarter dependence on it was a crossing; S2 re-based what both
# lanes actually shared (17 modules and 9 lemma families to
# `Setlec/SetBase/*`) and the section is empty.
# --- the de-basing proper: `EnvS2Core.base : EnvS` and the P carriers
# that reach the collapsed carrier through it (spec point 2).  S3
# de-based `EnvS2Core` itself and cut its edge; what is left is the
# fold-layer residue `EnvS2PM.base`, which S4/S5 delete with the v1
# install round trip.  The census's "ONE hard residue" (S7,
# `EnvS.empty_pinned` at the capstone's Empty key) is no longer an edge:
# `acval_empty_pinnedC` takes the pin as a premise in exactly the shape
# §1.5's carrier field will project, and the fold supplies it from the
# residue.
Setlec.SetP.Annot.EnvS2P -> Setlec.SetR.Interp2.EnvS2U                  # S4-S5: the v1 residue `EnvS2PM.base`, all that is left of `base : EnvS` (S3 de-based the CORE; the residue dies with the install round trip)
# --- the v1 install round trip (census §1.3's 47 sites): the P side
# calls a v1 install lemma only to build the new `EnvS`.  The premises
# vanish with the de-basing, and with them the imports.
Setlec.SetP.AxiomPinP -> Setlec.SetR.StdAxiomKey                # S3: propextKeyS_mem/choiceKeyS_mem at the axiom pin
Setlec.SetP.BasisEmptyP -> Setlec.SetR.Install.BasisS           # S3: extendEmptyS
Setlec.SetP.IndMemberP -> Setlec.SetR.Install.IndMembersS       # S3: indMemberS/memberKeyS base builders
# --- the bridge: the records are SHARED, the derivations are R's.
Setlec.SetP.FoldP -> Setlec.SetR.Bridge.Sound                   # S4: checkDeclRun_sound + declEtaStep (census C3/C4)
Setlec.SetP.NatEqsP -> Setlec.SetR.Bridge.Decl                  # S4: natEqFrame_of_frag + the DeclR record family to the shared base
"""

IMP = re.compile(r'^\s*(?:public\s+|private\s+|meta\s+)*import\s+([A-Za-z0-9_.]+)', re.M)

# --------------------------------------------------------------- the
# module graph.
mods = {}
for dirpath, _, files in os.walk('Setlec'):
    for f in sorted(files):
        if f.endswith('.lean'):
            rel = os.path.join(dirpath, f)
            mods[rel[:-5].replace('/', '.')] = rel
for extra in ('Setlec.lean', 'Main.lean', 'AnnotateBasis.lean'):
    if os.path.exists(extra):
        mods[extra[:-5]] = extra

edges = {}
for name, rel in mods.items():
    src = re.sub(r'/-.*?-/', '', open(rel).read(), flags=re.S)   # strip block comments
    edges[name] = [m for m in IMP.findall(src) if m in mods]

def closure(roots):
    seen, stack = set(), list(roots)
    while stack:
        m = stack.pop()
        if m in seen:
            continue
        seen.add(m)
        stack.extend(edges.get(m, []))
    return seen

# --------------------------------------------------------------- the
# lane classification.  **BY PATH ALONE** since S2's `Setlec/SetP/*`
# move: `Setlec/SetBase/*` is base, `Setlec/SetP{,/*}` is P,
# `Setlec/SetR/*` is R, everything else is base.  S1 had to compute the
# graded lane as `closure(P roots) minus closure(R roots)` because both
# lanes lived in the same directories; that closure rule is gone, and
# with it the P root list (the S1 seal's succession note called this).
#
# What survives of the closure machinery: the R side still uses it to
# spot a module under `Setlec/SetR/` that NO R capstone reaches
# (`neutral`) — such a module is checked to import no lane content, and
# must otherwise be assigned to `ROOTS_R` by name.
IMPL_DIRS   = ('Setlec/Kernel/', 'Setlec/Cached/', 'Setlec/Frontend/')
IMPL_ROOTS  = ('Main', 'AnnotateBasis')
THEORY_PFX  = ('Setlec.Verify.', 'Setlec.SetTheory.', 'Setlec.SetR.',
               'Setlec.SetP.', 'Setlec.SetBase.', 'Setlec.TT.')
CAPS        = {'Setlec.Verify.Cached.MainC', 'Setlec.Verify.Cached'}
UMBRELLAS   = {'Setlec.SetR', 'Setlec'}   # `Setlec.SetP` is gated as P

# The collapsed lane's roots: the R and R2 capstones, the 2U tier's own
# capstones (`Interp2.Capstone*`, which `Main2` does not import and
# which are what drag `Step2/InferQ` and its closure into R, per the
# ruling that the 2U lane goes to R whole), and the R-facing
# refutations/ladders.
ROOTS_R = ['Setlec.SetR.Main', 'Setlec.SetR.Main2',
           'Setlec.SetR.Interp2.Capstone',
           'Setlec.SetR.Interp2.Capstone2C',
           'Setlec.SetR.Interp2.Capstone2D',
           'Setlec.SetR.Interp2.Capstone2E',
           'Setlec.SetR.Interp2.Step2.CtxOk2OpenD',
           'Setlec.SetR.Interp2.Step2.CtxOk2RRefute',
           'Setlec.SetR.Annot.PremiseLadder',
           'Setlec.SetR.Annot.SortCohFrame',
           'Setlec.SetR.Annot.Validity',
           'Setlec.SetR.Examples',
           'Setlec.SetR.Interp2.EnvLaws2',
           'Setlec.SetR.Interp2.EnvS2Refute',
           'Setlec.SetR.Interp2.LevelLocal',
           'Setlec.SetR.Interp2.Step2.LevelsInst',
           'Setlec.SetR.Interp2.Step2.StrLit',
           'Setlec.SetR.Interp2.IotaArity',
           'Setlec.SetR.Interp2.Step2.SeamMono',
           # 2U content (`EnvS2UM` rows) that S2 left without a
           # consumer: its only importer was `Step2/Lit`, which used
           # nothing from it (a dead import), and `Lit` is base now.
           'Setlec.SetR.Interp2.Step2.Infer']

cR = closure(ROOTS_R)

def lane(m):
    rel = mods[m]
    if m in CAPS:      return 'caps'
    if m in UMBRELLAS: return 'umbrella'
    if rel == 'Setlec/SetP.lean' or rel.startswith('Setlec/SetP/'): return 'P'
    if rel.startswith('Setlec/SetBase/'): return 'base'
    if rel.startswith('Setlec/SetR/'):
        return 'R' if m in cR else 'neutral'
    return 'base'

LANE = {m: lane(m) for m in mods}

cross = sorted((a, b) for a in mods for b in edges[a]
               if LANE[a] == 'P' and LANE[b] == 'R')
back  = sorted((a, b) for a in mods for b in edges[a]
               if LANE[a] == 'R' and LANE[b] == 'P')
basev = sorted((a, b) for a in mods for b in edges[a]
               if LANE[a] == 'base' and LANE[b] in ('P', 'R'))
implv = sorted((a, b) for a in mods for b in edges[a]
               if (mods[a].startswith(IMPL_DIRS) or a in IMPL_ROOTS)
               and b.startswith(THEORY_PFX))
unass = sorted((a, b) for a in mods for b in edges[a]
               if LANE[a] == 'neutral' and LANE[b] in ('P', 'R'))

if '--list' in sys.argv[1:]:
    for a, b in cross:
        print(f'{a} -> {b}')
    sys.exit(0)

allowed = set()
for line in WHITELIST.splitlines():
    line = line.split('#')[0].strip()
    if not line:
        continue
    a, b = [s.strip() for s in line.split('->')]
    allowed.add((a, b))

fail = 0
def report(title, items, hint):
    global fail
    if items:
        fail = 1
        print(f'LAYERING FAIL — {title} ({len(items)}):')
        for a, b in items:
            print(f'    {a} -> {b}')
        print(f'    {hint}')

report('NEW cross-lane import P -> R', [e for e in cross if e not in allowed],
       'the separation forbids it; if a batch really needs it, the lead '
       'rules and the whitelist in tests/layering.sh gains a tagged line.')
report('cross-lane import R -> P', back,
       'zero since S1 (the Annot/Ok2 re-basing killed the last one).')
report('base module importing a lane', basev,
       'Setlec/{Kernel,Verify,SetTheory,TT,SetBase}/* stand BELOW both lanes.')
report('implementation importing theory', implv,
       'CLAUDE.md: Setlec/Kernel/*, Main.lean must never import '
       'Setlec/{SetTheory,SetR,SetBase,Verify}/*.')
report('unclassified module importing lane content', unass,
       'the importer is in no lane root\'s closure: add it to ROOTS_P or '
       'ROOTS_R in tests/layering.sh so its edges are gated.')

stale = sorted(allowed - set(cross))
if stale:
    fail = 1
    print(f'LAYERING FAIL — stale whitelist entries ({len(stale)}):')
    for a, b in stale:
        print(f'    {a} -> {b}')
    print('    the edge is gone: delete the line (the whitelist only shrinks).')

n = {l: sum(1 for m in LANE if LANE[m] == l) for l in ("base", "R", "P", "neutral", "caps")}
if not fail:
    print(f'layering: base {n["base"]} / R {n["R"]} / P {n["P"]} / neutral {n["neutral"]} modules; '
          f'{len(cross)} P->R edges, all whitelisted; 0 R->P')
sys.exit(fail)
PYEOF
