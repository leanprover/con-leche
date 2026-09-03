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
# --- the 2U/denote2 lane.  RULED (design review pt 1): it goes to R
# WHOLE, so every P-quarter dependence on it is a cross edge.  Each is
# one or two model-free lemmas (census §2.4: frame_open2,
# interp2C_trans, natLit_facts2, denote2_{app,const,fvar}); S2 moves
# those to the base and the edges die with the 2U move.
Setlec.SetR.Annot.BitClosed -> Setlec.SetR.Interp2.Denote2Closed        # S2: denote2 closedness
Setlec.SetR.Annot.BitExtend -> Setlec.SetR.Interp2.Denote2Extend        # S2: denote2 extension
Setlec.SetR.Annot.BitInst -> Setlec.SetR.Interp2.Denote2Closed          # S2: denote2 closedness
Setlec.SetR.Annot.BitInstall -> Setlec.SetR.Interp2.Install2            # S2: denote2 install
Setlec.SetR.Interp2.OkPTransport -> Setlec.SetR.Interp2.Denote2Closed   # S2: denote2 closedness
Setlec.SetR.Interp2.Claims2P -> Setlec.SetR.Interp2.Claims2E            # S2: the 2U claims carrier
Setlec.SetR.Interp2.InstallP -> Setlec.SetR.Interp2.Keys2Cond           # S2: denote2_{app,const,fvar}
Setlec.SetR.Interp2.BasisTypeOk -> Setlec.SetR.Interp2.BasisOk          # S2: the 2U basis-ok carrier
Setlec.SetR.Interp2.Step2.BitLevels -> Setlec.SetR.Interp2.Step2.Levels # S2: the 2U levels walk
Setlec.SetR.Interp2.Step2.DefEqP -> Setlec.SetR.Interp2.Step2.DefEqRun  # S2: census §2.4 — uses NOTHING from it
Setlec.SetR.Interp2.Step2.NatP -> Setlec.SetR.Interp2.Step2.Lit         # S2: natLit_facts2
Setlec.SetR.Interp2.Step2.IrrelP -> Setlec.SetR.Interp2.EmptyPin2       # S2: the 2U empty pin
Setlec.SetR.Annot.Bit -> Setlec.SetR.Annot.Canon                        # S2: Canon needs natLitT+charListT out of Annot/Pass (census edge 14 split); Canon is base-destined, not R content
# --- the de-basing proper: `EnvS2Core.base : EnvS` and the P carriers
# that reach the collapsed carrier through it (spec point 2).
Setlec.SetR.Annot.EnvS2Core -> Setlec.SetR.Annot.EnvS2U                 # S3-S5: the `base : EnvS` field itself
Setlec.SetR.Annot.EnvS2P -> Setlec.SetR.Interp2.EnvS2U                  # S3-S5: ditto, the P mirror's own base
Setlec.SetR.Interp2.CapstoneP -> Setlec.SetR.Interp2.EmptyPin2          # S7: EnvS.empty_pinned, the capstone's Empty key (census §1.5, the ONE hard residue)
# --- the v1 install round trip (census §1.3's 47 sites): the P side
# calls a v1 install lemma only to build the new `EnvS`.  The premises
# vanish with the de-basing, and with them the imports.
Setlec.SetR.Interp2.AxiomPinP -> Setlec.SetR.StdAxiomKey                # S3: propextKeyS_mem/choiceKeyS_mem at the axiom pin
Setlec.SetR.Interp2.BasisEmptyP -> Setlec.SetR.Install.BasisS           # S3: extendEmptyS
Setlec.SetR.Interp2.IndMemberP -> Setlec.SetR.Install.IndMembersS       # S3: indMemberS/memberKeyS base builders
Setlec.SetR.Interp2.IotaRulePlainP -> Setlec.SetR.Install.IotaRuleS     # S3: iotaRuleS base builder (+ IotaRuleR/IotaThmR records to base)
Setlec.SetR.Interp2.ProjInstallP -> Setlec.SetR.Install.DeclIndS        # S3: projInstallS/templatesS base builders
Setlec.SetR.Interp2.HarvestP -> Setlec.SetR.Install.ValueKinds          # S4: declDefnS/declThmS/declOpaqueS base builders (+ annotate_syntax to base)
# --- the bridge: the records are SHARED, the derivations are R's.
Setlec.SetR.Interp2.FoldP -> Setlec.SetR.Bridge.Sound                   # S4: checkDeclRun_sound + declEtaStep (census C3/C4)
Setlec.SetR.Interp2.NatEqsP -> Setlec.SetR.Bridge.Decl                  # S4: natEqFrame_of_frag + the DeclR record family to the shared base
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
# lane classification.  Path first (the campaign's target state:
# `Setlec/SetBase/*` is base, `Setlec/SetP/*` is P, and when the last P
# module has moved there the closure rule below is dead weight).  For
# the modules still sitting under `Setlec/SetR/` while S2-S5 move them,
# the lane is computed from the LANE ROOTS:
#
#   P  =  closure(P roots)  minus  closure(R roots)
#   R  =  closure(R roots),  everything under Setlec/SetR/
#
# — a module that BOTH lanes need counts as R (the task-#161 ruling
# "everything EnvS-containing lives in R", read conservatively: a shared
# module stays R until it is re-based to `Setlec/SetBase/*` by name).
# A module under `Setlec/SetR/` in NEITHER closure is `neutral`: it is
# checked to import no lane content, and must otherwise be assigned to a
# root list below (the gate says so by name).
#
# Consequence to keep in mind when reading the whitelist: some
# whitelisted edges point at modules that are *base-destined*, not
# R-lane content (`Annot.Canon`); the batch tag says which.
IMPL_DIRS   = ('Setlec/Kernel/', 'Setlec/Cached/', 'Setlec/Frontend/')
IMPL_ROOTS  = ('Main', 'AnnotateBasis')
THEORY_PFX  = ('Setlec.Verify.', 'Setlec.SetTheory.', 'Setlec.SetR.',
               'Setlec.SetBase.', 'Setlec.TT.')
CAPS        = {'Setlec.Verify.Cached.MainC', 'Setlec.Verify.Cached'}
UMBRELLAS   = {'Setlec.SetR', 'Setlec'}

# The graded lane's roots: the P capstone, plus the parked/probe tops
# that no capstone imports (they are the P mode's own future — the io
# arms above all, so they must be gated).
ROOTS_P = ['Setlec.SetR.Interp2.FoldP',
           'Setlec.SetR.Interp2.Claims2PIO',
           'Setlec.SetR.Interp2.IndPinProbeP',
           'Setlec.SetR.Interp2.Step2.InferIOP']
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
           'Setlec.SetR.Interp2.Step2.SeamMono']

cP = closure(ROOTS_P)
cR = closure(ROOTS_R)

def lane(m):
    rel = mods[m]
    if m in CAPS:      return 'caps'
    if m in UMBRELLAS: return 'umbrella'
    if rel.startswith('Setlec/SetP/'):    return 'P'
    if rel.startswith('Setlec/SetBase/'): return 'base'
    if rel.startswith('Setlec/SetR/'):
        if m in cR: return 'R'
        if m in cP: return 'P'
        return 'neutral'
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
