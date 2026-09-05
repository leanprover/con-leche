#!/usr/bin/env bash
# tests/proofdeps.sh — THE SEPARATION's PROOF-TERM gate (task #161, S10).
#
# WHY THIS EXISTS.  `tests/layering.sh` is an *import* gate: it measures
# where code SITS.  S9's payoff check found that this is not the
# campaign's criterion.  The layering gate read
#
#     base 260 / R 106 / P 117 / neutral 3 modules; 0 P->R edges
#
# — true, and simultaneously silent about `Red.beta` being live on the
# shipped P capstone's proof path, because S7/S8 moved the modules that
# DEFINE `Red`/`Infer`/`DefEq` into the shared base, where a
# directory-classifying gate counts them as `base`.  Nothing was hidden;
# the ratchet was measuring a different quantity.  The rule, recorded as
# the campaign's seventh gate-blindness instance and the sharpest:
#
#     An import gate measures where code SITS; only the proof term
#     measures what a theorem USES.  A separation criterion stated over
#     imports cannot certify a proof-path property.
#
# So this gate measures the proof term.  `tests/ProofDeps.lean` walks
# the transitive constant closure of a declaration's type AND proof
# term (with cut points) and prints one row per (root, target); the
# table below pins every row.
#
# THE RATCHET.  Divergence FAILS IN EITHER DIRECTION:
#   * a target that RE-ENTERS a closure is rot — the whole point of the
#     gate;
#   * a target that LEAVES a closure is progress that must be RECORDED:
#     flip the row here, in the batch that earned it.  The pin may only
#     ever tighten (`layering.sh`'s shrink-only whitelist discipline, at
#     the proof-term criterion).
# A `MISSING-ROOT`/`MISSING-TARGET` row also fails: a renamed constant
# must not silently turn the walk vacuous.
#
# Usage: tests/proofdeps.sh [--list]   (--list prints the measured rows
# in table syntax, for updating the pin after a batch).
set -u
cd "$(dirname "$0")/.."

MEASURED=$(lake env lean tests/ProofDeps.lean 2>&1) || {
  echo "PROOFDEPS FAIL — the instrument did not run:"
  echo "$MEASURED"
  exit 1
}

# (through the environment, not the heredoc: the table below is full of
# backticked prose and the heredoc must therefore be quoted)
export SETLEC_PROOFDEPS_MEASURED="$MEASURED"

exec python3 - "$@" <<'PYEOF'
import os, sys

MEASURED = os.environ['SETLEC_PROOFDEPS_MEASURED']

# ------------------------------------------------------------------ the
# PIN.  One line per measured row: "<PRESENT|absent> <label> :: <name>".
#
# **TASK #161 S11b — THE TABLE IS EMPTY.**  Every row below reads
# `absent` except the vacuity sentinel (`Setlec.Expr`, one per root):
# not one of the eleven R targets is reachable from any of the ten
# roots, and four of those roots are the SHIPPED P CAPSTONES.  That is
# the campaign's criterion, mechanized: the graded consistency proof's
# proof term does not mention the collapsed model (`EnvS`), the
# declaration bridge (`checkDeclR_ofEnvRE`), its records (`DeclR`,
# `DeclIndR`), the ind bridge (`declIndRR`), or the derivation tier at
# either granularity — the relation TYPES `Red`/`Infer`/`DefEq` and the
# constructors `Red.beta`/`Infer.app`/`DefEq.trans` alike.
#
# Read it in three blocks.
#
# (A) THE SHIPPED P CAPSTONE FAMILY — the user's question, mechanized.
#     S1-S8 bought `EnvS`; S11a bought `checkDeclR_ofEnvRE` and
#     `DeclR`; S11b buys the rest — `declIndRR`, `DeclIndR` and the six
#     relation names — by giving the `ind` kind a run-only bridge
#     (`declIndRunRR`) and re-pointing the graded fold's `Ind` slot at
#     `DeclIndRunR`.
#
#     **TASK #172 — THE FAMILY IS TWO ROOTS, NOT FOUR.**  `SP_P`, `C_P`
#     and `S_P` were the interned drivers' P letters (`checkDeclsSP`,
#     `cachedOps`, `checkDeclsShared`); the interned representation and
#     every driver over it were deleted, so those three letters retired
#     WITH THEIR SUBJECTS and their 36 rows went with them.  `SPCD_P`
#     (`no_proof_of_Empty_SPCD_P` over `checkDeclsSPCachedD`) is the
#     letter over the driver the binary now runs, and it measures the
#     same way: every R target absent.  The pin only ever tightens, and
#     a row whose subject no longer exists is not a loosening.
#
#     **Block (B) is retired**: it pinned a CUT at
#     `declIndRR`, and a cut at a constant that is not in the closure
#     measures the uncut reading (S11a finding 1: an inert cut row is
#     rot-shaped).  The door is now pinned directly, as a target.
#
# (C) THE P TIER'S OWN MATHEMATICS.  The claims tower, the inductive
#     tier's step and the value kinds' harvest reach none of the eleven.
#     `declIndP`'s two `PRESENT` rows (`Infer`/`DefEq`, through its
#     `DeclIndR` premise's statement furniture — the S10 measurement)
#     are gone with the premise.
#
# (D)/(E) THE RUN ROUTE, AT ITS OWN ROOTS.  `checkDeclRun_of` (the five
#     non-`ind` kinds' dispatch, S11a), `declIndRunRR` (the `ind` run
#     bridge, S11b) and `checkDeclRun_ofEnvRE` (the theorem the graded
#     fold actually calls, all six kinds discharged) reach none of the
#     eleven.  This is the deliverable stated positively rather than as
#     an absence in someone else's closure.
PIN = """
# (A) the shipped P capstone family — EVERY R target absent
# (two roots since task #172: the shipped driver's letter, and the pure one)
PRESENT SPCD_P :: Setlec.Expr
absent  SPCD_P :: Setlec.SetR.Red
absent  SPCD_P :: Setlec.SetR.Red.beta
absent  SPCD_P :: Setlec.SetR.Infer
absent  SPCD_P :: Setlec.SetR.Infer.app
absent  SPCD_P :: Setlec.SetR.DefEq
absent  SPCD_P :: Setlec.SetR.DefEq.trans
absent  SPCD_P :: Setlec.SetR.EnvS
absent  SPCD_P :: Setlec.SetR.checkDeclR_ofEnvRE
absent  SPCD_P :: Setlec.SetR.DeclR
absent  SPCD_P :: Setlec.SetR.declIndRR
absent  SPCD_P :: Setlec.SetR.DeclIndR
PRESENT P :: Setlec.Expr
absent  P :: Setlec.SetR.Red
absent  P :: Setlec.SetR.Red.beta
absent  P :: Setlec.SetR.Infer
absent  P :: Setlec.SetR.Infer.app
absent  P :: Setlec.SetR.DefEq
absent  P :: Setlec.SetR.DefEq.trans
absent  P :: Setlec.SetR.EnvS
absent  P :: Setlec.SetR.checkDeclR_ofEnvRE
absent  P :: Setlec.SetR.DeclR
absent  P :: Setlec.SetR.declIndRR
absent  P :: Setlec.SetR.DeclIndR

# (C) the P tier's own mathematics
PRESENT claims :: Setlec.Expr
absent  claims :: Setlec.SetR.Red
absent  claims :: Setlec.SetR.Red.beta
absent  claims :: Setlec.SetR.Infer
absent  claims :: Setlec.SetR.Infer.app
absent  claims :: Setlec.SetR.DefEq
absent  claims :: Setlec.SetR.DefEq.trans
absent  claims :: Setlec.SetR.EnvS
absent  claims :: Setlec.SetR.checkDeclR_ofEnvRE
absent  claims :: Setlec.SetR.DeclR
absent  claims :: Setlec.SetR.declIndRR
absent  claims :: Setlec.SetR.DeclIndR
PRESENT declIndP :: Setlec.Expr
absent  declIndP :: Setlec.SetR.Red
absent  declIndP :: Setlec.SetR.Red.beta
absent  declIndP :: Setlec.SetR.Infer
absent  declIndP :: Setlec.SetR.Infer.app
absent  declIndP :: Setlec.SetR.DefEq
absent  declIndP :: Setlec.SetR.DefEq.trans
absent  declIndP :: Setlec.SetR.EnvS
absent  declIndP :: Setlec.SetR.checkDeclR_ofEnvRE
absent  declIndP :: Setlec.SetR.DeclR
absent  declIndP :: Setlec.SetR.declIndRR
absent  declIndP :: Setlec.SetR.DeclIndR
PRESENT harvestDefnP :: Setlec.Expr
absent  harvestDefnP :: Setlec.SetR.Red
absent  harvestDefnP :: Setlec.SetR.Red.beta
absent  harvestDefnP :: Setlec.SetR.Infer
absent  harvestDefnP :: Setlec.SetR.Infer.app
absent  harvestDefnP :: Setlec.SetR.DefEq
absent  harvestDefnP :: Setlec.SetR.DefEq.trans
absent  harvestDefnP :: Setlec.SetR.EnvS
absent  harvestDefnP :: Setlec.SetR.checkDeclR_ofEnvRE
absent  harvestDefnP :: Setlec.SetR.DeclR
absent  harvestDefnP :: Setlec.SetR.declIndRR
absent  harvestDefnP :: Setlec.SetR.DeclIndR

# (D) the run route, and (E) the ind run bridge + the whole run dispatch
PRESENT runroute :: Setlec.Expr
absent  runroute :: Setlec.SetR.Red
absent  runroute :: Setlec.SetR.Red.beta
absent  runroute :: Setlec.SetR.Infer
absent  runroute :: Setlec.SetR.Infer.app
absent  runroute :: Setlec.SetR.DefEq
absent  runroute :: Setlec.SetR.DefEq.trans
absent  runroute :: Setlec.SetR.EnvS
absent  runroute :: Setlec.SetR.checkDeclR_ofEnvRE
absent  runroute :: Setlec.SetR.DeclR
absent  runroute :: Setlec.SetR.declIndRR
absent  runroute :: Setlec.SetR.DeclIndR
PRESENT indrunroute :: Setlec.Expr
absent  indrunroute :: Setlec.SetR.Red
absent  indrunroute :: Setlec.SetR.Red.beta
absent  indrunroute :: Setlec.SetR.Infer
absent  indrunroute :: Setlec.SetR.Infer.app
absent  indrunroute :: Setlec.SetR.DefEq
absent  indrunroute :: Setlec.SetR.DefEq.trans
absent  indrunroute :: Setlec.SetR.EnvS
absent  indrunroute :: Setlec.SetR.checkDeclR_ofEnvRE
absent  indrunroute :: Setlec.SetR.DeclR
absent  indrunroute :: Setlec.SetR.declIndRR
absent  indrunroute :: Setlec.SetR.DeclIndR
PRESENT declrun :: Setlec.Expr
absent  declrun :: Setlec.SetR.Red
absent  declrun :: Setlec.SetR.Red.beta
absent  declrun :: Setlec.SetR.Infer
absent  declrun :: Setlec.SetR.Infer.app
absent  declrun :: Setlec.SetR.DefEq
absent  declrun :: Setlec.SetR.DefEq.trans
absent  declrun :: Setlec.SetR.EnvS
absent  declrun :: Setlec.SetR.checkDeclR_ofEnvRE
absent  declrun :: Setlec.SetR.DeclR
absent  declrun :: Setlec.SetR.declIndRR
absent  declrun :: Setlec.SetR.DeclIndR
"""

def parse(text):
    rows, order = {}, []
    for line in text.splitlines():
        line = line.split('#')[0].strip()
        if not line:
            continue
        state, rest = line.split(None, 1)
        rows[rest.strip()] = state.strip()
        order.append(rest.strip())
    return rows, order

if '--list' in sys.argv[1:]:
    print(MEASURED)
    sys.exit(0)

pin, order = parse(PIN)
got, gorder = parse(MEASURED)

fail = 0

missing = [k for k in gorder if got[k] in ('MISSING-ROOT', 'MISSING-TARGET')]
if missing:
    fail = 1
    print('PROOFDEPS FAIL — the walk could not find a name (%d):' % len(missing))
    for k in missing:
        print('    %s  %s' % (got[k], k))
    print('    a renamed constant makes this gate vacuous; fix the name in '
          'tests/ProofDeps.lean and re-pin.')

rot = [k for k in gorder if k in pin and pin[k] == 'absent' and got[k] == 'PRESENT']
if rot:
    fail = 1
    print('PROOFDEPS FAIL — R content RE-ENTERED a proof-term closure (%d):' % len(rot))
    for k in rot:
        print('    %s' % k)
    print('    the separation forbids it: this is exactly what the gate is for.')

won = [k for k in gorder if k in pin and pin[k] == 'PRESENT' and got[k] == 'absent']
if won:
    fail = 1
    print('PROOFDEPS FAIL — R content LEFT a proof-term closure (%d):' % len(won))
    for k in won:
        print('    %s' % k)
    print('    that is progress: flip the row to "absent" in tests/proofdeps.sh '
          '(the pin only tightens) and record it in the batch seal.')

unpinned = [k for k in gorder if k not in pin]
if unpinned:
    fail = 1
    print('PROOFDEPS FAIL — measured rows that are not pinned (%d):' % len(unpinned))
    for k in unpinned:
        print('    %s %s' % (got[k], k))
    print('    add them to the PIN table (tests/proofdeps.sh --list prints them).')

stale = [k for k in order if k not in got]
if stale:
    fail = 1
    print('PROOFDEPS FAIL — pinned rows that are no longer measured (%d):' % len(stale))
    for k in stale:
        print('    %s' % k)
    print('    delete the line in the batch that removed the measurement.')

if not fail:
    caps = ['SPCD_P', 'P']
    tgts = ['EnvS', 'checkDeclR_ofEnvRE', 'DeclR', 'DeclIndR', 'declIndRR']
    rel = ['Red', 'Red.beta', 'Infer', 'Infer.app', 'DefEq', 'DefEq.trans']
    recs = sum(1 for c in caps for t in tgts
               if got['%s :: Setlec.SetR.%s' % (c, t)] == 'absent')
    beta = sum(1 for c in caps for t in rel
               if got['%s :: Setlec.SetR.%s' % (c, t)] == 'absent')
    doors = sum(1 for c in caps for t in rel
                if got['%s :: Setlec.SetR.%s' % (c, t)] == 'PRESENT')
    print('proofdeps: %d rows as pinned; EnvS/checkDeclR_ofEnvRE/DeclR/'
          'DeclIndR/declIndRR absent %d/%d and the derivation tier '
          '(Red, Red.beta, Infer, Infer.app, DefEq, DefEq.trans) absent '
          '%d/%d across the 2 shipped P capstones (doors: %d)'
          % (len(gorder), recs, len(caps) * len(tgts), beta,
             len(caps) * len(rel), doors))
sys.exit(fail)
PYEOF
