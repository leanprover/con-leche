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
# Read it in four blocks.
#
# (A) THE SHIPPED P CAPSTONE FAMILY — the user's question, mechanized.
#     `EnvS` **absent** is what S1-S8 bought and is now enforced here
#     rather than only at the import gate.  `checkDeclR_ofEnvRE` and
#     `DeclR` **absent** is what S11a bought: the graded fold no longer
#     runs on the declaration bridge or on its record, but on the run
#     dispatch `checkDeclRun_of` and `DeclRunR`.  `Red`/`Infer`/`DefEq`
#     and the β rule are still PRESENT — they arrive through the `ind`
#     kind alone now (block B), and S11b's ind run bridge flips them.
#
# (B) THE ONE DOOR — S11a MOVED IT.  S9 found the door at
#     `checkDeclR_ofEnvRE` (the whole declaration bridge); with the five
#     non-`ind` kinds on run-only producers it is `declIndRR` (the
#     `ind` kind's bridge alone), and the old cut point is not in the
#     closure at all any more, so cutting it would measure nothing.
#     Cutting `declIndRR` removes `Red`, `Red.beta`, `Infer.app` and
#     `DefEq.trans` outright: there is no second route into the
#     *derivations*.  A new door shows up here as a PRESENT.  The type
#     names `Infer`/`DefEq` stay PRESENT under the cut because the P
#     lane's ind-tier SIGNATURES mention the R records (`DeclIndR`
#     carries `∀ φ, … Infer … ∧ DefEq …`); that is the ind-tier record
#     split's target, not the β gate's.
#
# (C) THE P TIER'S OWN MATHEMATICS.  The claims tower and the value
#     kinds' harvest reach NONE of the nine; the inductive tier's step
#     reaches only the two type names, through its `DeclIndR` premise —
#     which is exactly the S10 measurement: no P proof derives anything
#     in the R relation tier, the names arrive as statement furniture.
#
# (D) THE RUN ROUTE (S11a).  `checkDeclRun_of` — the five non-`ind`
#     kinds' producer — reaches none of the nine.  This is the batch's
#     deliverable stated positively rather than as an absence in someone
#     else's closure: the route derives nothing, and everything the
#     capstones still reach comes through the `Ind` parameter.
PIN = """
# (A) the shipped P capstone family
PRESENT SP_P :: Setlec.Expr
PRESENT SP_P :: Setlec.SetR.Red
PRESENT SP_P :: Setlec.SetR.Red.beta
PRESENT SP_P :: Setlec.SetR.Infer
PRESENT SP_P :: Setlec.SetR.Infer.app
PRESENT SP_P :: Setlec.SetR.DefEq
PRESENT SP_P :: Setlec.SetR.DefEq.trans
absent  SP_P :: Setlec.SetR.EnvS
absent  SP_P :: Setlec.SetR.checkDeclR_ofEnvRE
absent  SP_P :: Setlec.SetR.DeclR
PRESENT C_P :: Setlec.Expr
PRESENT C_P :: Setlec.SetR.Red
PRESENT C_P :: Setlec.SetR.Red.beta
PRESENT C_P :: Setlec.SetR.Infer
PRESENT C_P :: Setlec.SetR.Infer.app
PRESENT C_P :: Setlec.SetR.DefEq
PRESENT C_P :: Setlec.SetR.DefEq.trans
absent  C_P :: Setlec.SetR.EnvS
absent  C_P :: Setlec.SetR.checkDeclR_ofEnvRE
absent  C_P :: Setlec.SetR.DeclR
PRESENT S_P :: Setlec.Expr
PRESENT S_P :: Setlec.SetR.Red
PRESENT S_P :: Setlec.SetR.Red.beta
PRESENT S_P :: Setlec.SetR.Infer
PRESENT S_P :: Setlec.SetR.Infer.app
PRESENT S_P :: Setlec.SetR.DefEq
PRESENT S_P :: Setlec.SetR.DefEq.trans
absent  S_P :: Setlec.SetR.EnvS
absent  S_P :: Setlec.SetR.checkDeclR_ofEnvRE
absent  S_P :: Setlec.SetR.DeclR
PRESENT P :: Setlec.Expr
PRESENT P :: Setlec.SetR.Red
PRESENT P :: Setlec.SetR.Red.beta
PRESENT P :: Setlec.SetR.Infer
PRESENT P :: Setlec.SetR.Infer.app
PRESENT P :: Setlec.SetR.DefEq
PRESENT P :: Setlec.SetR.DefEq.trans
absent  P :: Setlec.SetR.EnvS
absent  P :: Setlec.SetR.checkDeclR_ofEnvRE
absent  P :: Setlec.SetR.DeclR

# (B) the one door — S11a moved it from `checkDeclR_ofEnvRE` to `declIndRR`
PRESENT SP_P-cut-ind :: Setlec.Expr
absent  SP_P-cut-ind :: Setlec.SetR.Red
absent  SP_P-cut-ind :: Setlec.SetR.Red.beta
PRESENT SP_P-cut-ind :: Setlec.SetR.Infer
absent  SP_P-cut-ind :: Setlec.SetR.Infer.app
PRESENT SP_P-cut-ind :: Setlec.SetR.DefEq
absent  SP_P-cut-ind :: Setlec.SetR.DefEq.trans
absent  SP_P-cut-ind :: Setlec.SetR.EnvS
absent  SP_P-cut-ind :: Setlec.SetR.checkDeclR_ofEnvRE
absent  SP_P-cut-ind :: Setlec.SetR.DeclR

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
PRESENT declIndP :: Setlec.Expr
absent  declIndP :: Setlec.SetR.Red
absent  declIndP :: Setlec.SetR.Red.beta
PRESENT declIndP :: Setlec.SetR.Infer
absent  declIndP :: Setlec.SetR.Infer.app
PRESENT declIndP :: Setlec.SetR.DefEq
absent  declIndP :: Setlec.SetR.DefEq.trans
absent  declIndP :: Setlec.SetR.EnvS
absent  declIndP :: Setlec.SetR.checkDeclR_ofEnvRE
absent  declIndP :: Setlec.SetR.DeclR
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

# (D) the run route itself (S11a)
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
    caps = ['SP_P', 'C_P', 'S_P', 'P']
    envs = sum(1 for c in caps if got['%s :: Setlec.SetR.EnvS' % c] == 'absent')
    recs = sum(1 for c in caps if got['%s :: Setlec.SetR.DeclR' % c] == 'absent')
    beta = sum(1 for c in caps if got['%s :: Setlec.SetR.Red.beta' % c] == 'PRESENT')
    doors = 0 if got['SP_P-cut-ind :: Setlec.SetR.Red.beta'] == 'absent' else 1
    print('proofdeps: %d rows as pinned; EnvS absent from %d/%d and DeclR from '
          '%d/%d P capstones; Red.beta present in %d/%d '
          '(doors beyond declIndRR: %d)'
          % (len(gorder), envs, len(caps), recs, len(caps), beta, len(caps),
             doors))
sys.exit(fail)
PYEOF
