#!/usr/bin/env bash
# tests/proofdeps.sh — THE PROOF-TERM gate (task #161 S10; redefined at
# the SetR removal's Stage C, 2026-09-05).
#
# WHY THIS EXISTS.  `tests/layering.sh` is an *import* gate: it measures
# where code SITS.  S9's payoff check found that this is not a
# proof-path criterion.  The layering gate read
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
# WHAT IT MEASURED, AND WHY IT CHANGED.  Until 2026-09-05 it pinned
# eleven named R targets — `Red`, `Red.beta`, `Infer`, `Infer.app`,
# `DefEq`, `DefEq.trans`, `EnvS`, `checkDeclR_ofEnvRE`, `DeclR`,
# `declIndRR`, `DeclIndR` — each `absent` from every capstone's constant
# closure: the separation campaign's deliverable, mechanized, 88 rows.
# The SetR removal deleted the collapsed model, the R core, and finally
# the relation family and the derivation bridge above it.  **All eleven
# targets are gone**, so the old rows are not weakened — they have no
# subject.  A gate whose targets do not exist measures nothing.
#
# WHAT IT MEASURES NOW: a FROZEN MODULE-LEVEL DEPENDENCY PIN.  For each
# of the six pinned roots — the two MAIN THEOREMS (`Lech/
# MainTheorem.lean`, added 2026-09-07) and the four capstone letters
# and assembly lemmas they are corollaries of — `tests/ProofDeps.lean`
# prints the
# exact set of `Lech.*` modules its type and proof term reach at the
# constant level, sorted; `tests/proofdeps-expected.txt` is the frozen
# expectation and this gate is a diff.  Drift shows up as a named module
# appearing or disappearing.
#
# THE RATCHET, unchanged in shape: divergence FAILS IN EITHER
# DIRECTION.  A module that ENTERS a capstone's closure is a DOOR — the
# regression class the gate was built for, a capstone silently acquiring
# a dependency on machinery it should not need.  A module that LEAVES is
# progress that must be RECORDED: regenerate the expectation in the
# batch that earned it (`tests/proofdeps.sh --list > \
# tests/proofdeps-expected.txt`) and say so in the seal.  A
# `MISSING-ROOT` row also fails: a renamed capstone must not silently
# turn the walk vacuous, and a root whose closure came back empty prints
# no rows at all, which the diff reports as that root's whole row block
# missing (~370 lines).
#
# Usage: tests/proofdeps.sh [--list]   (--list prints the measured rows,
# for regenerating the expectation after a batch).
set -u
cd "$(dirname "$0")/.."

EXPECTED=tests/proofdeps-expected.txt

MEASURED=$(lake env lean tests/ProofDeps.lean 2>&1) || {
  echo "PROOFDEPS FAIL — the instrument did not run:"
  echo "$MEASURED"
  exit 1
}

if [ "${1-}" = --list ]; then
  printf '%s\n' "$MEASURED"
  exit 0
fi

if printf '%s\n' "$MEASURED" | grep -q '^MISSING-ROOT'; then
  echo 'PROOFDEPS FAIL — a capstone root does not exist:'
  printf '%s\n' "$MEASURED" | grep '^MISSING-ROOT'
  echo '    a renamed capstone must not silently turn the walk vacuous;'
  echo '    fix the name in tests/ProofDeps.lean in the batch that renamed it.'
  exit 1
fi

doors=$(comm -13 <(sort "$EXPECTED") <(printf '%s\n' "$MEASURED" | sort))
left=$(comm -23 <(sort "$EXPECTED") <(printf '%s\n' "$MEASURED" | sort))
rows=$(printf '%s\n' "$MEASURED" | grep -c ' :: ')
ndoors=$(printf '%s' "$doors" | grep -c ' :: ' || true)
nleft=$(printf '%s' "$left" | grep -c ' :: ' || true)

fail=0
if [ -n "$doors" ]; then
  fail=1
  echo "PROOFDEPS FAIL — modules ENTERED a capstone's proof-term closure ($ndoors):"
  printf '%s\n' "$doors" | sed 's/^/    /'
  echo '    a door: the capstone acquired a dependency it did not have.'
  echo '    Justify it or remove it; do not regenerate the pin to hide it.'
fi
if [ -n "$left" ]; then
  fail=1
  echo "PROOFDEPS FAIL — modules LEFT a capstone's proof-term closure ($nleft):"
  printf '%s\n' "$left" | sed 's/^/    /'
  echo '    that is progress: regenerate with'
  echo '      tests/proofdeps.sh --list > tests/proofdeps-expected.txt'
  echo '    in the batch that earned it, and record it in the seal.'
fi
[ "$fail" = 0 ] || exit 1

caps=$(cut -d' ' -f1 "$EXPECTED" | sort -u | tr '\n' ' ')
ncaps=$(cut -d' ' -f1 "$EXPECTED" | sort -u | wc -l)
echo "proofdeps: $rows module rows as pinned across $ncaps roots ($caps); doors: $ndoors"
