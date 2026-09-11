#!/usr/bin/env bash
# tests/challenge.sh — THE COMPARATOR PAIR GATE (task #281).
#
# `ConLeche/Challenge.lean` is the trusted half of the Comparator pair
# (`comparator.json`, DESIGN.md task #183): the advertised statement
# with `sorry` for its proof, importing the checker and the `SetTheory`
# interface and nothing from the proof tiers;
# `ConLeche/MainTheorem.lean` is the solution half.  The challenge is
# deliberately a TCB dead end — it roots its own `lean_lib`, that
# library is NOT in `defaultTargets`, and nothing in the tree imports
# it — which is exactly why it can rot unnoticed: `lake build`, `lake
# test` and every other gate leave it alone.  It did rot (task #257
# moved `checkDecls` to `ConLeche.Cached.Installed` while the module
# still imported `ConLeche.Cached.ParsedC`), and Comparator only
# compares statements it can build.  Hence this gate.
#
# Two checks, both cheap once the tree is built:
#   1. the challenge module BUILDS, and its only diagnostics are the
#      "declaration uses `sorry`" warnings of its stated theorems
#      (lake REPLAYS a cached module's log, so the warning shows up on
#      a warm tree too);
#   2. every name in `comparator.json`'s `theorem_names` (and
#      `definition_names`, empty today) has a statement that is
#      TOKEN-IDENTICAL between the two modules: `#check @name` under
#      `pp.universes`/`pp.explicit`/`pp.proofs` from a probe file per
#      module, the two outputs diffed — the method the task #183 record
#      describes, and what Comparator itself compares.
#
# What it does NOT check: that the challenge's imports stay out of
# `Verify/*`/`Model/*`.  That is `tests/layering.sh`'s base-purity
# clause, which classifies `ConLeche/Challenge.lean` as base.
set -uo pipefail
cd "$(dirname "$0")/.."
fail=0
tmp="_tmp/challenge-gate"; mkdir -p "$tmp"

cfg=comparator.json
read -r challenge solution <<< "$(python3 -c '
import json; c=json.load(open("comparator.json"))
print(c["challenge_module"], c["solution_module"])')" || { echo "challenge: cannot read $cfg"; exit 1; }
names="$(python3 -c '
import json; c=json.load(open("comparator.json"))
print(" ".join(c.get("theorem_names",[])+c.get("definition_names",[])))')"

# (1) the challenge builds, with the sorry warnings and nothing else.
log="$tmp/build.log"
if ! timeout 1800 lake build "$challenge" > "$log" 2>&1; then
  echo "challenge: lake build $challenge FAILED"; tail -20 "$log"; fail=1
else
  bad="$(grep -E '^(warning|error):' "$log" | grep -v 'declaration uses `sorry`' || true)"
  if [ -n "$bad" ]; then
    echo "challenge: diagnostics other than the expected sorry warnings:"; echo "$bad"; fail=1
  fi
fi

# (2) statement identity, challenge vs. solution.
if [ "$fail" = 0 ]; then
  if ! timeout 1800 lake build "$solution" > "$tmp/solution-build.log" 2>&1; then
    echo "challenge: lake build $solution FAILED"; tail -20 "$tmp/solution-build.log"; fail=1
  fi
fi
if [ "$fail" = 0 ] && [ -n "$names" ]; then
  for side in challenge solution; do
    mod="$challenge"; [ "$side" = solution ] && mod="$solution"
    {
      echo "import $mod"
      echo "set_option pp.universes true"
      echo "set_option pp.explicit true"
      echo "set_option pp.proofs true"
      echo "set_option pp.maxSteps 1000000"
      for n in $names; do echo "#check @$n"; done
    } > "$tmp/$side.lean"
    if ! timeout 600 lake env lean "$tmp/$side.lean" > "$tmp/$side.out" 2>&1; then
      echo "challenge: #check from $mod FAILED"; tail -5 "$tmp/$side.out"; fail=1
    fi
  done
fi
if [ "$fail" = 0 ]; then
  if [ -z "$names" ]; then
    echo "challenge: OK — builds with sorry only; comparator.json names no theorem"
  elif diff -q "$tmp/challenge.out" "$tmp/solution.out" > /dev/null; then
    echo "challenge: OK — builds with sorry only; statements identical for: $names"
  else
    echo "challenge: STATEMENTS DIFFER between $challenge and $solution:"
    diff "$tmp/challenge.out" "$tmp/solution.out" | head -40; fail=1
  fi
fi
exit $fail
