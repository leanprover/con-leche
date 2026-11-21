#!/usr/bin/env bash
# tests/challenge.sh — THE CHALLENGE GATE (tasks #281, #627, #628).
#
# `ConLeche/Challenge.lean` is the trusted half of the `lake comparator`
# pair (`comparator.json`): the main theorems about the binary's runs with `sorry`
# for their proofs, the binary's functions they name as holes (`def … := sorry`
# at their exact types), and specification imports only (`tests/layering.sh`'s
# challenge fence).  `ConLeche/MainTheorem.lean` is the solution half.  The
# challenge is in no default target and nothing imports it, so `lake build` and
# `lake test` never look at it; this gate does:
#
#   1. the challenge module BUILDS, and its only diagnostics are the
#      "declaration uses `sorry`" warnings (lake replays a cached module's log,
#      so they show on a warm tree too);
#   2. with `--modular`, the self-compare through the scheduler (`--olean
#      --schedule --compare`, one `--module` process per module of both
#      closures, the compare worker at the challenge), the justified names
#      exactly `comparator.json`'s: 7.4 T instructions:u, 3,162 modules,
#      13 GiB of workers at the peak, ~25 s wall at 96 threads.  Not part of
#      the standard battery (a release-gate candidate).
#
# The self-compare in one process, `.olean` and lean4export JSON, is the
# self-check, `scripts/selfcheck.sh`, which `tests/arena.sh` runs.
set -uo pipefail
cd "$(dirname "$0")/.."
modular=off
for a in "$@"; do
  case "$a" in
    --modular) modular=on;;
    *) echo "usage: tests/challenge.sh [--modular]"; exit 3;;
  esac
done
fail=0
tmp="_tmp/challenge-gate"; mkdir -p "$tmp"

read -r challenge solution <<< "$(python3 -c '
import json; c=json.load(open("comparator.json"))
print(c["challenge_module"], c["solution_module"])')" || { echo "challenge: cannot read comparator.json"; exit 1; }
python3 -c '
import json; c=json.load(open("comparator.json"))
print("\n".join(sorted(c.get("theorem_names",[])+c.get("definition_names",[]))))' > "$tmp/names.txt"

# (1) the challenge builds, with the sorry warnings and nothing else.
log="$tmp/build.log"
if ! timeout 1800 lake build "$challenge" > "$log" 2>&1; then
  echo "challenge: lake build $challenge FAILED"; tail -20 "$log"; exit 1
fi
bad="$(grep -E '^(warning|error):' "$log" | grep -v 'declaration uses `sorry`' || true)"
if [ -n "$bad" ]; then
  echo "challenge: diagnostics other than the expected sorry warnings:"; echo "$bad"; fail=1
fi

# (2) the modular self-compare, on request.
if [ "$modular" = on ] && [ "$fail" = 0 ]; then
  if ! timeout 3600 lake build "$solution" con-leche > "$tmp/solution-build.log" 2>&1; then
    echo "challenge: lake build $solution con-leche FAILED"; tail -20 "$tmp/solution-build.log"; exit 1
  fi
  lib="$(timeout 120 lake env lean --print-libdir)" || { echo "challenge: no toolchain libdir"; exit 1; }
  mout="$tmp/compare-modular.out"
  timeout 3600 .lake/build/bin/con-leche --olean --schedule --compare \
    --search-path="$PWD/.lake/build/lib/lean:$lib" -- "$challenge" "$solution" > "$mout" 2>&1
  e=$?
  sed -n 's/^con-leche: [a-z]* \(.*\) justified by the solution$/\1/p' "$mout" | sort > "$tmp/justified.txt"
  if [ "$e" != 0 ]; then
    echo "challenge: modular self-compare exit $e (expected 0):"; tail -10 "$mout"; fail=1
  elif ! diff -q "$tmp/names.txt" "$tmp/justified.txt" > /dev/null; then
    echo "challenge: modular self-compare: the justified names are not comparator.json's (< config, > run):"
    diff "$tmp/names.txt" "$tmp/justified.txt" | head -20; fail=1
  else
    echo "challenge: modular self-compare: $(grep -o 'accepted [0-9]* modules' "$mout" | tail -1)"
  fi
fi

if [ "$fail" = 0 ]; then
  echo "challenge: OK — builds with sorry warnings only"
fi
exit $fail
