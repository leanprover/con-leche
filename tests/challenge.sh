#!/usr/bin/env bash
# tests/challenge.sh — THE CHALLENGE GATE (tasks #281, #627).
#
# `ConLeche/Challenge.lean` is the trusted half of the Comparator pair
# (`comparator.json`): the main theorems about the binary's runs with `sorry`
# for their proofs, the binary's functions they name as holes (`def … := sorry`
# at their exact types), and specification imports only (`tests/layering.sh`'s
# challenge fence).  `ConLeche/MainTheorem.lean` is the solution half.  The
# challenge is in no default target and nothing imports it, so `lake build` and
# `lake test` never look at it; this gate does:
#
#   1. the challenge module BUILDS, and its only diagnostics are the
#      "declaration uses `sorry`" warnings (lake replays a cached module's log,
#      so they show on a warm tree too);
#   2. THE SELF-COMPARE: con-leche itself checks the challenge against the
#      solution, `con-leche --olean --compare -- ConLeche.Challenge
#      ConLeche.MainTheorem` over the built tree's `.olean` files and the
#      toolchain's: both closures are checked in full, and every hole and every
#      stated theorem of the challenge must be justified by the solution's
#      constant of the same name and statement, everything the statement reads
#      being the same constant in both or itself a justified hole.  The set of
#      justified names must be exactly `comparator.json`'s `theorem_names` and
#      `definition_names`.  Cost (task #627): 1.9 T instructions:u, 6.8 GiB
#      peak RSS, ~15 s wall at 96 threads.
#   3. with `--modular`, the same through the scheduler (`--olean --schedule
#      --compare`, one `--module` process per module of both closures, the
#      compare worker at the challenge): 7.4 T instructions:u, 3,162 modules,
#      13 GiB of workers at the peak, ~25 s wall at 96 threads.  Not part of
#      the standard battery.
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

# (2) the self-compare.
if ! timeout 3600 lake build "$solution" con-leche > "$tmp/solution-build.log" 2>&1; then
  echo "challenge: lake build $solution con-leche FAILED"; tail -20 "$tmp/solution-build.log"; exit 1
fi
lib="$(timeout 120 lake env lean --print-libdir)" || { echo "challenge: no toolchain libdir"; exit 1; }
sp="$PWD/.lake/build/lib/lean:$lib"
bin=.lake/build/bin/con-leche

justified() {  # the names a compare run's output reports as justified
  sed -n 's/^con-leche: [a-z]* \(.*\) justified by the solution$/\1/p' "$1" | sort
}
check_names() {  # $1: run label, $2: output file
  justified "$2" > "$tmp/justified.txt"
  if ! diff -q "$tmp/names.txt" "$tmp/justified.txt" > /dev/null; then
    echo "challenge: $1: the justified names are not comparator.json's (< config, > run):"
    diff "$tmp/names.txt" "$tmp/justified.txt" | head -20; fail=1
  fi
}

out="$tmp/compare.out"
timeout 3600 "$bin" --olean --compare --search-path="$sp" -- "$challenge" "$solution" > "$out" 2>&1
e=$?
if [ "$e" != 0 ]; then
  echo "challenge: self-compare exit $e (expected 0):"; grep -v '^con-leche: stats' "$out" | tail -10
  fail=1
else
  check_names "self-compare" "$out"
fi

# (3) the modular self-compare, on request.
if [ "$modular" = on ] && [ "$fail" = 0 ]; then
  mout="$tmp/compare-modular.out"
  timeout 3600 "$bin" --olean --schedule --compare --search-path="$sp" -- "$challenge" "$solution" \
    > "$mout" 2>&1
  e=$?
  if [ "$e" != 0 ]; then
    echo "challenge: modular self-compare exit $e (expected 0):"; tail -10 "$mout"; fail=1
  else
    echo "challenge: modular self-compare: $(grep -o 'accepted [0-9]* modules' "$mout" | tail -1)"
  fi
fi

if [ "$fail" = 0 ]; then
  echo "challenge: OK — builds with sorry only; self-compare accepts, $(wc -l < "$tmp/names.txt") names justified: $(grep -o 'accepted [0-9]* declarations, [0-9]* axioms justified' "$out")"
fi
exit $fail
