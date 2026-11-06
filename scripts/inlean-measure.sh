#!/usr/bin/env bash
# Task #451: instructions:u of `inlean-replay` for the kernels none (import
# only, the baseline), official and inlean, on Init, Std and Lean.  Wall time
# is not a measurement on this shared machine.  One run per cell, each under
# `timeout`.
#
#   scripts/inlean-measure.sh [MOD...]     (default: Init Std Lean)
#
# Build first: `lake build inlean-replay`.
set -u
cd "$(dirname "$0")/.."
BIN=.lake/build/bin/inlean-replay
[ -x "$BIN" ] || { echo "missing $BIN: lake build inlean-replay" >&2; exit 3; }
MODS=("$@"); [ ${#MODS[@]} -gt 0 ] || MODS=(Init Std Lean)
LIMIT=${INLEAN_TIMEOUT:-3400}
mkdir -p _tmp

printf '%-6s %18s %18s %18s %s\n' module none official inlean 'inlean verdict'
for m in "${MODS[@]}"; do
  row=()
  verdict=-
  for k in none official inlean; do
    out=_tmp/measure-$m-$k.log
    timeout "$LIMIT" perf stat -x, -e instructions:u -o "_tmp/measure-$m-$k.perf" \
      "$BIN" --kernel=$k --quiet "$m" > "$out" 2>&1
    rc=$?
    n=$(grep instructions "_tmp/measure-$m-$k.perf" | cut -d, -f1)
    row+=("${n:-n/a}")
    [ "$k" = inlean ] && verdict="exit $rc"
  done
  printf '%-6s %18s %18s %18s %s\n' "$m" "${row[0]}" "${row[1]}" "${row[2]}" "$verdict"
done
