#!/usr/bin/env bash
# tests/nested-shadow.sh — the NESTED ROUTE'S SHADOW GATE (task #279).
#
# The native nested route (`ConLeche/Kernel/Inductives/Nested*.lean`) is
# NOT on the fold's dispatch: a nested block still installs through the
# modelled route, because the accept set may not widen ahead of the
# model tier's `declNested`.  What the route does is therefore observed
# rather than acted on: with `CON_LECHE_NESTED_SHADOW=1` the driver runs
# `checkNested` beside the install, on the very same pre-block
# environment, and prints one
#
#     con-leche: nested-shadow <block> <accept|reject …|decline …|error …>
#
# line per recognised nested block.  This script runs the nested
# fixtures and compares those lines with `tests/nested-shadow-expected.txt`.
#
# Some fixtures are run with `CON_LECHE_INMODEL=0` (the second column):
# the in-process modeller DECLINES them at parse time, so the fold is
# never entered and the shadow never runs; turning the modeller off
# lets the declaration reach the install loop, where the shadow does.
# Those rows are exactly the coverage the native route adds.
#
# `tests/e2e/tower_nested.ndjson` is IN the gate since task #279 K.20:
# the shadow harness runs the CACHED route (`checkNestedS`, at the
# driver's own index and memo state, whose returned state is discarded),
# so the fixture's depth-60 DAG tower no longer exhausts memory inside
# `checkMutualCore` the way the pure uncached core did.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"
BIN="${BIN:-.lake/build/bin/con-leche}"
EXPECTED="${EXPECTED:-tests/nested-shadow-expected.txt}"
[ -x "$BIN" ] || { echo "no checker at $BIN (lake build first)" >&2; exit 3; }

ok=0
total=0
fail=0

while read -r fixture inmodel want; do
  case "$fixture" in ''|\#*) continue ;; esac
  total=$((total+1))
  # only the block NAME and the verdict WORD are compared, so that a
  # message change does not move the gate
  verdicts=$(CON_LECHE_INMODEL="$inmodel" CON_LECHE_NESTED_SHADOW=1 \
        timeout 900 "$BIN" --jobs=1 "$fixture" 2>&1 \
        | sed -n 's/^con-leche: nested-shadow \([^ ]*\) \([a-z]*\).*/\1=\2/p' \
        | tr '\n' ',' )
  if [ "$verdicts" = "$want" ]; then
    ok=$((ok+1))
  else
    fail=$((fail+1))
    echo "nested-shadow MISMATCH $fixture (inmodel=$inmodel)"
    echo "  want: $want"
    echo "  got:  $verdicts"
  fi
done < "$EXPECTED"

echo "nested-shadow: $ok/$total as expected"
[ "$fail" -eq 0 ] || exit 1
