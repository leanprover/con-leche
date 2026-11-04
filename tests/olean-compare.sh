#!/usr/bin/env bash
# THE OLEAN COMPARE GATE: the records the olean reader makes of a closure
# are, record for record, the ones lean4export writes of it
# (`lake exe olean-compare`).  Init's closure, by the toolchain's own files
# and by the exporter the self-check builds at this toolchain.
#
# Usage: tests/olean-compare.sh [L4E]   (L4E: the lean4export checkout;
# default _tmp/selfcheck-gate/lean4export, built by scripts/selfcheck.sh).
set -u
cd "$(dirname "$0")/.."
L4E="${1:-_tmp/selfcheck-gate/lean4export}"
if [ ! -x "$L4E/.lake/build/bin/lean4export" ]; then
  echo "olean-compare gate: no lean4export at $L4E (scripts/selfcheck.sh builds it)"
  exit 3
fi
OUT="${TMPDIR:-$PWD/_tmp/tmp}/olean-compare"
mkdir -p "$OUT"
lake build olean-compare >/dev/null || exit 3
LIB="$(dirname "$(dirname "$(elan which lean 2>/dev/null || command -v lean)")")/lib/lean"
timeout 1200 lake env "$L4E/.lake/build/bin/lean4export" Init > "$OUT/init.ndjson" || {
  echo "olean-compare gate: the export failed"; exit 3; }
timeout 1200 .lake/build/bin/olean-compare "$OUT/init.ndjson" "$LIB" Init > "$OUT/result.txt" 2>&1
e=$?
tail -1 "$OUT/result.txt"
if [ $e != 0 ]; then head -40 "$OUT/result.txt"; echo "OLEAN-COMPARE FAIL"; fi
rm -f "$OUT/init.ndjson"
exit $e
