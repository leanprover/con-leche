#!/usr/bin/env bash
# THE OLEAN COMPARE GATE: the records the olean reader makes of a closure
# are, record for record, the ones the exporter writes of it
# (`lake exe olean-compare`).  Init's closure, by the toolchain's own files
# and by the toolchain's own exporter, `leanexport` (lean4export's command
# line; see `scripts/selfcheck.sh`).
#
# Usage: tests/olean-compare.sh
set -u
cd "$(dirname "$0")/.."
EXPORT_BIN="$(lean --print-prefix)/bin/leanexport"
if [ ! -x "$EXPORT_BIN" ]; then
  echo "olean-compare gate: the toolchain ships no leanexport ($EXPORT_BIN)"
  exit 3
fi
OUT="${TMPDIR:-$PWD/_tmp/tmp}/olean-compare"
mkdir -p "$OUT"
lake build olean-compare >/dev/null || exit 3
LIB="$(dirname "$(dirname "$(elan which lean 2>/dev/null || command -v lean)")")/lib/lean"
timeout 1200 lake env "$EXPORT_BIN" Init > "$OUT/init.ndjson" || {
  echo "olean-compare gate: the export failed"; exit 3; }
timeout 1200 .lake/build/bin/olean-compare "$OUT/init.ndjson" "$LIB" Init > "$OUT/result.txt" 2>&1
e=$?
tail -1 "$OUT/result.txt"
if [ $e != 0 ]; then head -40 "$OUT/result.txt"; echo "OLEAN-COMPARE FAIL"; fi
# one constant's cone, as the exporter's -- gives it: exactly the same records
if [ $e = 0 ]; then
  timeout 600 lake env "$EXPORT_BIN" Init -- Nat.add_comm > "$OUT/init.ndjson" || {
    echo "olean-compare gate: the export of one constant failed"; exit 3; }
  timeout 600 .lake/build/bin/olean-compare --constant=Nat.add_comm "$OUT/init.ndjson" "$LIB" Init \
    > "$OUT/result.txt" 2>&1
  e=$?
  tail -1 "$OUT/result.txt"
  if [ $e != 0 ]; then head -40 "$OUT/result.txt"; echo "OLEAN-COMPARE FAIL (--constant)"; fi
fi
rm -f "$OUT/init.ndjson"
exit $e
