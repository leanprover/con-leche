#!/usr/bin/env bash
# Regenerate the committed .olean fixtures of tests/olean.sh from
# tests/olean/src/*.lean with the toolchain's own `lean` (the reader
# reads only oleans of the checker's toolchain, so a toolchain bump
# regenerates them, like the pins).  Run from the repository root.
set -euo pipefail
LEAN="$(elan which lean 2>/dev/null || command -v lean)"
OUT=tests/olean/lib
rm -rf "$OUT"; mkdir -p "$OUT"
for m in Tiny TinyClassic TinyUse ClashA ClashB CmpBase CmpChal CmpSol CmpSolDef CmpSolStmt CmpSolMissing CmpSolSorry HidA HidAll HidUse ReA ReB ReC Priv PrivUse TwinA TwinB LdX LdB LdM NlX NlY NlB NlM PoA PoM PdA PdB PdM; do
  LEAN_PATH="$OUT" "$LEAN" -o "$OUT/$m.olean" "tests/olean/src/$m.lean"
done
# only the olean levels are fixtures
rm -f "$OUT"/*.ir "$OUT"/*.ir.sig
ls -la "$OUT"
