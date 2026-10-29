#!/usr/bin/env bash
# Regenerate the committed .olean fixtures of tests/olean.sh from
# tests/olean/src/*.lean (the Up* modules: ported from Lake's and
# Comparator's test suites, task #384) with the toolchain's own `lean` (the reader
# reads only oleans of the checker's toolchain, so a toolchain bump
# regenerates them, like the pins).  Run from the repository root.
set -euo pipefail
LEAN="$(elan which lean 2>/dev/null || command -v lean)"
OUT=tests/olean/lib
rm -rf "$OUT"; mkdir -p "$OUT"
for m in Tiny TinyClassic TinyUse ClashA ClashB CmpBase CmpChal CmpSol CmpSolDef CmpSolStmt CmpSolMissing CmpSolSorry HidA HidAll HidUse ReA ReB ReC Priv PrivUse TwinA TwinB LdX LdB LdM NlX NlY NlB NlM PoA PoM PdA PdB PdM CmpOpq CmpOpqSol CmpOpqSolK CmpOpqSolTy \
    UpComm UpCommSol UpCommAxSol UpCommMisSol UpDefHole UpDefHoleSol UpDefHoleAxSol \
    UpDefHoleKindSol UpDefHoleTy UpDefHoleTySol UpKindDef UpKindDefOpqSol UpKindThm \
    UpKindThmDefSol UpKindThmOpqSol UpHidDef UpHidDefSol UpNum/12.34/5 UpNumSol UpBoom UpBoomOleanSol UpBoomOpqSol UpBoomCharSol \
    UpGcd UpGcdSol UpProj UpProjSol UpQuot UpQuotSol UpThmHole UpThmHoleSol UpMultiA UpMultiB \
    UpSorry; do
  mkdir -p "$(dirname "$OUT/$m")"
  LEAN_PATH="$OUT" "$LEAN" -o "$OUT/$m.olean" "tests/olean/src/$m.lean"
done
# only the olean levels are fixtures
find "$OUT" \( -name '*.ir' -o -name '*.ir.sig' \) -delete
ls -la "$OUT"
