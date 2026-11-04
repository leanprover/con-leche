#!/usr/bin/env bash
# Regenerate the committed .olean fixtures of tests/olean.sh from
# tests/olean/src/*.lean (the Up* modules: ported from Lake's and
# Comparator's test suites) with the toolchain's own `lean`.  Run from the
# repository root.
set -euo pipefail
LEAN="$(elan which lean 2>/dev/null || command -v lean)"
OUT=tests/olean/lib
rm -rf "$OUT"; mkdir -p "$OUT"
for m in Tiny TinyClassic TinyUse ClashA ClashB HidA HidAll HidUse WvA WvB WvM NlX NlY \
    NlB NlM NpAx RbH RbM UpComm UpCommSol UpCommAxSol UpCommMisSol UpDefHole UpDefHoleSol \
    UpDefHoleAxSol UpDefHoleKindSol UpDefHoleTy UpDefHoleTySol UpKindDef UpKindDefOpqSol \
    UpKindThm UpKindThmDefSol UpKindThmOpqSol UpHidDef UpHidDefSol UpNum/12.34/5 UpNumSol \
    UpBoom UpBoomOleanSol UpBoomOpqSol UpBoomCharSol UpGcd UpGcdSol UpProj UpProjSol \
    UpQuot UpQuotSol UpThmHole UpThmHoleSol UpMultiA UpMultiB UpSorry DgFlagA DgFlagB \
    DgLiftA DgLiftB DgInferA DgInferB DgColQ DgColH DgColM DgCapQ DgCapQ2 DgCapH DgCapM \
    HiLamA HiLamB HiInhD HiInhX HiInhL HiInhT HiInhM HiInhM2 TeqP1 TeqP2 TeqQ2 TeqH TeqM \
    TeqDM; do
  mkdir -p "$(dirname "$OUT/$m")"
  LEAN_PATH="$OUT" "$LEAN" -o "$OUT/$m.olean" "tests/olean/src/$m.lean"
done
# only the olean levels are fixtures
find "$OUT" \( -name '*.ir' -o -name '*.ir.sig' \) -delete
ls -la "$OUT"
