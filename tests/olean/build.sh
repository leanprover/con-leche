#!/usr/bin/env bash
# Regenerate the committed .olean fixtures of tests/olean.sh from
# tests/olean/src/*.lean (the Up* modules: ported from Lake's and
# Comparator's test suites) with the toolchain's own `lean`.  Run from the
# repository root.
set -euo pipefail
LEAN="$(elan which lean 2>/dev/null || command -v lean)"
OUT=tests/olean/lib
rm -rf "$OUT"; mkdir -p "$OUT"
for m in Tiny TinyClassic TinyUse PrivUnused LazyVal ClashA ClashB HidA HidAll HidUse WvA WvB WvM NlX NlY \
    NlB NlM NpAx RbH RbM UpComm UpCommSol UpCommAxSol UpCommMisSol UpDefHole UpDefHoleSol \
    UpDefHoleAxSol UpDefHoleKindSol UpDefHoleTy UpDefHoleTySol UpKindDef UpKindDefOpqSol \
    UpKindThm UpKindThmDefSol UpKindThmOpqSol UpHidDef UpHidDefSol UpNum/12.34/5 UpNumSol \
    UpBoom UpBoomOleanSol UpBoomOpqSol UpBoomCharSol UpGcd UpGcdSol UpProj UpProjSol \
    UpQuot UpQuotSol UpThmHole UpThmHoleSol UpMultiA UpMultiB UpSorry DgFlagA DgFlagB \
    DgLiftA DgLiftB DgInferA DgInferB DgColQ DgColH DgColM DgCapQ DgCapQ2 DgCapH DgCapM \
    HiLamA HiLamB HiInhD HiInhX HiInhL HiInhT HiInhM HiInhM2 TeqP1 TeqP2 TeqQ2 TeqH TeqM \
    TeqDM LvC LvB LvA LvM LvN ClashX ClashM FrX FrY FrM TeqBoth TeqX TeqBad MoX MoM GrN \
    PdA PdB PdM NsC NsH NsM NsN LdgQ LdgA LdgM LdvQ LdvA LdvM LdgN LdvN AxA AxB AxM AxNA AxNB \
    AxNX AxNM AxI AxIT AxIM UsA UsM RtA RtM PpA PpB PpM DnM1 DnM2 DnH GbG GbG2 QsP QsA QsB QsM UfH UfT \
    TdA TdB TdH TdM; do
  mkdir -p "$(dirname "$OUT/$m")"
  LEAN_PATH="$OUT" "$LEAN" -o "$OUT/$m.olean" "tests/olean/src/$m.lean"
done
# GbH is compiled against a stand-in GbG2 (its `w` without GbG2's S.rec, which GbG's would
# clash with); the gate then drops S.rec from GbG's exported part
mkdir -p "$OUT/stand"
LEAN_PATH="$OUT/stand" "$LEAN" -o "$OUT/stand/GbG2.olean" tests/olean/src/stand/GbG2.lean
LEAN_PATH="$OUT/stand:$OUT" "$LEAN" -o "$OUT/GbH.olean" tests/olean/src/GbH.lean
# UfM likewise, against a stand-in UfT (no S.rec, which GbG's would clash with)
LEAN_PATH="$OUT/stand" "$LEAN" -o "$OUT/stand/UfT.olean" tests/olean/src/stand/UfT.lean
LEAN_PATH="$OUT/stand:$OUT" "$LEAN" -o "$OUT/UfM.olean" tests/olean/src/UfM.lean
# PdN likewise, against a stand-in PdA (no pd: Lean's import refuses PdA's definition beside
# PdB's theorem)
LEAN_PATH="$OUT/stand" "$LEAN" -o "$OUT/stand/PdA.olean" tests/olean/src/stand/PdA.lean
LEAN_PATH="$OUT/stand:$OUT" "$LEAN" -o "$OUT/PdN.olean" tests/olean/src/PdN.lean
rm -r "$OUT/stand"
# only the olean levels are fixtures
find "$OUT" \( -name '*.ir' -o -name '*.ir.sig' \) -delete
ls -la "$OUT"
