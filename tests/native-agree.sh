#!/usr/bin/env bash
# tests/native-agree.sh — THE PREDICATE/RECOGNISER AGREEMENT GATE (task #178).
#
# `setlec-preprocess` (SetlecPreprocess.lean) is `lean-inductive-models` told
# which inductive blocks setlec installs *natively*: `setlecNative`, a mirror
# of the direct simple-structure recogniser `Setlec.directPartsCore?`
# (Setlec/Kernel/Direct/Parts.lean).  A block the predicate accepts leaves the
# preprocessor UNMODELLED, so the two sides must agree in one direction:
#
#   predicate accepts  ⟹  recogniser accepts
#
# A block accepted natively that the recogniser then rejects reaches the
# checker as a bare inductive it cannot install — a DECLINE where the stream
# used to be an accept.  That is the regression this gate stops.
#
# Two of the recogniser's conjuncts (`directShape` and the recursor rule's
# right-hand side) are argued rather than mirrored — they pin the shape Lean's
# kernel generates, and mirroring them would mean a second implementation of a
# syntactic pin over a second `Expr` type (see SetlecPreprocess.lean's header).
# This script is what gates them: it runs each stream through BOTH binaries and
# compares the checker's verdict on the two outputs.  A verdict that differs is
# a failure, whichever way it went; a `native`-line count is reported so the
# predicate's reach is visible.
#
# Usage: tests/native-agree.sh [streams-dir]   (default: _tmp/arena-tests)
#
# Requires `.lake/build/bin/setlec-preprocess` and the stock
# `lean-inductive-models` at the pinned revision, which `lake build` puts at
# .lake/packages/lean_inductive_models/.lake/build/bin/ (override with
# $SETLEC_STOCK_PREPROCESSOR).
set -u
cd "$(dirname "$0")/.."

BIN=.lake/build/bin/setlec
NEW=.lake/build/bin/setlec-preprocess
STOCK=${SETLEC_STOCK_PREPROCESSOR:-.lake/packages/lean_inductive_models/.lake/build/bin/lean-inductive-models}
DIR="${1:-_tmp/arena-tests}"

for f in "$BIN" "$NEW"; do
  [ -x "$f" ] || { echo "native-agree: SKIPPED — $f not built"; exit 0; }
done
[ -x "$STOCK" ] || { echo "native-agree: SKIPPED — stock preprocessor not built ($STOCK)"; exit 0; }
[ -d "$DIR" ] || { echo "native-agree: SKIPPED — no streams at $DIR"; exit 0; }

WORK=$(mktemp -d "${TMPDIR:-/tmp}/setlec-native-agree.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

fail=0; ok=0; total=0; natives=0; withnative=0; ppdiff=0; skipped=0

while IFS= read -r src; do
  # only streams the preprocessor has anything to do with
  grep -q '^{"inductive"' "$src" || continue
  total=$((total+1))
  rel=${src#"$DIR"/}

  # `-o` renames over the target only on a clean pass, so a failed run leaves
  # NO file — clear both, or a later stream would be compared against an
  # earlier stream's output.
  rm -f "$WORK/old.ndjson" "$WORK/new.ndjson"
  "$STOCK" --quiet -o "$WORK/old.ndjson" "$src" >/dev/null 2>"$WORK/old.err"; oldpp=$?
  # no `--quiet` on the new side: the `native` lines are pass diagnostics
  "$NEW" -o "$WORK/new.ndjson" "$src" >/dev/null 2>"$WORK/new.err"; newpp=$?
  if [ "$oldpp" != "$newpp" ]; then
    echo "NATIVE-AGREE NOTE $rel: preprocessor exit $oldpp -> $newpp"
    ppdiff=$((ppdiff+1))
  fi
  # a rejected or declined run wrote nothing; nothing to compare
  if [ ! -s "$WORK/new.ndjson" ] || [ ! -s "$WORK/old.ndjson" ]; then
    skipped=$((skipped+1)); continue
  fi

  n=$(grep -c ': native — left to the consumer$' "$WORK/new.err" 2>/dev/null || true)
  natives=$((natives + n))
  [ "${n:-0}" -gt 0 ] && withnative=$((withnative+1))

  timeout 120 "$BIN" --pre "$WORK/old.ndjson" >/dev/null 2>&1; oldv=$?
  timeout 120 "$BIN" --pre "$WORK/new.ndjson" >/dev/null 2>&1; newv=$?
  if [ "$oldv" != "$newv" ]; then
    if [ "$oldv" = 0 ] && [ "$newv" = 2 ]; then
      echo "NATIVE-AGREE FAIL $rel: REGRESSION — accept -> decline (a native block the recogniser rejects)"
    else
      echo "NATIVE-AGREE FAIL $rel: verdict $oldv -> $newv"
    fi
    fail=1
  else
    ok=$((ok+1))
  fi
done < <(find -L "$DIR" -name '*.ndjson' | sort)

echo "native-agree: $ok/$((total - skipped)) comparable streams agree ($skipped had no output on one side, $ppdiff differed in the preprocessor's own exit code); $natives native blocks over $withnative streams"
[ "$fail" = 0 ] || echo "native-agree: FAILURES"
exit $fail
