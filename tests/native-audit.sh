#!/usr/bin/env bash
# tests/native-audit.sh — THE NATIVE-PREDICATE AUDIT (task #193):
# predicate ⊆ recogniser, mechanically, block by block.
#
# WHY.  `lech-preprocess` leaves a block unmodelled ("native") when its
# predicate `lechNative` (LechPreprocess.lean) says the checker installs
# it directly; the checker installs it directly when a RECOGNISER
# (`directPartsF?` / `directSumPartsF?`, Lech/Kernel/Direct/*) takes it.
# The standing rule is that the predicate must be no LOOSER than the
# recogniser: a block the predicate leaves native and the recogniser
# then rejects reaches the checker with neither a model nor a direct
# install — a "missing model" DECLINE where the stream used to accept.
# Task #193 found exactly that at Mathlib scale
# (`CategoryTheory.Presieve.ofArrows`, a former declared at a definition
# that only unfolds to a telescope: `numIndices` said "indexed family",
# the recogniser's `stripPis (nP + nIdx)` said "no").  The predicate is
# a hand-written mirror over a second `Expr` type, so it WILL drift
# again; this script is the gate that catches the drift on every stream
# it is given.
#
# HOW.  For each RAW stream: `lech-preprocess -o PRE STREAM` and the
# names on its "native — left to the consumer" lines are the
# predicate's verdicts; `LECH_ROUTE_TRACE=1 lech --pre PRE` prints one
# `lech: route <block> <struct|sum|modeled>` line per inductive block
# the fold reaches — the recogniser's verdict on the SAME environment
# the install sees (Main.lean, the progress lane).  Every native block
# must read `struct` or `sum`.
#
#   * native ∧ modeled  → FAIL (the regression class; the checker's own
#                          "missing model for X" decline is caught too)
#   * native ∧ unreached → the fold stopped before the block (a decline
#                          or reject earlier in the stream): NOTE, not a
#                          failure — the block was not audited
#   * modelled by the tool ∧ struct/sum → costs bytes, costs no verdict;
#                          counted, never a failure
#
# Streams: the `good/` arena fixtures of tests/arena-expected.txt (raw
# exports, fast) by default; `--full` adds `_tmp/init-exports/
# init-full.ndjson`; further arguments are more raw streams (a Mathlib
# cone slice cut from the raw export, say).  A stream the preprocessor
# itself refuses (nonzero exit, no output) is skipped with a NOTE.
#
# Usage: tests/native-audit.sh [--full] [STREAM.ndjson ...]
set -u
cd "$(dirname "$0")/.."

BIN=.lake/build/bin/lech
PRE=.lake/build/bin/lech-preprocess
[ -x "$BIN" ] || { echo "native audit: $BIN not built"; exit 1; }
[ -x "$PRE" ] || { echo "native audit: $PRE not built"; exit 1; }

full=0
streams=()
for a in "$@"; do
  case "$a" in
    --full) full=1;;
    *) streams+=("$a");;
  esac
done
if [ ${#streams[@]} = 0 ] || [ "$full" = 1 ]; then
  while read -r exp rel; do
    case "$exp" in ''|'#'*) continue;; esac
    case "$rel" in good/*) [ -f "_tmp/arena-tests/$rel" ] && streams+=("_tmp/arena-tests/$rel");; esac
  done < tests/arena-expected.txt
fi
if [ "$full" = 1 ] && [ -f _tmp/init-exports/init-full.ndjson ]; then
  streams+=(_tmp/init-exports/init-full.ndjson)
fi

WORK=$(mktemp -d _tmp/native-audit.XXXXXX)
trap 'rm -rf "$WORK"' EXIT

fail=0; nstreams=0; nnative=0; nstruct=0; nsum=0; nbasis=0; nmodeled=0; nunreached=0; nskipped=0
for s in "${streams[@]}"; do
  rm -f "$WORK/pre.ndjson"
  "$PRE" -o "$WORK/pre.ndjson" "$s" > "$WORK/pre.log" 2>&1
  pexit=$?
  if [ "$pexit" != 0 ] || [ ! -f "$WORK/pre.ndjson" ]; then
    echo "  NOTE $s: lech-preprocess exit $pexit, no output — not audited"
    nskipped=$((nskipped+1)); continue
  fi
  nstreams=$((nstreams+1))
  sed -n 's/: native — left to the consumer$//p' "$WORK/pre.log" | sort -u > "$WORK/native.txt"
  ( ulimit -v 16000000; LECH_ROUTE_TRACE=1 timeout 3000 "$BIN" --pre "$WORK/pre.ndjson" \
      > "$WORK/out.txt" 2> "$WORK/trace.txt" )
  cexit=$?
  if grep -q 'missing model for' "$WORK/trace.txt"; then
    echo "  FAIL $s: $(grep -m1 -o 'missing model for [^ ]*' "$WORK/trace.txt") — native, not recognised"
    fail=1
  fi
  sed -n 's/^lech: route //p' "$WORK/trace.txt" > "$WORK/routes.txt"
  while read -r name; do
    [ -n "$name" ] || continue
    nnative=$((nnative+1))
    route=$(awk -v n="$name" '$1 == n { print $2; exit }' "$WORK/routes.txt")
    case "$route" in
      struct) nstruct=$((nstruct+1));;
      sum) nsum=$((nsum+1));;
      basis) nbasis=$((nbasis+1));;   # a pinned basis block (`False`): the parse matches it before any recogniser
      modeled) nmodeled=$((nmodeled+1)); fail=1
              echo "  FAIL $s: $name is native (predicate) but the recogniser rejects it";;
      '') nunreached=$((nunreached+1))
          echo "  NOTE $s: native $name not reached (checker exit $cexit)";;
    esac
  done < "$WORK/native.txt"
done

echo "native audit: $nstreams streams ($nskipped skipped), $nnative native blocks — \
$nstruct struct, $nsum sum, $nbasis basis, $nmodeled unrecognised, $nunreached unreached"
[ "$fail" = 0 ] || { echo "NATIVE AUDIT FAIL — the predicate is looser than the recogniser"; exit 1; }
exit 0
