#!/usr/bin/env bash
# tests/route-census.sh — THE INSTALL-ROUTE CENSUS (task #207, the
# successor of the native-predicate audit of task #193).
#
# WHY THE AUDIT IS GONE.  Until task #207 the checker ran an external
# preprocessor (`lean-inductive-models`, wrapped as
# `con-leche-preprocess`) whose predicate `conlecheNative` mirrored the
# checker's own recognisers conjunct for conjunct, and the audit gated
# the mirror: a block the predicate left native and the recogniser then
# rejected reached the fold with neither a model nor a direct install.
# There is no second predicate any more — the tool, its mirror and the
# drift risk went together — so the *audited property has ceased to
# exist*.  This is a DIFFERENT gate with a different failure meaning:
# it does not compare two implementations, it pins what the ONE
# implementation does.
#
# WHAT IT PINS.  For each raw stream, `CON_LECHE_ROUTE_TRACE=1` prints
# one `con-leche: route <block> <struct|sum|fix|inmodel|modeled|basis>`
# line per inductive block the fold reaches — the recogniser's verdict
# on the same environment the install sees (Main.lean, the progress
# lane).  Every block must read a route the checker owns:
#
#   * struct / sum / fix   the direct routes
#   * inmodel              a `_model` family generated in-process
#                          (task #200) — the checker's own too
#   * basis                a pinned basis block, matched by the parse
#   * modeled           →  FAIL on a raw stream: the block's model came
#                          from the STREAM, and no exporter emits one
#                          since task #207 (a hand-written stream may;
#                          such a stream does not belong in this gate)
#   * "no install route"→  FAIL: the block reached the fold bare (the
#                          decline `ConLeche/Kernel/DeclCheck.lean`
#                          prints).  On a *good* fixture that is a
#                          coverage regression
#
# Streams: the ACCEPTING `good/` arena fixtures of
# tests/arena-expected.txt (the rows recorded `0`; raw exports, fast)
# by default — a fixture the checker declines has, by definition, a
# block on no route, and its verdict is recorded there with its reason
# rather than repeated here.  `--full` adds
# `_tmp/init-exports/init-full.ndjson`; further arguments are more raw
# streams (a Mathlib cone slice cut from the raw export, say).
#
# Usage: tests/route-census.sh [--full] [STREAM.ndjson ...]
set -u
cd "$(dirname "$0")/.."
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"

BIN=.lake/build/bin/con-leche
[ -x "$BIN" ] || { echo "route census: $BIN not built"; exit 1; }

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
    [ "$exp" = 0 ] || continue
    case "$rel" in good/*) [ -f "_tmp/arena-tests/$rel" ] && streams+=("_tmp/arena-tests/$rel");; esac
  done < tests/arena-expected.txt
fi
if [ "$full" = 1 ] && [ -f _tmp/init-exports/init-full.ndjson ]; then
  streams+=(_tmp/init-exports/init-full.ndjson)
fi

WORK=$(mktemp -d "$TMPDIR/route-census.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

fail=0; nstreams=0; nblocks=0
nstruct=0; nsum=0; nfix=0; ninmodel=0; nbasis=0; nmodeled=0
for s in "${streams[@]}"; do
  nstreams=$((nstreams+1))
  ( ulimit -v 16000000; CON_LECHE_ROUTE_TRACE=1 timeout 3000 "$BIN" "$s" \
      > "$WORK/out.txt" 2> "$WORK/trace.txt" )
  cexit=$?
  if grep -q 'no install route for' "$WORK/trace.txt"; then
    echo "  FAIL $s: $(grep -m1 -o 'no install route for inductive block [^:]*' "$WORK/trace.txt") — no route takes it"
    fail=1
  fi
  # a stream passed on the command line may legitimately reject or
  # decline (the default set is the accepting one); an ERROR never is.
  if [ "$cexit" = 3 ]; then
    echo "  FAIL $s: checker exit 3 (error)"; fail=1
  fi
  while read -r name route; do
    [ -n "$route" ] || continue
    nblocks=$((nblocks+1))
    case "$route" in
      struct) nstruct=$((nstruct+1));;
      sum) nsum=$((nsum+1));;
      fix) nfix=$((nfix+1));;
      inmodel) ninmodel=$((ninmodel+1));;
      basis) nbasis=$((nbasis+1));;
      modeled) nmodeled=$((nmodeled+1)); fail=1
              echo "  FAIL $s: $name routed 'modeled' — the model came from the stream";;
      *) echo "  FAIL $s: $name routed '$route' (unknown route)"; fail=1;;
    esac
  done < <(sed -n 's/^con-leche: route //p' "$WORK/trace.txt")
done

echo "route census: $nstreams streams, $nblocks blocks — \
$nstruct struct, $nsum sum, $nfix fix, $ninmodel inmodel, $nbasis basis, $nmodeled modeled"
[ "$fail" = 0 ] || { echo "ROUTE CENSUS FAIL — a block the checker does not install itself"; exit 1; }
exit 0
