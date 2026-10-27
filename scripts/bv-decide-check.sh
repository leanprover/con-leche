#!/usr/bin/env bash
# scripts/bv-decide-check.sh — regenerate the `bv_decide` stream and check
# the checker's verdicts on it (task #368).
#
#   LEAN4EXPORT_DIR=<lean4export built for the checker's toolchain> \
#     scripts/bv-decide-check.sh [con-leche binary]
#
# The natively checked `bv_decide` path accepts only streams from the
# checker's OWN toolchain (`lean-toolchain`): the pinned closure of
# `BVLogicalExpr.Unsat` is that toolchain's.  `lean4export` must be built
# for it (for v4.35.0: lean4export at `5a9a355`).  The stream is about
# 80 MB (Std's LRAT checker and its soundness proofs) and is written to
# `_tmp/bv-decide/`, not committed.
#
# Three runs, each against its expected exit code:
#   accept  — `bvAndOr`, proved by `bv_decide`: 0
#   leak    — `bvLeak`, the native axiom used directly: 2 (decline)
#   badcert — `bvAndOr` with one LRAT literal changed: 2 (the native
#             check fails, the axiom's use declines)
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
BIN="${1:-$ROOT/.lake/build/bin/con-leche}"
TOOLCHAIN="$(cat "$ROOT/lean-toolchain")"
EXPORT_DIR="${LEAN4EXPORT_DIR:?set LEAN4EXPORT_DIR to a lean4export built for $TOOLCHAIN}"
EXPORT_BIN="$EXPORT_DIR/.lake/build/bin/lean4export"
[ -x "$EXPORT_BIN" ] || { echo "no lean4export at $EXPORT_BIN" >&2; exit 2; }
[ -x "$BIN" ] || { echo "no checker binary at $BIN" >&2; exit 2; }
[ "$(cat "$EXPORT_DIR/lean-toolchain")" = "$TOOLCHAIN" ] || {
  echo "lean4export at $EXPORT_DIR is not built for $TOOLCHAIN" >&2; exit 2; }

WORK="$ROOT/_tmp/bv-decide"
mkdir -p "$WORK"
cp "$ROOT/scripts/bv-decide/BvDecideUnsat.lean" "$WORK/"
( cd "$WORK" && elan run "$TOOLCHAIN" lean -o BvDecideUnsat.olean BvDecideUnsat.lean )
EXPORT_LEAN_PATH="$(cd "$EXPORT_DIR" && lake env printenv LEAN_PATH)"
LEAN_PATH="$WORK:$EXPORT_LEAN_PATH" "$EXPORT_BIN" BvDecideUnsat -- bvAndOr > "$WORK/accept.ndjson"
LEAN_PATH="$WORK:$EXPORT_LEAN_PATH" "$EXPORT_BIN" BvDecideUnsat -- bvLeak > "$WORK/leak.ndjson"
# the certificate is the one long string literal of the stream
line="$(grep -n '"strVal":"' "$WORK/accept.ndjson" | awk -F: 'length($0) > 10000 { print $1; exit }')"
[ -n "$line" ] || { echo "no certificate literal in the stream" >&2; exit 3; }
sed -E "${line}s/(\"strVal\":\")([0-9]+) /\1\2 -1 /" "$WORK/accept.ndjson" > "$WORK/badcert.ndjson"
cmp -s "$WORK/accept.ndjson" "$WORK/badcert.ndjson" && { echo "certificate not corrupted" >&2; exit 3; }

fail=0
for run in accept:0 leak:2 badcert:2; do
  name="${run%%:*}"; want="${run##*:}"
  set +e
  timeout 1800 "$BIN" "$WORK/$name.ndjson" > "$WORK/$name.out" 2>&1
  got=$?
  set -e
  if [ "$got" = "$want" ]; then
    echo "bv-decide: $name exit $got as expected"
  else
    echo "bv-decide: $name exit $got, expected $want ($(tail -1 "$WORK/$name.out"))"
    fail=1
  fi
done
exit $fail
