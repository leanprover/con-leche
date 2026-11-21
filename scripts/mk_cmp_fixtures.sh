#!/usr/bin/env bash
# scripts/mk_cmp_fixtures.sh — the `--compare` fixtures of the e2e gate (task #612).
#
# Compiles every tests/e2e/src/cmp_*.lean with the repository toolchain's `lean` and exports the
# names its `--#export` line lists with the toolchain's `leanexport` into tests/e2e/cmp_*.ndjson.
# A challenge and its solutions list the same names (a missing-constant solution lists its own),
# as leanprover/comparator exports both modules at the same targets.
set -euo pipefail
cd "$(dirname "$0")/.."
PREFIX=$(lean --print-prefix)
L4E=$PREFIX/bin/leanexport
[ -x "$L4E" ] || { echo "no leanexport in $PREFIX/bin"; exit 3; }
OUT=_tmp/cmp-fixtures
mkdir -p "$OUT"
for src in tests/e2e/src/cmp_*.lean; do
  m=$(basename "$src" .lean)
  roots=$(sed -n 's/^--#export //p' "$src")
  timeout 300 lean -o "$OUT/$m.olean" "$src"
  LEAN_PATH="$OUT:$PREFIX/lib/lean" timeout 300 "$L4E" "$m" -- $roots > "tests/e2e/$m.ndjson"
  echo "$m: $(wc -l < "tests/e2e/$m.ndjson") lines"
done
