#!/usr/bin/env bash
set -euo pipefail

if [ "${CONLECHE_AFL_ROLE:-}" = cc ]; then   # re-entry: Lake calling us as LEAN_CC
  for arg in "$@"; do
    if [ "$arg" = "-c" ]; then exec afl-clang-fast "$@"; fi
  done
  exec afl-clang-fast "$@" -L "$LEAN_SYSROOT/lib"
fi

cd "$(dirname "${BASH_SOURCE[0]}")/.."

LEAN_SYSROOT=$(lean --print-prefix)
export LEAN_SYSROOT
export LEAN_CC="$PWD/scripts/afl-build.sh"
export CONLECHE_AFL_ROLE=cc
export AFL_QUIET=1                            # no AFL banner per compile

find .lake/build/ir -name '*.o*' -delete 2>/dev/null || true
lake build con-leche "$@"

exe=.lake/build/bin/con-leche
if [ "$(nm "$exe" | grep -c __afl_area_ptr)" -gt 0 ]; then
  echo "afl-build: $exe is instrumented (afl-fuzz -i <seeds> -o <out> -- $exe @@)" >&2
else
  echo "afl-build: $exe carries NO AFL instrumentation" >&2
  exit 3
fi
