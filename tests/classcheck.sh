#!/usr/bin/env bash
# The class checker (CLASSCHECK, experimental route) on every e2e and arena
# stream, against tests/classcheck-expected.txt.  Not part of tests/arena.sh.
# Usage: tests/classcheck.sh [-j N]
set -u
cd "$(dirname "$0")/.."
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"
J=8
[ "${1:-}" = "-j" ] && J=$2
timeout 3600 lake build class-sweep >/dev/null || exit 3
[ -d _tmp/arena-tests ] || { mkdir -p _tmp/arena-tests; tar -xzf tests/arena/lean-arena-tests.tar.gz -C _tmp/arena-tests || exit 3; }
one() {
  exp=$1; suite=$2; rel=$3
  if [ "$suite" = e2e ]; then f=tests/e2e/$rel; else f=_tmp/arena-tests/$rel; fi
  src=$f
  case $f in *.gz) src=$(mktemp "$TMPDIR/cc.XXXXXX.ndjson"); gunzip -c "$f" > "$src";; esac
  timeout 300 .lake/build/bin/class-sweep "$src" >/dev/null 2>&1; c=$?
  case $f in *.gz) rm -f "$src";; esac
  [ "$c" = "$exp" ] || echo "MISMATCH $suite $rel: expected $exp, got $c"
}
export -f one
out=$(grep -v '^#' tests/classcheck-expected.txt | xargs -P "$J" -L1 bash -c 'one "$@"' _)
if [ -n "$out" ]; then echo "$out"; exit 1; fi
echo "classcheck: $(grep -vc '^#' tests/classcheck-expected.txt) streams as expected"
