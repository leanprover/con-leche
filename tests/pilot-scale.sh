#!/usr/bin/env bash
# Doubling-n growth comparison for the cached-clone pilot.
#
# The method is tests/scale.sh's: retired instructions (perf stat,
# median of 3), a per-shape n=1 startup baseline subtracted, and the
# growth exponent read as log2 of the adjusted ratio between successive
# doublings.  Here it is run for two `--core=` variants side by side, so
# the question answered is "does the cached-clone representation change
# the *asymptotics*", not just the constant.
#
# Usage: tests/pilot-scale.sh [--deep]
set -u
cd "$(dirname "$0")/.."

BIN=${BIN:-.lake/build/bin/con-leche}
GEN=tests/scale/gen.py
# Generated streams go to DISK, never tmpfs (task #180): honour TMPDIR if
# set, else the project's on-disk ./_tmp/tmp.
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT
VARIANTS=${VARIANTS:-production,cached-parsed}
DEEP=0
[ "${1:-}" = --deep ] && DEEP=1

# shape:base-n
SPECS="chain:100 spine:50 many:100 telescope:50 dag:200 delta:100
fanout:100 lets:100 lparams:100 thm:200"

measure_once() { # <core> <file>
  perf stat -e instructions:u -x, timeout 600 nice -n 10 \
    "$BIN" "--core=$1" "$2" 2>&1 >/dev/null |
    awk -F, '/instructions/{print $1}'
}
measure() { # <core> <file> -> median of 3
  local a b c
  a=$(measure_once "$1" "$2"); b=$(measure_once "$1" "$2"); c=$(measure_once "$1" "$2")
  printf '%s\n%s\n%s\n' "$a" "$b" "$c" | sort -n | sed -n 2p
}

MULTS="1 2 4 8"
[ "$DEEP" = 1 ] && MULTS="1 2 4 8 16 32"

printf '%-12s %-16s %10s' shape core base
for m in $MULTS; do printf ' %12s' "${m}x"; done
printf ' %10s\n' 'exp(last)'

for spec in $SPECS; do
  shape=${spec%%:*}; base=${spec##*:}
  python3 "$GEN" "$shape" 1 > "$TMP/$shape-1.ndjson"
  for m in $MULTS; do
    python3 "$GEN" "$shape" $((base*m)) > "$TMP/$shape-$m.ndjson"
  done
  for core in ${VARIANTS//,/ }; do
    b0=$(measure "$core" "$TMP/$shape-1.ndjson")
    printf '%-12s %-16s %10s' "$shape" "$core" "$b0"
    prev=""; expo="-"
    for m in $MULTS; do
      v=$(measure "$core" "$TMP/$shape-$m.ndjson")
      adj=$((v - b0))
      printf ' %12s' "$adj"
      if [ -n "$prev" ] && [ "$prev" -gt 0 ] && [ "$adj" -gt 0 ]; then
        expo=$(awk -v a="$adj" -v p="$prev" 'BEGIN{printf "%.2f", log(a/p)/log(2)}')
      fi
      prev=$adj
    done
    printf ' %10s\n' "$expo"
  done
done
