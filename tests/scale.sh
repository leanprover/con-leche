#!/usr/bin/env bash
# Asymptotic scalability harness (task #56) — doubling-n growth tests.
#
# For each shape produced by tests/scale/gen.py the checker is run at
# n, 2n, 4n, 8n; work is measured in retired instructions
# (perf stat -e instructions:u; falls back to wall time if perf is
# unavailable, which is noisier).  A measured startup baseline (a
# 1-declaration stream: basis install etc.) is subtracted before
# fitting the growth exponent between successive doublings
# (log2 of the ratio).  PASS per shape iff the largest-step exponent
# is <= 1.3.
#
# Expected exponents for a scalable checker: ~1.0 for every shape
#   chain     n defs d_i := d_{i-1} + a use forcing n delta unfoldings
#   spine     one application spine of n arguments
#   many      n independent tiny defs (env insertion/lookup)
#   telescope one Pi/lambda telescope of depth n
# (chain/many may read slightly above 1.0 from log-factor container
# costs; anything >= 1.3 on the largest step is a real blowup.)
#
# NOT part of `lake test` — run manually or as an optional CI job:
#   tests/scale.sh            # default sizes, ~1 min total when healthy
#   BIN=path/to/setlec tests/scale.sh
# Exit code: 0 all shapes PASS, 1 otherwise.
set -u
cd "$(dirname "$0")/.."

BIN=${BIN:-.lake/build/bin/setlec}
GEN=tests/scale/gen.py
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

[ -x "$BIN" ] || { echo "checker binary $BIN not found" >&2; exit 1; }

# Measurement: prints one number (instructions, or ns wall time).
MODE=instructions
if ! perf stat -e instructions:u true >/dev/null 2>&1; then
  MODE=walltime
  echo "note: perf unavailable, falling back to wall time (noisy)" >&2
fi
measure() { # measure FILE -> count on stdout, empty on failure
  if [ "$MODE" = instructions ]; then
    perf stat -e instructions:u -x, "$BIN" "$1" 2>&1 >/dev/null \
      | awk -F, '/instructions/{print $1}'
  else
    local t0 t1
    t0=$(date +%s%N)
    "$BIN" "$1" >/dev/null 2>&1 || return 1
    t1=$(date +%s%N)
    echo $((t1 - t0))
  fi
}

# Startup baseline (basis install, IO): a single-declaration stream.
python3 "$GEN" many 1 > "$TMP/base.ndjson"
"$BIN" "$TMP/base.ndjson" >/dev/null || { echo "baseline stream not accepted" >&2; exit 1; }
BASE=$(measure "$TMP/base.ndjson")
echo "measuring $MODE; startup baseline: $BASE"

# shape base-n; largest run (8n) must stay well under ~60 s even at the
# currently observed (superlinear) growth.
fail=0
for spec in chain:100 spine:50 many:100 telescope:50; do
  shape=${spec%:*}; n0=${spec#*:}
  echo
  echo "== $shape (base n=$n0) =="
  prev=
  worst=
  for m in 1 2 4 8; do
    n=$((n0 * m))
    python3 "$GEN" "$shape" "$n" > "$TMP/s.ndjson"
    if ! timeout 120 "$BIN" "$TMP/s.ndjson" >/dev/null 2>&1; then
      echo "  n=$n: stream not accepted (exit $?) -- FAIL"; fail=1; prev=; continue
    fi
    cnt=$(measure "$TMP/s.ndjson")
    [ -n "$cnt" ] || { echo "  n=$n: measurement failed -- FAIL"; fail=1; prev=; continue; }
    adj=$((cnt - BASE)); [ "$adj" -gt 0 ] || adj=1
    if [ -n "$prev" ]; then
      exp=$(awk -v a="$prev" -v b="$adj" 'BEGIN{printf "%.2f", log(b/a)/log(2)}')
      echo "  n=$n: $cnt ($MODE), adjusted $adj, ratio exponent $exp"
      worst=$exp
    else
      echo "  n=$n: $cnt ($MODE), adjusted $adj"
    fi
    prev=$adj
  done
  if [ -z "$worst" ]; then
    echo "  $shape: no exponent computed -- FAIL"; fail=1
  elif awk -v e="$worst" 'BEGIN{exit !(e <= 1.3)}'; then
    echo "  $shape: largest-step exponent $worst <= 1.3 -- PASS"
  else
    echo "  $shape: largest-step exponent $worst > 1.3 -- FAIL"
    fail=1
  fi
done
echo
[ "$fail" = 0 ] && echo "scale: all shapes PASS" || echo "scale: FAIL"
exit "$fail"
