#!/usr/bin/env bash
# Asymptotic scalability harness (tasks #56, #98) — doubling-n growth tests.
#
# For each shape produced by tests/scale/gen.py the checker is run at
# n, 2n, 4n, 8n (standard mode) or up to 32n (deep mode); work is
# measured in retired instructions (perf stat -e instructions:u,
# median of 3 runs).  A per-shape startup baseline (the same shape at
# n=1: basis install, IO, and — for preprocessed shapes — the
# preprocessor's fixed cost) is subtracted before fitting the growth
# exponent between successive doublings (log2 of the adjusted ratio).
# PASS per shape iff the exponent at the LARGEST step is <= the
# per-shape gate (superlinear growth shows most clearly at the largest
# n — spine read 1.26 at n=400 but 1.58 at n=1600 before the fix, so
# regressions that standard mode reads as borderline are confirmed by
# deep mode).
#
# Gates are per shape, set at the measured master exponent plus slack
# (see the SPECS table below and DESIGN.md "Asymptotic scalability
# harness"), NOT a blanket threshold: shapes that measure flat gate
# tightly (<= 1.15), shapes with known superlinear behavior gate at
# measured+slack so they cannot get *worse* silently.
#
# Peak RSS is fitted the same way for the shapes whose retained state
# grows with n (chain/many/dag/thm): max of 3 runs of the process
# tree's ru_maxrss, per-shape n=1 baseline subtracted.  RSS is much
# noisier than instruction counts (allocator granularity, ~60 MB
# binary/runtime floor); on current master the adjusted retention at
# the largest standard sizes is well under 3 MB, i.e. inside allocator
# noise, so per-doubling RSS exponents are meaningless there.  The RSS
# gate therefore has a signal floor: a shape PASSes outright when the
# adjusted peak RSS at the largest n stays under RSS_FLOOR_KB (healthy
# retention); only above the floor — where a real retention blowup
# lands immediately — must the largest-step exponent meet the (still
# generous) per-shape RSS gate.
#
# Modes:
#   tests/scale.sh            standard: 4 points per shape, ~1 min
#                             measured (budget 2-3 min when loaded);
#                             the CI profile / merge gate.
#   tests/scale.sh --ci       alias for standard (documented CI entry
#                             point; identical behavior).
#   tests/scale.sh --deep     deep: up to 6 points per shape (n up to
#   (or SCALE_DEEP=1)         32x base), ~3-4 min measured (budget
#                             ~10 min); for performance work and
#                             nightly runs — quadratics that read
#                             borderline at standard sizes are
#                             unambiguous here, with their own
#                             deep-calibrated gates.
#
# Requirements and skip policy (flaky gates are worse than absent
# ones — there is deliberately NO wall-time fallback):
#   * perf with working counters (perf stat -e instructions:u).  When
#     unavailable (no perf in PATH, or kernel.perf_event_paranoid too
#     restrictive), the harness SKIPS everything: prominent notice,
#     exit 0.
#   * the preprocessor (found like the checker finds it:
#     $SETLEC_INDUCTIVE_MODELS, this build's setlec-preprocess, the
#     _tmp/ stock dev checkout, PATH).
#     When unavailable, only the preprocessed shapes (ctors-mod,
#     fields-mod) are SKIPPED with a notice; everything else runs.
#
# NOT part of `lake test` (needs a built binary, perf, and a process
# per stream) — run manually or as a CI job:
#   tests/scale.sh
#   BIN=path/to/setlec tests/scale.sh --deep
# Exit code: 0 all measured shapes PASS (or harness skipped), 1 a
# gate failed.
set -u
cd "$(dirname "$0")/.."

BIN=${BIN:-.lake/build/bin/setlec}
GEN=tests/scale/gen.py
# Generated streams go to DISK, never tmpfs (task #180): honour TMPDIR if
# set, else the project's on-disk ./_tmp/tmp — `mktemp -d` and the
# generator both read TMPDIR from here.
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

DEEP=0
for a in "$@"; do
  case "$a" in
    --deep) DEEP=1 ;;
    --ci) ;;                      # documented alias for standard mode
    *) echo "usage: tests/scale.sh [--deep|--ci]" >&2; exit 1 ;;
  esac
done
[ "${SCALE_DEEP:-0}" = 1 ] && DEEP=1

[ -x "$BIN" ] || { echo "checker binary $BIN not found" >&2; exit 1; }

# --- perf availability: skip everything without it (no wall-time
# fallback — a noisy gate that flakes is worse than no gate).
if ! perf stat -e instructions:u true >/dev/null 2>&1; then
  echo "scale: SKIPPED — perf unavailable (no perf binary, or"
  echo "scale: kernel.perf_event_paranoid too restrictive for user"
  echo "scale: counters).  No shapes were measured; this is NOT a pass"
  echo "scale: of the growth gates."
  exit 0
fi

# --- preprocessor availability (same search order as the checker,
# Main.lean findPreprocessor): decides whether the *-mod shapes run.
HAVE_PP=0
if [ -n "${SETLEC_INDUCTIVE_MODELS:-}" ]; then
  [ -x "$SETLEC_INDUCTIVE_MODELS" ] && HAVE_PP=1
elif [ -x .lake/build/bin/setlec-preprocess ] \
    || [ -x _tmp/lean-inductive-models/.lake/build/bin/lean-inductive-models ] \
    || command -v setlec-preprocess >/dev/null 2>&1; then
  HAVE_PP=1
fi

TIMEOUT=120
[ "$DEEP" = 1 ] && TIMEOUT=600

# run_shape MODE FILE — run the checker on FILE; MODE `raw` disables
# the preprocessor (the raw-stream/direct-install path), `def`/`mod`
# run the checker as-is.
run_shape() {
  if [ "$1" = raw ]; then
    SETLEC_INDUCTIVE_MODELS=/nonexistent timeout "$TIMEOUT" nice -n 10 "$BIN" "$2"
  else
    timeout "$TIMEOUT" nice -n 10 "$BIN" "$2"
  fi
}

measure_once() { # measure_once MODE FILE -> instruction count
  if [ "$1" = raw ]; then
    perf stat -e instructions:u -x, env SETLEC_INDUCTIVE_MODELS=/nonexistent \
      timeout "$TIMEOUT" nice -n 10 "$BIN" "$2" 2>&1 >/dev/null
  else
    perf stat -e instructions:u -x, \
      timeout "$TIMEOUT" nice -n 10 "$BIN" "$2" 2>&1 >/dev/null
  fi | awk -F, '/instructions/{print $1}'
}

measure() { # measure MODE FILE -> median of 3, empty on failure
  local a b c
  a=$(measure_once "$1" "$2"); b=$(measure_once "$1" "$2"); c=$(measure_once "$1" "$2")
  [ -n "$a" ] && [ -n "$b" ] && [ -n "$c" ] || return 1
  printf '%s\n%s\n%s\n' "$a" "$b" "$c" | sort -n | sed -n 2p
}

rss_once() { # rss_once MODE FILE -> peak RSS (KB) of the process tree
  local pre=()
  [ "$1" = raw ] && pre=(env SETLEC_INDUCTIVE_MODELS=/nonexistent)
  "${pre[@]}" python3 - "$BIN" "$2" "$TIMEOUT" <<'EOF'
import resource, subprocess, sys
r = subprocess.run(["timeout", sys.argv[3], "nice", "-n", "10",
                    sys.argv[1], sys.argv[2]],
                   stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
if r.returncode == 0:
    print(resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
EOF
}

rss_max3() { # rss_max3 MODE FILE -> max of 3 runs, empty on failure
  local a b c
  a=$(rss_once "$1" "$2"); b=$(rss_once "$1" "$2"); c=$(rss_once "$1" "$2")
  [ -n "$a" ] && [ -n "$b" ] && [ -n "$c" ] || return 1
  printf '%s\n%s\n%s\n' "$a" "$b" "$c" | sort -n | sed -n 3p
}

# --- shape table -----------------------------------------------------
# label : gen-shape : mode : base-n : deep-maxm : instr-gate :
#   deep-instr-gate : rss-gate
#
# mode      def = plain definition stream; raw = preprocessor disabled
#           (direct-install path); mod = preprocessor required.
# deep-maxm largest n multiplier in deep mode (standard is always 8);
#           bounded per shape so deep stays in budget even on the
#           known-superlinear shapes.
# instr-gate / deep-instr-gate  largest-step instruction exponent
#           gate for standard / deep mode: measured master value +
#           slack (see DESIGN.md for the measured table).  The
#           superlinear shapes read HIGHER exponents at deep sizes
#           (their curves still rise), hence per-mode calibration;
#           the flat shapes gate identically in both modes.
# rss-gate  largest-step peak-RSS exponent gate (only applied above
#           the RSS_FLOOR_KB signal floor), `-` = not measured.
#
# Gate provenance (measured on master 4f63b6c, 2026-08-24; full table
# in DESIGN.md): the flat shapes measured 1.00-1.02 and gate at 1.15.
# Four shapes measured SUPERLINEAR on master (known findings, gated at
# measured+slack so they cannot silently get worse): lparams 1.49/8x
# 1.78/32x, ctors-mod 2.58/8x 2.76/16x, fields-mod 2.08/8x 2.43/16x.
# fields-raw recalibrated after the direct-install instantiation fix
# (DESIGN.md "fields-raw: the near-cubic direct install"): measured
# 1.92/8x 2.22/32x, gated at 2.20/2.50.
SPECS="
chain:chain:def:100:32:1.15:1.15:1.60
spine:spine:def:50:32:1.15:1.15:-
many:many:def:100:32:1.15:1.15:1.60
telescope:telescope:def:50:32:1.15:1.15:-
dag:dag:def:200:32:1.15:1.15:1.60
delta:delta:def:100:32:1.15:1.15:-
fanout:fanout:def:100:32:1.15:1.15:-
lets:lets:def:100:32:1.15:1.15:-
lparams:lparams:def:100:32:1.65:1.95:-
thm:thm:def:200:32:1.15:1.15:1.60
fields-raw:fields:raw:25:32:2.20:2.50:-
ctors-mod:ctors:mod:4:16:2.90:3.00:-
fields-mod:fields:mod:8:16:2.40:2.70:-
"
RSS_FLOOR_KB=16384

MULTS="1 2 4 8"
[ "$DEEP" = 1 ] && MULTS="1 2 4 8 16 32"

fail=0
echo "scale: measuring instructions (median of 3)$([ "$DEEP" = 1 ] && echo ', deep mode')"
for spec in $SPECS; do
  label=${spec%%:*}; rest=${spec#*:}
  shape=${rest%%:*}; rest=${rest#*:}
  mode=${rest%%:*}; rest=${rest#*:}
  n0=${rest%%:*}; rest=${rest#*:}
  maxm=${rest%%:*}; rest=${rest#*:}
  gate=${rest%%:*}; rest=${rest#*:}
  dgate=${rest%%:*}
  rssgate=${rest#*:}
  [ "$DEEP" = 1 ] && gate=$dgate
  echo
  echo "== $label (base n=$n0, gate $gate) =="
  if [ "$mode" = mod ] && [ "$HAVE_PP" != 1 ]; then
    echo "  SKIPPED: lean-inductive-models preprocessor not available"
    continue
  fi
  # per-shape startup baseline: the same shape at n=1
  python3 "$GEN" "$shape" 1 > "$TMP/base.ndjson"
  run_shape "$mode" "$TMP/base.ndjson" >/dev/null 2>&1 \
    || { echo "  baseline (n=1) stream not accepted -- FAIL"; fail=1; continue; }
  BASE=$(measure "$mode" "$TMP/base.ndjson") \
    || { echo "  baseline measurement failed -- FAIL"; fail=1; continue; }
  RSSBASE=
  [ "$rssgate" != - ] && RSSBASE=$(rss_max3 "$mode" "$TMP/base.ndjson")
  prev=; rprev=
  worst=; rworst=; rlast=
  for m in $MULTS; do
    [ "$m" -le "$maxm" ] || continue
    n=$((n0 * m))
    python3 "$GEN" "$shape" "$n" > "$TMP/s.ndjson"
    if ! run_shape "$mode" "$TMP/s.ndjson" >/dev/null 2>&1; then
      echo "  n=$n: stream not accepted (exit $?) -- FAIL"; fail=1; prev=; continue
    fi
    cnt=$(measure "$mode" "$TMP/s.ndjson") \
      || { echo "  n=$n: measurement failed -- FAIL"; fail=1; prev=; continue; }
    adj=$((cnt - BASE)); [ "$adj" -gt 0 ] || adj=1
    line="  n=$n: $cnt instr, adjusted $adj"
    if [ -n "$prev" ]; then
      exp=$(awk -v a="$prev" -v b="$adj" 'BEGIN{printf "%.2f", log(b/a)/log(2)}')
      line="$line, exponent $exp"
      worst=$exp
    fi
    prev=$adj
    if [ "$rssgate" != - ] && [ -n "$RSSBASE" ]; then
      r=$(rss_max3 "$mode" "$TMP/s.ndjson")
      if [ -n "$r" ]; then
        radj=$((r - RSSBASE)); [ "$radj" -gt 0 ] || radj=1
        line="$line | rss ${r}KB, adjusted $radj"
        if [ -n "$rprev" ]; then
          rexp=$(awk -v a="$rprev" -v b="$radj" 'BEGIN{printf "%.2f", log(b/a)/log(2)}')
          line="$line, exponent $rexp"
          rworst=$rexp
        fi
        rprev=$radj; rlast=$radj
      fi
    fi
    echo "$line"
  done
  if [ -z "$worst" ]; then
    echo "  $label: no exponent computed -- FAIL"; fail=1
  elif awk -v e="$worst" -v g="$gate" 'BEGIN{exit !(e <= g)}'; then
    echo "  $label: largest-step exponent $worst <= $gate -- PASS"
  else
    echo "  $label: largest-step exponent $worst > $gate -- FAIL"
    fail=1
  fi
  if [ "$rssgate" != - ]; then
    if [ -z "$rlast" ]; then
      echo "  $label: no RSS measurement -- FAIL"; fail=1
    elif [ "$rlast" -lt "$RSS_FLOOR_KB" ]; then
      echo "  $label: adjusted RSS ${rlast}KB < floor ${RSS_FLOOR_KB}KB (retention flat) -- PASS"
    elif [ -n "$rworst" ] && awk -v e="$rworst" -v g="$rssgate" 'BEGIN{exit !(e <= g)}'; then
      echo "  $label: largest-step RSS exponent $rworst <= $rssgate -- PASS"
    else
      echo "  $label: adjusted RSS ${rlast}KB over floor, RSS exponent ${rworst:-none} > $rssgate -- FAIL"
      fail=1
    fi
  fi
done
echo
[ "$fail" = 0 ] && echo "scale: all measured shapes PASS" || echo "scale: FAIL"
exit "$fail"
