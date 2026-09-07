#!/usr/bin/env bash
# Cross-checker scale comparison (LOCAL ONLY — needs reference checker
# binaries that are not on CI).  Same methodology as tests/scale.sh:
# per shape, run at doubling n, measure retired instructions (perf
# stat -e instructions:u, median of 3), subtract the per-shape n=1
# startup baseline, report the per-doubling exponent — applied
# identically to con-leche, the official kernel checker, and upstream
# nanoda, so constant factors AND growth exponents can be compared.
#
# Reference binaries (override via env):
#   OFF  official lean4 kernel arena checker
#        (_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0)
#   NAN  upstream nanoda (_tmp/nanoda_lib)
#
# PITFALL — nanoda fork vs upstream: the reference clone `nanodatg`
# under _tmp/ is the *certifying* fork; it emits/validates
# certificates and is quadratic BY DESIGN on several shapes.  Never
# use it for growth comparisons — build and use UPSTREAM nanoda
# (https://github.com/ammkrn/nanoda_lib) instead, e.g.:
#   git clone https://github.com/ammkrn/nanoda_lib _tmp/nanoda_lib
#   (cd _tmp/nanoda_lib && cargo build --release)
# nanoda also requires structurally deduplicated table entries (it
# crashes on duplicates); tests/scale/gen.py hash-conses everything it
# emits, so its streams are safe for all three checkers.
#
# Shape coverage: the def-only shapes plus `fields`.  All streams are
# fed to the references raw, and so is con-leche (task #207: every
# checker here installs inductive blocks natively, so the rows compare
# the same code paths).  `ctors` is excluded by default
# because its stream is Theta(n^2) bytes (each of the n rule RHSs
# binds all n minors), which makes per-n exponents misleading across
# checkers; add it to SHAPES below if you want it anyway.
#
# Usage: tests/scale/compare.sh   (from anywhere; ~2-4 min)
set -u
cd "$(dirname "$0")/../.."

GEN=tests/scale/gen.py
SET=${SET:-.lake/build/bin/con-leche}
OFF=${OFF:-_tmp/perfcmp/arena-upstream/checkers/official-v4.33.0/.lake/build/bin/kernel}
NAN=${NAN:-_tmp/nanoda_lib/target/release/nanoda_bin}
TMP=$(mktemp -d)
trap 'rm -rf "$TMP"' EXIT

# upstream nanoda takes a JSON config and the stream on stdin
cat > "$TMP/nanoda.json" <<'EOF'
{
  "use_stdin": true,
  "nat_extension": true,
  "string_extension": true,
  "unpermitted_axiom_hard_error": false,
  "unsafe_permit_all_axioms": true,
  "num_threads": 1
}
EOF

if ! perf stat -e instructions:u true >/dev/null 2>&1; then
  echo "compare: perf unavailable — nothing to measure" >&2
  exit 1
fi

# shape:base-n  (same bases as tests/scale.sh standard mode)
SHAPES="chain:100 spine:50 many:100 telescope:50 dag:200 delta:100
        fanout:100 lets:100 lparams:100 thm:200 fields:25"

run_checker() { # run_checker CHECKER FILE
  case $1 in
    con-leche)   timeout 300 nice -n 10 "$SET" "$2" ;;
    official) timeout 300 nice -n 10 "$OFF" "$2" ;;
    nanoda)   timeout 300 nice -n 10 "$NAN" "$TMP/nanoda.json" < "$2" ;;
  esac
}

measure_once() { # CHECKER FILE -> instruction count
  case $1 in
    con-leche)   perf stat -e instructions:u -x, timeout 300 nice -n 10 "$SET" "$2" 2>&1 >/dev/null ;;
    official) perf stat -e instructions:u -x, timeout 300 nice -n 10 "$OFF" "$2" 2>&1 >/dev/null ;;
    nanoda)   perf stat -e instructions:u -x, timeout 300 nice -n 10 "$NAN" "$TMP/nanoda.json" < "$2" 2>&1 >/dev/null ;;
  esac | awk -F, '/instructions/{print $1}'
}

measure() { # CHECKER FILE -> median of 3
  local a b c
  a=$(measure_once "$1" "$2"); b=$(measure_once "$1" "$2"); c=$(measure_once "$1" "$2")
  [ -n "$a" ] && [ -n "$b" ] && [ -n "$c" ] || return 1
  printf '%s\n%s\n%s\n' "$a" "$b" "$c" | sort -n | sed -n 2p
}

for chk in con-leche official nanoda; do
  bin=$SET; [ "$chk" = official ] && bin=$OFF; [ "$chk" = nanoda ] && bin=$NAN
  if [ ! -x "$bin" ]; then
    echo "### $chk: binary $bin not found — skipped (local references only)"
    echo
    continue
  fi
  echo "### $chk"
  for spec in $SHAPES; do
    shape=${spec%:*}; n0=${spec#*:}
    python3 "$GEN" "$shape" 1 > "$TMP/base.ndjson"
    if ! run_checker "$chk" "$TMP/base.ndjson" >/dev/null 2>&1; then
      echo "  $shape: baseline (n=1) not accepted"; continue
    fi
    BASE=$(measure "$chk" "$TMP/base.ndjson") || { echo "  $shape: baseline measurement failed"; continue; }
    prev=
    line="$shape:"
    last=
    for m in 1 2 4 8; do
      n=$((n0 * m))
      python3 "$GEN" "$shape" "$n" > "$TMP/s.ndjson"
      if ! run_checker "$chk" "$TMP/s.ndjson" >/dev/null 2>&1; then
        echo "  $shape n=$n: not accepted"; prev=; continue
      fi
      cnt=$(measure "$chk" "$TMP/s.ndjson") || { echo "  $shape n=$n: measurement failed"; prev=; continue; }
      adj=$((cnt - BASE)); [ "$adj" -gt 0 ] || adj=1
      if [ -n "$prev" ]; then
        exp=$(awk -v a="$prev" -v b="$adj" 'BEGIN{printf "%.2f", log(b/a)/log(2)}')
        line="$line n=$n adj=$adj exp=$exp |"
        last=$exp
      else
        line="$line n=$n adj=$adj |"
      fi
      prev=$adj
    done
    echo "  $line  largest-step=$last"
  done
  echo
done
