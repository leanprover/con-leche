#!/usr/bin/env bash
# Verdict-parity gate for the cached-clone performance pilot.
#
# Runs every fixture of the arena, e2e and annot suites through the
# three `--core=` variants and requires *identical* verdicts:
#
#   production        checkDeclsSP        (the shipped driver)
#   interned-shared   checkDeclsShared    (interned core, Expr-typed
#                                          shared-state driver)
#   cached            the pilot's clone   (same driver, cached core)
#   cached-parsed     the clone under its own parsed-declaration
#                     driver (the configuration to compare with
#                     production)
#
# `production` vs `interned-shared` is the driver control (it must
# already agree — both are kernel code); `interned-shared` vs `cached`
# and `production` vs `cached-parsed` are the pilot's claims.  Both
# exit codes and the decision-relevant stdout line ("setlec: accepted
# N declarations") are compared.
#
# Usage: tests/pilot-parity.sh [--mode=--verified|--trusted] [tests-dir]
set -u
cd "$(dirname "$0")/.."

MODEFLAG=--verified
args=()
for a in "$@"; do
  case "$a" in
    --mode=*) MODEFLAG="${a#--mode=}";;
    *) args+=("$a");;
  esac
done
set -- ${args+"${args[@]}"}

TESTS_DIR="${1:-_tmp/arena-tests}"
BIN=.lake/build/bin/setlec
TIMEOUT=${PILOT_TIMEOUT:-300}

lake build setlec >/dev/null || exit 3

fail=0
checked=0
divergent=0

# run <label> <core> -- <cmd...>; sets $got and $out
run_one() {
  local core=$1; shift
  local out
  out=$(timeout "$TIMEOUT" "$BIN" $MODEFLAG "--core=$core" "$@" 2>/dev/null)
  got=$?
  # keep only the decision-relevant stdout line
  outline=$(printf '%s\n' "$out" | grep -E '^setlec: (accepted|installed|checked)' || true)
}

# compare <suite> <fixture-label> <cmd...>
compare() {
  local label=$1; shift
  checked=$((checked+1))
  run_one production "$@";      local p_got=$got p_out=$outline
  run_one interned-shared "$@"; local i_got=$got i_out=$outline
  run_one cached "$@";          local c_got=$got c_out=$outline
  run_one cached-parsed "$@";   local q_got=$got q_out=$outline
  if [ "$i_got" != "$c_got" ] || [ "$i_out" != "$c_out" ]; then
    echo "PARITY FAIL $label: interned-shared exit $i_got ($i_out) vs cached exit $c_got ($c_out)"
    fail=1
  elif [ "$c_got" != "$q_got" ] || [ "$c_out" != "$q_out" ]; then
    echo "PARITY FAIL $label: cached exit $c_got ($c_out) vs cached-parsed exit $q_got ($q_out)"
    fail=1
  elif [ "$p_got" != "$c_got" ] || [ "$p_out" != "$c_out" ]; then
    echo "DRIVER DIVERGENCE $label: production exit $p_got ($p_out) vs clone exit $c_got ($c_out)"
    divergent=$((divergent+1))
  fi
}

echo "== arena suite ($MODEFLAG)"
while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  compare "arena/$rel" "$TESTS_DIR/$rel"
done < tests/arena-expected.txt

echo "== e2e suite ($MODEFLAG)"
while read -r exp rel mode; do
  case "$exp" in ''|'#'*) continue;; esac
  src="tests/e2e/$rel"
  if [ ! -f "$src" ] && [ -f "$src.gz" ]; then
    tmpf="${TMPDIR:-/tmp}/setlec-pilot-$(basename "$rel")"
    gunzip -c "$src.gz" > "$tmpf" || { echo "E2E gunzip failed $rel"; fail=1; continue; }
    src="$tmpf"
  fi
  case "${mode:-}" in
    raw) SETLEC_INDUCTIVE_MODELS=/nonexistent compare "e2e/$rel[raw]" "$src";;
    pre) compare "e2e/$rel[pre]" --pre "$src";;
    *)   compare "e2e/$rel" "$src";;
  esac
done < tests/e2e-expected.txt

echo "== annot suite ($MODEFLAG)"
while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  compare "annot/$rel" "tests/annot/$rel"
done < tests/annot-expected.txt

echo "pilot parity: $checked fixtures compared, $divergent production/shared-driver divergences"
if [ "$fail" = 0 ]; then echo "PILOT PARITY OK"; else echo "PILOT PARITY FAILED"; fi
exit $fail
