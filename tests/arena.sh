#!/usr/bin/env bash
# Run the checker over the lean kernel arena tutorial tests and compare
# against tests/arena-expected.txt (lines: "<expected-exit> <relative-path>").
#
# Exit codes of the checker: 0 accept, 1 reject, 2 decline, 3 error.
# Rules enforced here, beyond matching expectations:
#  * a "good" test must never be rejected (exit 1) or error (exit 3)
#  * a "bad" test must never be accepted (exit 0) — that would be a
#    soundness bug
# The expectations file additionally pins the current accept/decline status
# so that progress and regressions are both visible; update it consciously.
set -u
cd "$(dirname "$0")/.."

TESTS_DIR="${1:-_tmp/arena-tests}"
BIN=.lake/build/bin/setlec
EXPECTED=tests/arena-expected.txt

if [ ! -d "$TESTS_DIR" ]; then
  # The arena tests are vendored (pinned snapshot, 2026-08-19,
  # sha256 162c3c5f…) so CI never depends on the live arena's
  # progression.  Refresh deliberately by replacing the tarball.
  echo "arena tests not found; extracting vendored snapshot to $TESTS_DIR" >&2
  mkdir -p "$TESTS_DIR"
  if [ -f tests/arena/lean-arena-tests.tar.gz ]; then
    tar -xzf tests/arena/lean-arena-tests.tar.gz -C "$TESTS_DIR" || exit 3
  else
    curl -sL https://arena.lean-lang.org/lean-arena-tests.tar.gz | tar -xz -C "$TESTS_DIR" || exit 3
  fi
fi

lake build setlec >/dev/null || exit 3

fail=0
accepted=0
total_good=0
while read -r want rel; do
  case "$want" in ''|'#'*) continue;; esac
  f="$TESTS_DIR/$rel"
  timeout 60 "$BIN" "$f" >/dev/null 2>&1
  got=$?
  case "$rel" in
    good/*) total_good=$((total_good+1))
            [ "$got" = 0 ] && accepted=$((accepted+1))
            if [ "$got" = 1 ] || [ "$got" = 3 ]; then
              echo "FAIL $rel: good test got exit $got"; fail=1; continue
            fi;;
    bad/*)  if [ "$got" = 0 ]; then
              echo "SOUNDNESS FAIL $rel: bad test accepted"; fail=1; continue
            fi;;
  esac
  if [ "$got" != "$want" ]; then
    echo "CHANGE $rel: expected exit $want, got $got"; fail=1
  fi
done < "$EXPECTED"

echo "arena tutorial: $accepted/$total_good good tests accepted"

# Own end-to-end tests (committed exports of tests/e2e/src/*.lean;
# regenerate with lean-inductive-models' scripts/export-fixture.sh,
# FIXTURE_DIR=tests/e2e/src OUT_DIR=tests/e2e FILTER=0).
E2E_EXPECTED=tests/e2e-expected.txt
if [ -f "$E2E_EXPECTED" ]; then
  e2e_ok=0
  e2e_total=0
  while read -r want rel; do
    case "$want" in ''|'#'*) continue;; esac
    e2e_total=$((e2e_total+1))
    timeout 60 "$BIN" "tests/e2e/$rel" >/dev/null 2>&1
    got=$?
    if [ "$got" != "$want" ]; then
      echo "E2E FAIL $rel: expected exit $want, got $got"; fail=1
    else
      e2e_ok=$((e2e_ok+1))
    fi
  done < "$E2E_EXPECTED"
  echo "e2e: $e2e_ok/$e2e_total as expected"
fi
exit $fail
