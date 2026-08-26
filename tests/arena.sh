#!/usr/bin/env bash
# Run the checker over the lean kernel arena tutorial tests and compare
# against tests/arena-expected.txt (lines: "<expectation> <relative-path>").
#
# Exit codes of the checker: 0 accept, 1 reject, 2 decline, 3 error.
# Rules enforced here, beyond matching expectations:
#  * a "good" test must never be rejected (exit 1) or error (exit 3)
#  * a "bad" test must never be accepted (exit 0) — that would be a
#    soundness bug
# The expectations file additionally pins the current accept/decline status
# so that progress and regressions are both visible; update it consciously.
#
# Usage: tests/arena.sh [--direct-off] [tests-dir]
#
# An <expectation> is either a single exit code, as for the overwhelming
# majority of fixtures, or a pair "<on>|<off>" for the few fixtures whose
# verdict depends on the direct simple-structure master switch
# (`Setlec.directStructsEnabled`, Setlec/Kernel/Direct.lean, task #119):
# the left code is expected in the shipped configuration, the right one
# with the switch off.  Both forms are accepted in tests/arena-expected.txt
# and in tests/e2e-expected.txt.
#
# `--direct-off` runs the whole suite against a second binary built with
# that switch set to `false` (tests/build-direct-off.sh builds it into
# _tmp/, no source edit), applying the right-hand expectations.  It is an
# opt-in run — the default invocation is unchanged, and unchanged in cost.
set -u
cd "$(dirname "$0")/.."

DIRECT=on
args=()
for a in "$@"; do
  case "$a" in
    --direct-off) DIRECT=off;;
    *) args+=("$a");;
  esac
done
set -- ${args+"${args[@]}"}

TESTS_DIR="${1:-_tmp/arena-tests}"
BIN=.lake/build/bin/setlec
EXPECTED=tests/arena-expected.txt

# Select the applicable half of an expectation: "0|2" is (on|off), a bare
# "0" applies to both configurations.
if [ "$DIRECT" = off ]; then
  pick() { case "$1" in *'|'*) want=${1#*|};; *) want=$1;; esac; }
else
  pick() { case "$1" in *'|'*) want=${1%%'|'*};; *) want=$1;; esac; }
fi

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

if [ "$DIRECT" = off ]; then
  BIN=$(tests/build-direct-off.sh 2>/dev/null) || {
    echo "failed to build the direct-structs-off binary" \
         "(run tests/build-direct-off.sh to see why)" >&2; exit 3; }
  echo "direct simple-structure installs: OFF ($BIN)"
else
  lake build setlec >/dev/null || exit 3
fi

fail=0
accepted=0
total_good=0
while read -r exp rel; do
  case "$exp" in ''|'#'*) continue;; esac
  pick "$exp"
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
  while read -r exp rel mode; do
    case "$exp" in ''|'#'*) continue;; esac
    pick "$exp"
    e2e_total=$((e2e_total+1))
    src="tests/e2e/$rel"
    if [ ! -f "$src" ] && [ -f "$src.gz" ]; then
      # large fixtures are committed gzipped
      tmpf="${TMPDIR:-/tmp}/setlec-e2e-$(basename "$rel")"
      gunzip -c "$src.gz" > "$tmpf" || { echo "E2E FAIL $rel: gunzip failed"; fail=1; continue; }
      src="$tmpf"
    fi
    # a `raw` fixture is a plain lean4export result: run it with the
    # preprocessor made unavailable, so the stream really carries no
    # `_model` declarations and the direct install path is exercised
    if [ "${mode:-}" = raw ]; then
      SETLEC_INDUCTIVE_MODELS=/nonexistent timeout 60 "$BIN" "$src" >/dev/null 2>&1
    elif [ "${mode:-}" = pre ]; then
      # `pre` fixtures assert the --pre flag: the input is taken as
      # already preprocessed — no detection scan, no spawn.  The
      # preprocessor is left *available*, so a fixture whose verdict
      # depends on not preprocessing (std_axioms declines at the raw
      # `Iff` block) catches a broken/ignored flag.
      timeout 60 "$BIN" --pre "$src" >/dev/null 2>&1
    else
      timeout 60 "$BIN" "$src" >/dev/null 2>&1
    fi
    got=$?
    if [ "$got" != "$want" ]; then
      echo "E2E FAIL $rel: expected exit $want, got $got"; fail=1
    else
      e2e_ok=$((e2e_ok+1))
    fi
  done < "$E2E_EXPECTED"
  echo "e2e: $e2e_ok/$e2e_total as expected"
fi

# Split install/check driver (task #108): --install-only and
# --check-range.  Two properties are pinned here.
#  (a) Honesty: a run that checked less than the whole stream never
#      accepts (exit 0 is reserved for "everything was checked and
#      accepted" by the verified interleaved driver), and never
#      pronounces a stream invalid either — a skipped check might have
#      declined first, so a partial run downgrades `invalid` to a
#      decline.  Only exit 3 (usage/internal) is unconditional.
#  (b) Selectivity: a range that excludes a bad declaration must not
#      trip over it, while a range containing just that declaration
#      must find it — the whole point of the mode.
# Fixtures are the committed e2e ones: indexed_vec accepts, and
# nat_add_wrong has its type mismatch at declaration index 46
# (theorem addOk), well past the prefix its check needs.
SPLIT_GOOD=tests/e2e/indexed_vec.ndjson
SPLIT_BAD=tests/e2e/nat_add_wrong.ndjson
split_ok=0
split_total=0
split_case() {
  want=$1; shift
  split_total=$((split_total+1))
  timeout 120 "$BIN" "$@" >/dev/null 2>&1
  got=$?
  if [ "$got" != "$want" ]; then
    echo "SPLIT FAIL ($*): expected exit $want, got $got"; fail=1
  else
    split_ok=$((split_ok+1))
  fi
}
split_case 0 "$SPLIT_GOOD"                       # verified driver: accept
split_case 2 --install-only "$SPLIT_GOOD"        # installed, nothing checked
split_case 2 --check-range 0:2 "$SPLIT_GOOD"     # a subrange
split_case 2 --check-range 0: "$SPLIT_GOOD"      # all of it, but split driver
split_case 1 --check-range 0: "$SPLIT_BAD"       # full range finds the bad one
split_case 2 --check-range 46:47 "$SPLIT_BAD"    # just the bad one: reported…
split_case 2 --check-range 0:1 "$SPLIT_BAD"      # …excluded: not tripped over
split_case 2 --install-only "$SPLIT_BAD"         # nor installed into a reject
split_case 3 --check-range bogus "$SPLIT_GOOD"   # malformed range spec
split_case 3 --yolo --install-only "$SPLIT_GOOD" # unverified stack + split
# selectivity, positively: checking *only* declaration 46 must actually
# report that declaration's failure
split_total=$((split_total+1))
if timeout 120 "$BIN" --check-range 46:47 "$SPLIT_BAD" 2>&1 |
    grep -q "type mismatch in addOk"; then
  split_ok=$((split_ok+1))
else
  echo "SPLIT FAIL: --check-range 46:47 did not report addOk"; fail=1
fi
echo "split driver: $split_ok/$split_total as expected"

exit $fail
