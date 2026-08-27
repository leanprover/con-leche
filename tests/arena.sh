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
# Usage: tests/arena.sh [--direct-off] [--infer-only] [--no-yolo] [tests-dir]
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
#
# `--infer-only` runs the arena and e2e halves with SETLEC_INFER_ONLY=1
# (task #134), against the *same* expectations: the infer-only mode
# trusts subterms at internal re-derivations, so it could in principle
# accept a bad fixture the certified mode rejects — as of the landing
# measurement none does, and this run is what would surface it.  The
# split-driver half is skipped (the two modes are mutually exclusive by
# construction); one case pins that refusal instead.  Opt-in: the
# default invocation is unchanged and unchanged in cost.
#
# THE YOLO SWEEP (task #139).  After the certified sections a *second*
# pass over both expectation files runs with SETLEC_NO_PROOF_CERTS=1 —
# the cert-skipping measurement stack (Setlec/Kernel/{CoreNC,CheckerNC}
# .lean, task #76).  It runs by default, because the mode had silently
# drifted: `iotaRecNC` kept instantiating the stored nested-rule pins in
# the pre-#105 `mI`-context after the certified twin was lowered to the
# `rP`-context, and nothing in the harness ever ran a suite under the
# flag — the `<on>|<off>` pairs above are the --direct-off switch, not
# this one.  Measured cost of the extra pass (2026-08-27): ~17s arena +
# ~21s e2e on top of a ~48s certified run; `--no-yolo` skips it for a
# tight edit loop, but a landing gate runs it.  `--direct-off` and
# `--infer-only` skip it too — those are opt-in runs of a *different*
# configuration and stay unchanged in cost.
#
# The two stacks are expected to agree on every verdict except one
# acknowledged class-B divergence: yolo skips the per-argument
# application check everywhere, so a stream whose *only* defect is an
# application type mismatch can be accepted under yolo and rejected
# under the certified stack.  Such a fixture gets a yolo-specific
# expected exit code in tests/yolo-expected.txt (same idea as the
# `<on>|<off>` pairs, but as an override file rather than a column:
# as of 2026-08-27 no fixture in either suite diverges, so a column
# would be 205 unused separators).  Any other flip is a bug in the NC
# path — investigate, do not record it.
set -u
cd "$(dirname "$0")/.."

DIRECT=on
INFER_ONLY=off
YOLO_SWEEP=on
args=()
for a in "$@"; do
  case "$a" in
    --direct-off) DIRECT=off;;
    --infer-only) INFER_ONLY=on;;
    --no-yolo) YOLO_SWEEP=off;;
    *) args+=("$a");;
  esac
done
set -- ${args+"${args[@]}"}

TESTS_DIR="${1:-_tmp/arena-tests}"
BIN=.lake/build/bin/setlec
EXPECTED=tests/arena-expected.txt
E2E_EXPECTED=tests/e2e-expected.txt
YOLO_EXPECTED=tests/yolo-expected.txt

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

if [ "$INFER_ONLY" = on ]; then
  export SETLEC_INFER_ONLY=1
  echo "infer-only mode: ON (task #134; expectations unchanged)"
fi

# The yolo overrides, keyed "<suite> <fixture> <mode>" (mode empty for
# arena lines and for plain e2e lines).  See the header for when a line
# belongs in here.
declare -A YOLO_OVR=()
if [ -f "$YOLO_EXPECTED" ]; then
  while read -r yexp ysuite yrel ymode; do
    case "$yexp" in ''|'#'*) continue;; esac
    YOLO_OVR["$ysuite $yrel ${ymode:-}"]=$yexp
  done < "$YOLO_EXPECTED"
fi

# SWEEP is `cert` for the certified pass and `yolo` for the second one;
# it selects the override table and the failure wording.
SWEEP=cert

# Resolve $want for one fixture: the certified expectation, overridden
# in the yolo sweep if tests/yolo-expected.txt records a divergence.
resolve() { # <expectation-field> <suite> <fixture> <mode>
  pick "$1"
  want_src=certified
  if [ "$SWEEP" = yolo ]; then
    local o=${YOLO_OVR["$2 $3 ${4:-}"]:-}
    if [ -n "$o" ]; then want=$o; want_src="tests/yolo-expected.txt"; fi
  fi
  return 0
}

# Report a verdict that is not the expected one.  In the yolo sweep a
# mismatch is a *divergence from the certified stack* (the expectation
# is the certified one unless overridden), so it is worded as such.
mismatch() { # <prefix> <fixture> <want> <got>
  if [ "$SWEEP" = yolo ]; then
    echo "YOLO DIVERGENCE $2: $want_src expects exit $3, yolo got $4"
  else
    echo "$1 $2: expected exit $3, got $4"
  fi
  fail=1
}

fail=0
accepted=0
total_good=0

# --- the arena half ------------------------------------------------
arena_half() {
  accepted=0
  total_good=0
  arena_checked=0
  while read -r exp rel; do
    case "$exp" in ''|'#'*) continue;; esac
    resolve "$exp" arena "$rel" ""
    arena_checked=$((arena_checked+1))
    f="$TESTS_DIR/$rel"
    timeout 60 "$BIN" "$f" >/dev/null 2>&1
    got=$?
    case "$rel" in
      good/*) total_good=$((total_good+1))
              [ "$got" = 0 ] && accepted=$((accepted+1))
              if [ "$got" = 1 ] || [ "$got" = 3 ]; then
                mismatch FAIL "$rel" "$want" "$got"; continue
              fi;;
      bad/*)  if [ "$got" = 0 ]; then
                mismatch "SOUNDNESS FAIL" "$rel" "$want" "$got"; continue
              fi;;
    esac
    if [ "$got" != "$want" ]; then
      mismatch CHANGE "$rel" "$want" "$got"
    fi
  done < "$EXPECTED"
}

# --- the e2e half --------------------------------------------------
# Own end-to-end tests (committed exports of tests/e2e/src/*.lean;
# regenerate with lean-inductive-models' scripts/export-fixture.sh,
# FIXTURE_DIR=tests/e2e/src OUT_DIR=tests/e2e FILTER=0).
e2e_half() {
  e2e_ok=0
  e2e_total=0
  while read -r exp rel mode; do
    case "$exp" in ''|'#'*) continue;; esac
    resolve "$exp" e2e "$rel" "${mode:-}"
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
      mismatch "E2E FAIL" "$rel" "$want" "$got"
    else
      e2e_ok=$((e2e_ok+1))
    fi
  done < "$E2E_EXPECTED"
}

arena_half
echo "arena tutorial: $accepted/$total_good good tests accepted"

if [ -f "$E2E_EXPECTED" ]; then
  e2e_half
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
# The split driver is the certified stack's; an infer-only run pins the
# refusal to combine the two and leaves the rest of this section alone.
if [ "$INFER_ONLY" = on ]; then
  timeout 120 "$BIN" --install-only "$SPLIT_GOOD" >/dev/null 2>&1
  if [ $? = 3 ]; then
    echo "infer-only: refuses the split driver, as expected"
  else
    echo "INFER-ONLY FAIL: --install-only under SETLEC_INFER_ONLY did not error"
    fail=1
  fi
  exit $fail
fi
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

# The infer-only mode (task #134): it accepts what the certified stack
# accepts and rejects what it rejects, and it refuses to be combined
# with either of the other two non-default stacks — each combination
# would make a verdict's provenance unreadable.  The whole-suite sweep
# with the mode on is the opt-in `tests/arena.sh --infer-only` run.
io_ok=0
io_total=0
io_case() {
  want=$1; shift
  io_total=$((io_total+1))
  timeout 120 "$BIN" "$@" >/dev/null 2>&1
  got=$?
  if [ "$got" != "$want" ]; then
    echo "INFER-ONLY FAIL ($*): expected exit $want, got $got"; fail=1
  else
    io_ok=$((io_ok+1))
  fi
}
io_case 0 --infer-only "$SPLIT_GOOD"                 # accepts the good stream
io_case 1 --infer-only "$SPLIT_BAD"                  # still rejects the bad one
io_case 3 --infer-only --install-only "$SPLIT_GOOD"  # + split driver: refused
io_case 3 --infer-only --yolo "$SPLIT_GOOD"          # + measurement mode: refused
io_total=$((io_total+1))
if SETLEC_INFER_ONLY=1 timeout 120 "$BIN" --install-only "$SPLIT_GOOD" \
    >/dev/null 2>&1; [ $? = 3 ]; then
  io_ok=$((io_ok+1))                                 # …also via the env var
else
  echo "INFER-ONLY FAIL: SETLEC_INFER_ONLY=1 --install-only did not error"
  fail=1
fi
echo "infer-only: $io_ok/$io_total as expected"

# The yolo sweep (task #139): both suites again under
# SETLEC_NO_PROOF_CERTS=1, against the certified expectations plus the
# recorded class-B overrides.  See the header.
if [ "$YOLO_SWEEP" = on ] && [ "$DIRECT" = on ]; then
  SWEEP=yolo
  export SETLEC_NO_PROOF_CERTS=1
  yolo_fail_before=$fail
  arena_half
  yolo_arena=$arena_checked
  e2e_half
  unset SETLEC_NO_PROOF_CERTS
  SWEEP=cert
  if [ "$fail" = "$yolo_fail_before" ]; then
    echo "yolo sweep: $yolo_arena arena + $e2e_total e2e agree with certified" \
         "(${#YOLO_OVR[@]} recorded divergences)"
  else
    echo "yolo sweep: DIVERGED — see the lines above" \
         "(tests/arena.sh header: what belongs in tests/yolo-expected.txt)"
  fi
fi

exit $fail
