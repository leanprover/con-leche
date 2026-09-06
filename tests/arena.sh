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
# Usage: tests/arena.sh [--no-sweeps] [tests-dir]
#
# An <expectation> is a single exit code.  Until task #148 T0b it could
# also be a pair "<on>|<off>" for the five fixtures whose verdict
# depended on the direct simple-structure master switch
# (`Setlec.directStructsEnabled`, Setlec/Kernel/Direct.lean, task
# #119/#120), and `--direct-off` ran the whole suite against a second
# binary built with the switch off.  The switch now ships `false` — the
# configuration both verified lanes reason about — so the shipped binary
# *is* the former "off" column: the pairs collapsed to single codes and
# the second-binary harness (tests/build-direct-off.sh) went with them.
# The pre-flip codes are recorded in the two expectation files.
#
# THE MODE SWEEP (task #147; one mode fewer since #148 T7b).  The
# checker has one two-valued mode: `--verified` (the default — the
# surface the set model proves) and `--trusted` (the unverified lane:
# checking-mode front door, infer-only internals, no certificate
# families; it absorbs the retired --yolo/SETLEC_NO_PROOF_CERTS and
# --infer-only/SETLEC_INFER_ONLY).  `--tt-model` selected the seven
# TT-lane checks for the declarative verification lane; that lane was
# deleted at #148 T7b and the flag is a hard error now, so its sweep —
# which had claimed and shown byte-identity with the default on every
# fixture — went with it.  The certified sections run at the default
# (`--verified`); afterwards both suites run again
#
#   * with `--trusted`, against the certified expectations plus the
#     recorded overrides in tests/trusted-expected.txt (the successor
#     of tests/yolo-expected.txt — see that file's header for what may
#     be recorded: partial-stack divergences of the unverified lane,
#     each with the defect it stops or starts detecting differently).
#
# `--no-sweeps` skips the extra pass for a tight edit loop; a landing
# gate runs it.
set -u
cd "$(dirname "$0")/.."

MODE_SWEEPS=on
args=()
for a in "$@"; do
  case "$a" in
    --no-sweeps) MODE_SWEEPS=off;;
    *) args+=("$a");;
  esac
done
set -- ${args+"${args[@]}"}

TESTS_DIR="${1:-_tmp/arena-tests}"
BIN=.lake/build/bin/setlec
EXPECTED=tests/arena-expected.txt
E2E_EXPECTED=tests/e2e-expected.txt
ANNOT_EXPECTED=tests/annot-expected.txt
T_EXPECTED=tests/trusted-expected.txt

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


# The trusted-mode overrides, keyed "<suite> <fixture> <mode>" (mode empty
# for arena lines and for plain e2e lines).  See the file's header for
# when a line belongs in here.
declare -A T_OVR=()
if [ -f "$T_EXPECTED" ]; then
  while read -r yexp ysuite yrel ymode; do
    case "$yexp" in ''|'#'*) continue;; esac
    T_OVR["$ysuite $yrel ${ymode:-}"]=$yexp
  done < "$T_EXPECTED"
fi

# SWEEP is `cert` for the default (--verified) pass and `trusted` for
# the --trusted pass; it selects the mode flag, the override table and
# the failure wording.
SWEEP=cert
MODEFLAG=""

# Resolve $want for one fixture: the certified expectation, overridden
# in the trusted sweep if tests/trusted-expected.txt records a
# divergence.
resolve() { # <expectation-field> <suite> <fixture> <mode>
  want=$1
  want_src=certified
  if [ "$SWEEP" = trusted ]; then
    local o=${T_OVR["$2 $3 ${4:-}"]:-}
    if [ -n "$o" ]; then want=$o; want_src="tests/trusted-expected.txt"; fi
  fi
  return 0
}

# Report a verdict that is not the expected one.  In the extra sweeps a
# mismatch is a *divergence from the default mode* (the expectation is
# the certified one unless overridden), so it is worded as such.
mismatch() { # <prefix> <fixture> <want> <got>
  case "$SWEEP" in
    trusted) echo "TRUSTED-MODE DIVERGENCE $2: $want_src expects exit $3, --trusted got $4";;
    *) echo "$1 $2: expected exit $3, got $4";;
  esac
  fail=1
}

fail=0
accepted=0
total_good=0

# THE LAYERING GATE (task #161 S1).  The separation's boundary — the
# collapsed-model tree and the graded-model tree import nothing of each
# other over the shared base — is checked from the source tree, with a
# whitelist of the cross edges the campaign's remaining batches remove.
# It runs here so the standard battery fails if the boundary rots.
if tests/layering.sh; then :; else fail=1; fi

# THE PROOF-TERM GATE (task #161 S10).  The layering gate above measures
# where code SITS; this one measures what the capstones USE — the
# transitive constant closure of their type and proof term, pinned row
# by row.  S9's finding is why both are needed: the import gate read
# "0 P->R edges" while `Red.beta` was live on the shipped P capstone's
# proof path.  The pin only ever tightens.
if tests/proofdeps.sh; then :; else fail=1; fi

# THE PIN-DUMP FRESHNESS GATE (task #176).  The pinned Nat-operation
# declarations and their certificate proof blobs are a COMMITTED
# generator output (pins/<toolchain>.json, see pins/README.md) since the
# olean-by-name load was removed from the checker's build.  As with
# every committed generator output here, staleness is a test failure:
# regenerate and diff.
if tests/pindump.sh; then :; else fail=1; fi

# THE AXIOM PIN (2026-09-06, external review §2/§5.1).  The six
# consistency capstones carry `#guard_msgs in #print axioms` guards in
# `tests/SetlecTests/Axioms.lean`, pinning them at exactly
# `[propext, Classical.choice, Quot.sound]`.  The guards ARE the
# elaboration of that module, so building the test library is the gate:
# a drifting axiom footprint is a build error, not a claim in the
# journal.  (`lake test` runs the same library; this line is so the
# standard battery says so too.)
AXLOG=$(lake build SetlecTests 2>&1)
if [ $? = 0 ] && ! printf '%s\n' "$AXLOG" | grep -q 'error:'; then
  echo "axioms: pinned (6 capstones at [propext, Classical.choice, Quot.sound])"
else
  echo 'AXIOM PIN FAIL — tests/SetlecTests/Axioms.lean did not elaborate:'
  printf '%s\n' "$AXLOG" | grep -A6 'error:' | head -40 | sed 's/^/    /'
  echo '    a changed `#print axioms` message is a FINDING: report it,'
  echo '    do not relax the guard.'
  fail=1
fi

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
    timeout 60 "$BIN" $MODEFLAG "$f" >/dev/null 2>&1
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
#
# The committed `pre` fixtures were preprocessed by the STOCK tool, so
# they still carry `_model` artifacts for blocks the direct install
# recognises; that is inert (the W4c priority gate ignores them) and
# they are deliberately left alone as pre-#178 baselines.  A fixture
# regenerated from now on should go through `setlec-preprocess`.
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
      SETLEC_INDUCTIVE_MODELS=/nonexistent timeout 60 "$BIN" $MODEFLAG "$src" >/dev/null 2>&1
    elif [ "${mode:-}" = pre ]; then
      # `pre` fixtures assert the --pre flag: the input is taken as
      # already preprocessed — no detection scan, no spawn.  The
      # preprocessor is left *available*, so a fixture whose verdict
      # depends on not preprocessing (std_axioms declines at the raw
      # `Iff` block) catches a broken/ignored flag.
      timeout 60 "$BIN" $MODEFLAG --pre "$src" >/dev/null 2>&1
    else
      timeout 60 "$BIN" $MODEFLAG "$src" >/dev/null 2>&1
    fi
    got=$?
    if [ "$got" != "$want" ]; then
      mismatch "E2E FAIL" "$rel" "$want" "$got"
    else
      e2e_ok=$((e2e_ok+1))
    fi
  done < "$E2E_EXPECTED"
}

# --- the annotated suite (task #161) --------------------------------
# Hand-written export streams whose binder records carry the "pw"
# sort-annotation field; see tests/annot-expected.txt's header.
annot_half() {
  annot_ok=0
  annot_total=0
  while read -r exp rel; do
    case "$exp" in ''|'#'*) continue;; esac
    resolve "$exp" annot "$rel" ""
    annot_total=$((annot_total+1))
    timeout 60 "$BIN" $MODEFLAG "tests/annot/$rel" >/dev/null 2>&1
    got=$?
    if [ "$got" != "$want" ]; then
      mismatch "ANNOT FAIL" "$rel" "$want" "$got"
    else
      annot_ok=$((annot_ok+1))
    fi
  done < "$ANNOT_EXPECTED"
}

# THE CERTIFIED SWEEP, RESTORED (task #161 P5, 2026-09-01).  The P2..P5
# suspension is over: the annotate pass writes the `pw` datum for every
# binder of every unannotated stream, so the arena and e2e suites run at
# `--verified` again — validated, not merely checked.  A regression in
# the pass shows up here as a `sort-annotation mismatch (<site>)`
# decline against a certified expectation.  The annotated fixture suite
# stays and is now the pass's *negative* gate: the annot_decline_*
# streams carry explicit wrong claims the pass must not overwrite.
arena_half
echo "arena tutorial: $accepted/$total_good good tests accepted"
if [ -f "$E2E_EXPECTED" ]; then
  e2e_half
  echo "e2e: $e2e_ok/$e2e_total as expected"
fi
annot_half
echo "annot suite: $annot_ok/$annot_total as expected"


# Retired flag surface (task #172): the `--core` selector and the split
# install/check driver (`--install-only` / `--check-range`) were arena
# machinery and went with the interned representation.  They are HARD
# ERRORS, not silently ignored — the same rule the retired mode
# environment variables follow: a verdict's provenance must be readable
# off the invocation.  The fixtures below are the streams the mode
# section reuses.
SPLIT_GOOD=tests/annot/annot_split_good.ndjson
SPLIT_BAD=tests/annot/annot_split_bad.ndjson
split_ok=0
split_total=0
split_case() {
  want=$1; shift
  split_total=$((split_total+1))
  timeout 120 "$BIN" "$@" >/dev/null 2>&1
  got=$?
  if [ "$got" != "$want" ]; then
    echo "RETIRED-FLAG FAIL ($*): expected exit $want, got $got"; fail=1
  else
    split_ok=$((split_ok+1))
  fi
}
split_case 0 "$SPLIT_GOOD"                        # the one driver: accept
split_case 1 "$SPLIT_BAD"                         # …and it still rejects
split_case 3 --install-only "$SPLIT_GOOD"         # retired: hard error
split_case 3 --check-range 0:2 "$SPLIT_GOOD"      # retired: hard error
split_case 3 --check-range=0:2 "$SPLIT_GOOD"      # …in the `=` spelling too
split_case 3 --core=production "$SPLIT_GOOD"      # retired core selector
split_case 3 --core=cached-parsed "$SPLIT_GOOD"   # …including the one that won
split_case 3 --core production "$SPLIT_GOOD"      # …in the two-token spelling
echo "retired flags: $split_ok/$split_total as expected"

# The mode flags (task #147): the modes parse and judge the smoke
# fixtures alike — the verified lane (`--verified`, the default) and
# the trusted lane (`--trusted`) — and the RETIRED flags/environment
# variables error out with a pointer to the new modes rather than being
# silently ignored.  `--set-model=r` joined them 2026-09-05: the R core
# and the collapsed-model consistency proof it was the subject of were
# deleted, and the spelling must not silently alias onto a different
# core.  `--set-model`, `--set-model=p` and `--no-model` joined them at
# the mode rename (2026-09-06): they name the same two cores under the
# old vocabulary, and even so they are hard errors, not aliases — a
# verdict's provenance must be readable off the invocation.
mode_ok=0
mode_total=0
mode_case() {
  want=$1; shift
  mode_total=$((mode_total+1))
  timeout 120 "$BIN" "$@" >/dev/null 2>&1
  got=$?
  if [ "$got" != "$want" ]; then
    echo "MODE FAIL ($*): expected exit $want, got $got"; fail=1
  else
    mode_ok=$((mode_ok+1))
  fi
}
mode_case 0 --verified "$SPLIT_GOOD"               # the default, spelled out
mode_case 1 --verified "$SPLIT_BAD"                # …and it still rejects
mode_case 0 --trusted "$SPLIT_GOOD"                # trusted lane: accepts
mode_case 1 --trusted "$SPLIT_BAD"                 # front door still rejects
mode_case 3 --set-model "$SPLIT_GOOD"              # RENAMED: hard error
mode_case 3 --set-model=p "$SPLIT_GOOD"            # …the `=p` spelling too
mode_case 3 --no-model "$SPLIT_GOOD"               # RENAMED: hard error
mode_case 3 --no-model "$SPLIT_BAD"                # …on a bad stream too
mode_case 3 --tt-model "$SPLIT_GOOD"               # retired flag: hard error
mode_case 3 --trusted --install-only "$SPLIT_GOOD" # retired flag: hard error
mode_case 3 --set-model=r "$SPLIT_GOOD"            # RETIRED R lane: hard error
mode_case 3 --set-model=r "$SPLIT_BAD"             # …on a bad stream too
mode_case 3 --yolo "$SPLIT_GOOD"                   # retired flag: hard error
mode_case 3 --infer-only "$SPLIT_GOOD"             # retired flag: hard error
mode_total=$((mode_total+1))
if SETLEC_NO_PROOF_CERTS=1 timeout 120 "$BIN" "$SPLIT_GOOD" \
    >/dev/null 2>&1; [ $? = 3 ]; then
  mode_ok=$((mode_ok+1))                           # retired env var: hard error
else
  echo "MODE FAIL: SETLEC_NO_PROOF_CERTS=1 did not error"
  fail=1
fi
mode_total=$((mode_total+1))
if SETLEC_INFER_ONLY=1 timeout 120 "$BIN" "$SPLIT_GOOD" \
    >/dev/null 2>&1; [ $? = 3 ]; then
  mode_ok=$((mode_ok+1))                           # retired env var: hard error
else
  echo "MODE FAIL: SETLEC_INFER_ONLY=1 did not error"
  fail=1
fi
echo "mode flags: $mode_ok/$mode_total as expected"

# The mode sweep (task #147): both suites again with `--trusted`
# (certified expectations plus the recorded overrides in
# tests/trusted-expected.txt).  See the header.
if [ "$MODE_SWEEPS" = on ]; then
  SWEEP=trusted
  MODEFLAG=--trusted
  t_fail_before=$fail
  arena_half
  t_arena=$arena_checked
  e2e_half
  annot_half
  SWEEP=cert
  MODEFLAG=""
  if [ "$fail" = "$t_fail_before" ]; then
    # "as expected" rather than "agree": the overridden fixtures
    # deliberately do not agree — they are the recorded divergences of
    # the unverified lane, counted here so a silently emptied
    # tests/trusted-expected.txt is visible in the summary line.
    echo "trusted sweep: $t_arena arena + $e2e_total e2e +" \
         "$annot_total annot as expected" \
         "(${#T_OVR[@]} recorded divergences)"
  else
    echo "trusted sweep: DIVERGED — see the lines above" \
         "(tests/trusted-expected.txt header: what may be recorded)"
  fi
fi

exit $fail
