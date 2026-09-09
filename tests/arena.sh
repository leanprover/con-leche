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
# (`ConLeche.structsEnabled`, ConLeche/Kernel/Inductives/*, task
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
# families; it absorbs the retired --yolo/CON_LECHE_NO_PROOF_CERTS and
# --infer-only/CON_LECHE_INFER_ONLY).  `--tt-model` selected the seven
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

# Scratch space goes to DISK, never tmpfs (task #180).  Honour TMPDIR if
# the caller set one; otherwise use the project's on-disk scratch
# directory rather than the system temp, which is commonly a RAM-backed
# tmpfs — the gzipped e2e fixtures below expand to gigabytes.  Exported,
# so the checker and every child honour the same choice.
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"

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
BIN=.lake/build/bin/con-leche
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

lake build con-leche >/dev/null || exit 3


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

# THE TRUST-SURFACE GATE (2026-09-06, external review §5.6).  The
# layering gate fences one direction of trust (the implementation may
# not import the theory); this one fences the other — no compiler
# escape (`unsafe`, `implemented_by`, `computed_field`, `native_decide`,
# …) outside the allowlisted trusted-surface files, whose justification
# is the script's header.  It is the companion of the axiom pin above:
# `#print axioms` sees the LOGICAL TCB, this one sees the RUNTIME TCB,
# and neither sees the other's.
if tests/trust-surface.sh; then :; else fail=1; fi

# THE OVERVIEW LINK GATE (task #216).  `OVERVIEW.md` is the guided tour
# of the proof, and nearly every claim in it is anchored at a LINE RANGE
# of a source file.  Line anchors rot silently — one added `import`
# slides every anchor in a module — so the gate copies the cited lines
# into a committed text (`tests/overview-links-expected.txt`) and diffs.
# A diff is not "the docs are broken": it means a citation moved (update
# the `#L<a>-L<b>`) or its text changed (re-read the paragraph that
# cites it, then `tests/overview-links.sh --update`).  Source-tree only,
# no build, milliseconds.
if tests/overview-links.sh; then :; else fail=1; fi

# THE IMPORT GATE (task #235).  Two questions no other gate asks and the
# compiler answers for neither: is an import LINE needed at all (`lake shake`,
# read against task #223's criterion and an allowlist of the proposals that
# criterion rejects), and does a line need its `public` keyword — a re-export
# only something else's PUBLIC statement can require, whose absence shows up
# as a `rfl` that stops closing rather than an unknown identifier.  Needs the
# built tree; ~1 min, most of it the two olean dumps the fixpoint reads.
if tests/shake.sh; then :; else fail=1; fi

# THE INSTALL-ROUTE CENSUS (task #207, the successor of task #193's
# native-predicate audit).  There is no external predicate to compare
# the recognisers against any more — the preprocessor and its mirror
# went together — so this gate pins what the ONE implementation does:
# every inductive block of every good arena fixture must route
# `struct`, `sum`, `fix`, `inmodel` or `basis`
# (`CON_LECHE_ROUTE_TRACE`, Main.lean), never `modeled` (a model out of
# the stream) and never "no install route" (a block reaching the fold
# bare).  `tests/route-census.sh --full` adds init-full.
if tests/route-census.sh; then :; else fail=1; fi

# THE IN-PROCESS MODELLER'S GATE (task #200; the modeller is the only
# model source since #207): the raw mutual/nested fixtures through the
# generator, the debug dump re-checked in both modes, and the off
# switch.  See tests/inmodel.sh's header.
if tests/inmodel.sh; then :; else fail=1; fi

# THE AXIOM PIN (2026-09-06, external review §2/§5.1).  The two main
# theorems, the four letters, the assembly under them and the `IO`
# loop's bridge — and, since task #181, the `False` letters — carry `#guard_msgs in #print axioms`
# guards in `tests/ConLecheTests/Axioms.lean`, pinning them at exactly
# `[propext, Classical.choice, Quot.sound]`.  The guards ARE the
# elaboration of that module, so building the test library is the gate:
# a drifting axiom footprint is a build error, not a claim in the
# journal.  (`lake test` runs the same library; this line is so the
# standard battery says so too.)
AXLOG=$(lake build ConLecheTests 2>&1)
if [ $? = 0 ] && ! printf '%s\n' "$AXLOG" | grep -q 'error:'; then
  nax=$(grep -c '^#print axioms' tests/ConLecheTests/Axioms.lean)
  echo "axioms: pinned ($nax theorems at [propext, Classical.choice, Quot.sound])"
else
  echo 'AXIOM PIN FAIL — tests/ConLecheTests/Axioms.lean did not elaborate:'
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
# Own end-to-end tests: committed `lean4export` streams of
# tests/e2e/src/*.lean, every one of them run RAW (task #207 — there
# is no preprocessing step any more; regenerate a fixture by exporting
# the module with the arena's lean4export and committing its NDJSON,
# gzipped when large).
#
# Every stream here is raw (task #219: there is no input-model path —
# the in-process modeller is the only model source and a `_model`
# record in a stream is an ordinary declaration).  The 34 fixtures that
# carried preprocessor-era model families were regenerated; three
# fixtures keep `_model` NAMES on purpose, as the controls that the
# name is not special: `model_name_plain`, `budget_model` and
# `yolo_decline_vs_accept`.
e2e_half() {
  e2e_ok=0
  e2e_total=0
  while read -r exp rel; do
    case "$exp" in ''|'#'*) continue;; esac
    resolve "$exp" e2e "$rel" ""
    e2e_total=$((e2e_total+1))
    src="tests/e2e/$rel"
    if [ ! -f "$src" ] && [ -f "$src.gz" ]; then
      # large fixtures are committed gzipped
      tmpf="$TMPDIR/con-leche-e2e-$(basename "$rel")"
      gunzip -c "$src.gz" > "$tmpf" || { echo "E2E FAIL $rel: gunzip failed"; fail=1; continue; }
      src="$tmpf"
    fi
    timeout 60 "$BIN" $MODEFLAG "$src" >/dev/null 2>&1
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
# verdict's provenance must be readable off the invocation.  `--pre`
# joined them at task #207, when the preprocessor it asserted about was
# dropped: every input is a raw lean4export stream now.
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
mode_case 3 --pre "$SPLIT_GOOD"                    # RETIRED at #207: hard error
mode_case 3 --pre "$SPLIT_BAD"                     # …on a bad stream too
mode_case 3 --yolo "$SPLIT_GOOD"                   # retired flag: hard error
mode_case 3 --infer-only "$SPLIT_GOOD"             # retired flag: hard error
mode_total=$((mode_total+1))
if CON_LECHE_NO_PROOF_CERTS=1 timeout 120 "$BIN" "$SPLIT_GOOD" \
    >/dev/null 2>&1; [ $? = 3 ]; then
  mode_ok=$((mode_ok+1))                           # retired env var: hard error
else
  echo "MODE FAIL: CON_LECHE_NO_PROOF_CERTS=1 did not error"
  fail=1
fi
mode_total=$((mode_total+1))
if CON_LECHE_INFER_ONLY=1 timeout 120 "$BIN" "$SPLIT_GOOD" \
    >/dev/null 2>&1; [ $? = 3 ]; then
  mode_ok=$((mode_ok+1))                           # retired env var: hard error
else
  echo "MODE FAIL: CON_LECHE_INFER_ONLY=1 did not error"
  fail=1
fi
echo "mode flags: $mode_ok/$mode_total as expected"

# THE BUILT-IN PRELUDE'S COUNT INVARIANT (task #191).  Every run now
# installs the six basis blocks and `Bool` first; a stream's own copies
# are dropped as duplicates.  The verdict line must still count the
# STREAM's declaration records — dropped copies included, since they
# are installed (from the prelude) and the official checker counts them
# — so the number is unchanged by the prelude's existence and equal
# across reorderings of the same records: natop_order.ndjson has 35
# declaration records (4 of them prelude duplicates: Nat, PUnit, Bool,
# Eq), and natop_before_eq.ndjson / natop_before_ble.ndjson are the same
# 35 records in other orders.
prelude_ok=0
prelude_total=0
prelude_count() { # <fixture> <expected count>
  prelude_total=$((prelude_total+1))
  local got
  got=$(timeout 120 "$BIN" "tests/e2e/$1" 2>/dev/null | sed -n 's/^con-leche: accepted \([0-9]*\) declarations.*/\1/p')
  if [ "$got" = "$2" ]; then
    prelude_ok=$((prelude_ok+1))
  else
    echo "PRELUDE COUNT FAIL $1: expected 'accepted $2 declarations', got '${got:-no accept line}'"
    fail=1
  fi
}
prelude_count natop_order.ndjson 35
prelude_count natop_before_eq.ndjson 35
prelude_count natop_before_ble.ndjson 35
echo "prelude counts: $prelude_ok/$prelude_total as expected"

# The progress lane (`--progress[=<stride>]`, 2026-09-07; a FLAG since
# task #229).  Two folds, one verdict: without the flag the driver runs
# the verified `checkDecls`, with it the unverified `checkDeclsProgressIO`
# — the same steps with a line printed before each declaration.  The
# checks below are the contract: the lane prints, it prints EVERY
# declaration at stride 1 (that is the localisation mode: a dying run
# names the declaration it died in on its last line), and it changes no
# verdict, on an accepting and on a rejecting fixture alike.
prog_ok=0
prog_total=0
prog_check() { # <description> <condition-result>
  prog_total=$((prog_total+1))
  if [ "$2" = ok ]; then
    prog_ok=$((prog_ok+1))
  else
    echo "PROGRESS FAIL: $1"; fail=1
  fi
}
# the accepting fixture: exit 0 with and without the flag, same
# stdout verdict line, and one progress line per declaration at stride 1
prog_out=$(timeout 120 "$BIN" "$SPLIT_GOOD" 2>/dev/null); prog_code=$?
prog_err1=$(timeout 120 "$BIN" --progress=1 "$SPLIT_GOOD" 2>&1 >/dev/null)
prog_out1=$(timeout 120 "$BIN" --progress=1 "$SPLIT_GOOD" 2>/dev/null)
prog_code1=$?
prog_lines=$(printf '%s\n' "$prog_err1" | grep -c '^con-leche: progress [0-9]')
# one line per FOLD record: the stream's records after the built-in
# prelude's (task #191) — the total the closing "fold done: N/N" line
# names; the verdict line counts the stream's records only
prog_decls=$(printf '%s\n' "$prog_err1" | sed -n 's/^con-leche: progress fold done: [0-9]*\/\([0-9]*\) .*/\1/p')
prog_check "stride 1 exits 0 on the accepting fixture" \
  "$([ "$prog_code1" = 0 ] && echo ok)"
prog_check "the verdict line is unchanged by the flag" \
  "$([ "$prog_out" = "$prog_out1" ] && [ "$prog_code" = "$prog_code1" ] && echo ok)"
prog_check "stride 1 prints one line per fold record" \
  "$([ -n "$prog_decls" ] && [ "$prog_lines" = "$prog_decls" ] && echo ok)"
prog_check "the lane brackets the run (parse done / fold done)" \
  "$(printf '%s' "$prog_err1" | grep -q 'progress parse done' && \
     printf '%s' "$prog_err1" | grep -q 'progress fold done' && echo ok)"
# the rejecting fixture: still exit 1, still naming the declaration
prog_errB=$(timeout 120 "$BIN" --progress=1 "$SPLIT_BAD" 2>&1 >/dev/null)
prog_codeB=$?
prog_check "stride 1 still rejects the bad fixture (exit 1)" \
  "$([ "$prog_codeB" = 1 ] && echo ok)"
prog_check "the rejection still names the failing declaration" \
  "$(printf '%s' "$prog_errB" | grep -q '\[at .*, fold position [0-9]' && echo ok)"
# bare --progress is stride 1, and the flag composes with the mode flag
# in either order
prog_errBare=$(timeout 120 "$BIN" --progress "$SPLIT_GOOD" 2>&1 >/dev/null)
prog_errPost=$(timeout 120 "$BIN" --trusted --progress=1 "$SPLIT_GOOD" 2>&1 >/dev/null)
prog_errPre=$(timeout 120 "$BIN" --progress=1 --trusted "$SPLIT_GOOD" 2>&1 >/dev/null)
prog_check "bare --progress is stride 1" \
  "$([ "$(printf '%s\n' "$prog_errBare" | grep -c '^con-leche: progress [0-9]')" \
      = "$prog_lines" ] && echo ok)"
prog_check "--progress composes with --trusted in either order" \
  "$([ "$(printf '%s\n' "$prog_errPost" | grep -c '^con-leche: progress [0-9]')" \
      = "$(printf '%s\n' "$prog_errPre" | grep -c '^con-leche: progress [0-9]')" ] && \
    printf '%s' "$prog_errPost" | grep -q 'progress fold done' && echo ok)"
# the check pass (task #253): the ONE loop installs every record, then
# checks every recorded declaration — one `check` line per record,
# bracketed by the `install done` line naming their number
prog_lines2c=$(printf '%s\n' "$prog_err1" | grep -c '^con-leche: progress check [0-9]')
prog_pending2=$(printf '%s\n' "$prog_err1" | sed -n 's/^con-leche: progress install done: \([0-9]*\) pending.*/\1/p')
prog_check "stride 1 prints one check line per pending record" \
  "$([ -n "$prog_pending2" ] && [ "$prog_lines2c" = "$prog_pending2" ] && [ "$prog_pending2" -gt 0 ] && echo ok)"
# a bad stride is a USAGE error (exit 3), not a silently degraded run
timeout 120 "$BIN" --progress=x "$SPLIT_GOOD" >/dev/null 2>&1; prog_codeX=$?
timeout 120 "$BIN" --progress=0 "$SPLIT_GOOD" >/dev/null 2>&1; prog_code0=$?
prog_check "--progress=x is a usage error (exit 3)" \
  "$([ "$prog_codeX" = 3 ] && echo ok)"
prog_check "--progress=0 is a usage error (exit 3)" \
  "$([ "$prog_code0" = 3 ] && echo ok)"
# THE ENVIRONMENT VARIABLE IS GONE (task #229), not aliased: a stale
# script that still exports it gets a plain run, heartbeat and all
# absent, so it cannot keep working silently.
prog_errEnv=$(CON_LECHE_PROGRESS=1 timeout 120 "$BIN" "$SPLIT_GOOD" 2>&1 >/dev/null)
prog_outEnv=$(CON_LECHE_PROGRESS=1 timeout 120 "$BIN" "$SPLIT_GOOD" 2>/dev/null)
prog_codeEnv=$?
prog_check "CON_LECHE_PROGRESS is ignored: no heartbeat" \
  "$([ "$(printf '%s\n' "$prog_errEnv" | grep -c '^con-leche: progress')" = 0 ] && echo ok)"
prog_check "CON_LECHE_PROGRESS changes no verdict" \
  "$([ "$prog_outEnv" = "$prog_out" ] && [ "$prog_codeEnv" = "$prog_code" ] && echo ok)"
echo "progress lane: $prog_ok/$prog_total as expected"

# THE DAG-TOWER GATE (tasks #215, #226).  The frontend tree-size budget
# is gone; what stands in its place is a fixture, not a limit.
# `tests/e2e/tower_*.ndjson` (scripts/mk_tower_fixtures.py) put a shared
# tower of depth 60 — about 2^60 nodes unshared, ~190 entries as a DAG —
# into one record kind each.  A walk that is not DAG-safe never
# finishes on one, so the fixture hangs (or exhausts memory) and names
# the walker.  Task #226 completed the matrix: the four ACCEPTING kinds
# and the four DECLINING ones, whose verdict has to be reached without
# walking the tower — each through a lockstep comparison bounded by the
# pin it is compared against.  Task #233 added the OPEN tower — one
# built over a field's own variable rather than closed — which is what
# a packed-bound cutoff cannot answer and only a memo can.  Task #240
# added the EQUALITY-memo tower: two structurally equal towers that are
# not the same objects, shaped so that one node's memo entry alternates
# between two partners — which is what a memo keyed on one side of the
# comparison cannot answer and only a pair-keyed one can.  Task #246
# added the three block shapes the earlier kinds never entered: a
# RECURSIVE field (the fvar-occurrence question the install asks of
# every later field), and a MUTUAL and a NESTED block, which is where
# the in-process modeller's own walkers live.  The memory
# cap makes an unbounded walk fail fast instead of swapping the machine.
tower_ok=0
tower_total=0
tower_check() { # <description> <condition-result>
  tower_total=$((tower_total+1))
  if [ "$2" = ok ]; then
    tower_ok=$((tower_ok+1))
  else
    echo "TOWER FAIL: $1"; fail=1
  fi
}
tower_run() { # <fixture> <expected-exit> <description>
  t_code=0
  ( ulimit -v 8000000; timeout 60 "$BIN" "tests/e2e/$1.ndjson" >/dev/null 2>&1 ) \
    || t_code=$?
  tower_check "$3" "$([ "$t_code" = "$2" ] && echo ok)"
}
tower_run tower_thm 0 "a depth-60 tower in a theorem's type and value accepts"
tower_run budget_block 0 "the retired budget's block fixture still accepts, uncapped"
tower_run tower_struct 0 "a tower in a structure's constructor field type accepts"
tower_run tower_proj 0 \
  "a tower under a two-field structure's projection bodies accepts"
tower_run tower_axiom 2 \
  "a tower in Quot.sound's type declines without walking it"
tower_run tower_quot 2 \
  "a tower in a quotient record's type declines without walking it"
tower_run tower_prelude 2 \
  "a tower in a prelude-named block declines without walking it"
tower_run tower_axiom_pin 2 \
  "a tower in propext's type declines without walking it"
tower_run tower_axiom_nonstd 2 \
  "a tower in a non-pinned axiom's type declines on the name"
tower_run tower_usedlater 0 \
  "a tower over a field variable, asked about a LATER field, accepts"
tower_run tower_beqpair 0 \
  "two equal towers whose comparison alternates a node's partner accept"
tower_run tower_recfield 0 \
  "a tower after a RECURSIVE field, asked about that field, accepts"
tower_run tower_mutual 0 \
  "a tower in a MUTUAL block's field domain accepts"
tower_run tower_nested 0 \
  "a tower in a NESTED block's field domain accepts"
echo "DAG-tower gate: $tower_ok/$tower_total as expected"

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
