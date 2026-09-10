#!/usr/bin/env bash
# scripts/natop-matrix.sh — THE PIN-DRIFT PROBE FOR ONE TOOLCHAIN
# (task #274).
#
# WHY THIS EXISTS.  con-leche pins the toolchain's own definitions of
# the fifteen kernel-accelerated `Nat` operations (`ConLeche/Kernel/
# NatOpPins.lean`, `pins/<toolchain>.json`) and of the two
# compiler-trust opaque values (`ConLeche/Kernel/TrustPins.lean`).  At
# install the stream's declaration is compared against the pin by
# definitional equality, so a stream exported by a DIFFERENT toolchain
# than the one the checker was built with is accepted only as long as
# upstream has not respelled the operation.  That drift is real: when
# `Decidable` was rewritten on lean4 master, `Nat.mod`'s export stopped
# matching the pin and the whole stream was declined at that record.
#
# This script is the per-toolchain half of the probe:
#
#     scripts/natop-matrix.sh v4.33.0
#     scripts/natop-matrix.sh leanprover/lean4-nightly:nightly-2026-09-10
#
# It installs the toolchain if elan does not have it, obtains an
# EXPORTER BUILT FOR THAT TOOLCHAIN, exports the dependency cone of the
# pinned constants, runs the con-leche binary over the result in
# verified mode, and prints ONE summary line on stdout:
#
#     toolchain | exporter | records | verdict | first failing record
#
# Everything else goes to stderr, so a caller can do
# `line=$(scripts/natop-matrix.sh "$tc")` and keep the exit code
# (0 accept, non-zero anything else — the checker's own exit codes are
# passed through: 1 reject, 2 decline, 3 error).  A summary line is
# printed even when the run never reaches the checker (`n/a` verdicts
# `no-toolchain`, `no-exporter`, `export-failed`).
#
# A THIRD KIND OF DRIFT, and the silent one: a pinned constant that no
# longer EXISTS under that name.  Both exporters answer an unknown name
# with `panic! "Constant X not found in environment."` and still exit 0,
# so the stream simply comes back short and the checker never sees the
# record.  The script reads those names off the exporter's stderr; a run
# that is otherwise an accept becomes `accept(incomplete)` and fails.
# (Measured 2026-09-10: `Lean.reduceBool` and `Lean.reduceNat` — the
# whole compiler-trust escape hatch — are gone from `Init` on lean4
# master.)
#
# THE EXPORTER.  Two sources, in this order:
#
#   1. `leanexport` in the toolchain's own `bin/`.  Lean ships an
#      exporter itself since `src/LeanExport.lean` landed upstream
#      (2026-08-28, lean4#14885) — that is, in nightlies from then on
#      and in releases after v4.34.0-rc2.  Its command line is
#      lean4export's: `leanexport Init -- Nat.div Nat.mod ...`.
#   2. Otherwise github.com/leanprover/lean4export, built HERE against
#      the target toolchain.  That repo tags a release per Lean release
#      (`v4.33.0`, `v4.29.1`, ...), so the ref is the exact tag when it
#      exists; a Lean patch release with no tag of its own (v4.32.1 and
#      v4.33.1 in the matrix, v4.28.1 below its floor, as of this
#      writing) falls back to the newest
#      tag that is not newer than the target, and the clone's
#      `lean-toolchain` is overwritten with the target either way — the
#      exporter must link against the toolchain whose environment it
#      dumps.
#
# THE CONSTANTS.  `ConLeche/Kernel/Core.lean` is the authority:
# `natOpNames` (pred add sub mul pow beq ble) and `natDivModNames`
# (div mod gcd land lor xor shiftLeft shiftRight), plus the two
# `TrustPins` opaque values `Lean.reduceBool` / `Lean.reduceNat`.
# `Nat.succ` needs no entry — it is a constructor of `Nat` and rides in
# on every cone.  The list below is checked against `Core.lean` on
# every run (`--no-verify-names` turns that off for a tree where the
# sources are not present).
#
# RESOURCES (CLAUDE.md): every checker run is under `ulimit -v` and
# `timeout`, and passes an explicit `--jobs=4` — the default worker
# count is the hardware thread count and each worker reserves address
# space, which aborts under the limit.  Builds get a `timeout` only.
#
# Usage:
#   scripts/natop-matrix.sh [OPTIONS] <toolchain>
#
#     <toolchain>          `v4.33.0`, `leanprover/lean4:v4.33.0`, or
#                          `leanprover/lean4-nightly:nightly-2026-09-10`
#     --binary PATH        the con-leche binary
#                          (default .lake/build/bin/con-leche)
#     --work DIR           scratch root (default _tmp/pin-matrix)
#     --jobs N             checker worker threads (default 4)
#     --mem KB             checker address-space limit
#                          (default 16000000, i.e. ~16 GiB)
#     --timeout SECS       checker timeout (default 900)
#     --no-verify-names    skip the cross-check of the constant list
#                          against ConLeche/Kernel/Core.lean
#
# The export and the checker's log are left under <work>/exports —
# a failing run is diagnosed from them.
set -uo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"

BINARY="$ROOT/.lake/build/bin/con-leche"
WORK="$ROOT/_tmp/pin-matrix"
JOBS=4
MEMKB=16000000
CHECK_TIMEOUT=900
BUILD_TIMEOUT=1800
VERIFY_NAMES=1
LEAN4EXPORT_URL="${LEAN4EXPORT_URL:-https://github.com/leanprover/lean4export.git}"

TC_IN=""
while (($#)); do
  case "$1" in
    --binary) BINARY="$2"; shift 2 ;;
    --work) WORK="$2"; shift 2 ;;
    --jobs) JOBS="$2"; shift 2 ;;
    --mem) MEMKB="$2"; shift 2 ;;
    --timeout) CHECK_TIMEOUT="$2"; shift 2 ;;
    --no-verify-names) VERIFY_NAMES=0; shift ;;
    -h|--help) awk 'NR > 1 && /^#/ { print; next } NR > 1 { exit }' \
                 "${BASH_SOURCE[0]}"; exit 0 ;;
    -*) echo "natop-matrix: unknown option $1" >&2; exit 3 ;;
    *) TC_IN="$1"; shift ;;
  esac
done

[ -n "$TC_IN" ] || { echo "usage: natop-matrix.sh [OPTIONS] <toolchain>" >&2; exit 3; }

# ---------------------------------------------------------------------
# The summary line.  Printed exactly once, on stdout, whatever happens.
EXPORTER="n/a"
RECORDS="n/a"
VERDICT="n/a"
FAILREC="-"
summary_printed=0
emit_summary() {
  [ "$summary_printed" = 1 ] && return 0
  summary_printed=1
  printf '%s | %s | %s | %s | %s\n' \
    "$TC" "$EXPORTER" "$RECORDS" "$VERDICT" "$FAILREC"
}
die() {  # die <verdict> <message>
  VERDICT="$1"; shift
  echo "natop-matrix: $*" >&2
  emit_summary
  exit 3
}

# ---------------------------------------------------------------------
# 1. The toolchain.
#
# `v4.33.0` is shorthand for `leanprover/lean4:v4.33.0`; a
# `nightly-...` name for `leanprover/lean4-nightly:...`; anything with
# a `/` or `:` is taken as written.
case "$TC_IN" in
  */*|*:*) TC="$TC_IN" ;;
  nightly-*) TC="leanprover/lean4-nightly:$TC_IN" ;;
  *) TC="leanprover/lean4:$TC_IN" ;;
esac
# elan's directory spelling, and the version part for tag matching
TC_VERSION="${TC##*:}"

command -v elan >/dev/null || die no-toolchain "elan is not on PATH"

# `elan toolchain list` marks the default one with a suffix, so the
# comparison is on the first field.
if ! elan toolchain list | awk '{print $1}' | grep -qxF "$TC"; then
  echo "natop-matrix: installing $TC" >&2
  timeout "$BUILD_TIMEOUT" elan toolchain install "$TC" >&2 \
    || die no-toolchain "elan could not install $TC"
fi

SYSROOT="$(elan run "$TC" lean --print-prefix 2>/dev/null | tr -d '\r')"
[ -n "$SYSROOT" ] && [ -d "$SYSROOT" ] \
  || die no-toolchain "no sysroot for $TC"
LEAN_VERSION="$(elan run "$TC" lean --version 2>/dev/null | tr -d '\r')"
echo "natop-matrix: $TC — $LEAN_VERSION" >&2
echo "natop-matrix: sysroot $SYSROOT" >&2

# ---------------------------------------------------------------------
# 2. The constant list, and its cross-check against the kernel source.
NAT_OPS=(Nat.pred Nat.add Nat.sub Nat.mul Nat.pow Nat.beq Nat.ble)
NAT_WF_OPS=(Nat.div Nat.mod Nat.gcd Nat.land Nat.lor Nat.xor
            Nat.shiftLeft Nat.shiftRight)
TRUST_PINS=(Lean.reduceBool Lean.reduceNat)
CONSTANTS=("${NAT_OPS[@]}" "${NAT_WF_OPS[@]}" "${TRUST_PINS[@]}")

CORE="$ROOT/ConLeche/Kernel/Core.lean"
if [ "$VERIFY_NAMES" = 1 ] && [ -f "$CORE" ]; then
  # `natOpNames` / `natDivModNames` are lists of `natXxxName`
  # abbreviations, each `def natXxxName : Name := natName.str "xxx"`.
  extract_list() {  # extract_list <def name>
    sed -n "/^def $1 : List Name :=/,/\]/p" "$CORE" \
      | tr ',[]' '\n\n\n' | sed -n 's/^ *\(nat[A-Za-z]*Name\) *$/\1/p'
  }
  resolve() {  # resolve <natXxxName> -> Nat.xxx
    sed -n "s/^def $1 : Name := natName.str \"\([A-Za-z0-9]*\)\"/Nat.\1/p" "$CORE"
  }
  declared=()
  for sym in $(extract_list natOpNames) $(extract_list natDivModNames); do
    r="$(resolve "$sym")"
    [ -n "$r" ] || die names "cannot resolve $sym in ConLeche/Kernel/Core.lean"
    declared+=("$r")
  done
  want="$(printf '%s\n' "${NAT_OPS[@]}" "${NAT_WF_OPS[@]}" | sort)"
  have="$(printf '%s\n' "${declared[@]}" | sort)"
  if [ "$want" != "$have" ]; then
    echo "natop-matrix: the Nat-operation list in this script disagrees with" >&2
    echo "natop-matrix: ConLeche/Kernel/Core.lean (natOpNames + natDivModNames):" >&2
    diff <(printf '%s\n' "$want") <(printf '%s\n' "$have") >&2
    die names "constant list is stale — update scripts/natop-matrix.sh"
  fi
  echo "natop-matrix: constant list matches ConLeche/Kernel/Core.lean \
(${#declared[@]} Nat operations + ${#TRUST_PINS[@]} trust pins)" >&2
fi

# ---------------------------------------------------------------------
# 3. The exporter.
mkdir -p "$WORK/exports" || die setup "cannot create $WORK"

EXPORT_BIN=""
if [ -x "$SYSROOT/bin/leanexport" ]; then
  EXPORT_BIN="$SYSROOT/bin/leanexport"
  EXPORTER="leanexport(bundled)"
  echo "natop-matrix: exporter = the toolchain's own $EXPORT_BIN" >&2
else
  # lean4export, at the tag for this release (or the newest tag that is
  # not newer than it), built against the target toolchain.
  CLONE="$WORK/lean4export"
  if [ ! -d "$CLONE/.git" ]; then
    echo "natop-matrix: cloning lean4export" >&2
    timeout "$BUILD_TIMEOUT" git clone --quiet "$LEAN4EXPORT_URL" "$CLONE" >&2 \
      || die no-exporter "cannot clone $LEAN4EXPORT_URL"
  else
    timeout 300 git -C "$CLONE" fetch --quiet --tags origin >&2 || true
  fi

  tags="$(git -C "$CLONE" tag --list 'v*')"
  if printf '%s\n' "$tags" | grep -qxF "$TC_VERSION"; then
    REF="$TC_VERSION"
  else
    # The newest tag that is not newer than the target.  `sort -V` puts
    # `v4.33.0-rc1` AFTER `v4.33.0`, which is the wrong order for
    # Lean's scheme, so `-rc` becomes `~rc` for the sort (GNU sort
    # treats `~` as sorting before everything, the Debian rule) and
    # back afterwards.  A nightly, or a target older than every tag,
    # has no predecessor and falls back to the default branch.
    marked="$(printf '%s' "$TC_VERSION" | sed 's/-rc/~rc/')"
    REF="$(printf '%s\n%s\n' "$tags" "$TC_VERSION" | sed 's/-rc/~rc/' \
            | sort -V | grep -B1 -xF "$marked" | head -1 | sed 's/~rc/-rc/')"
    [ "$REF" = "$TC_VERSION" ] && REF=""
    if [ -z "$REF" ]; then
      REF="$(git -C "$CLONE" rev-parse --quiet --verify origin/HEAD >/dev/null \
             && echo origin/HEAD || echo origin/main)"
    fi
    echo "natop-matrix: lean4export has no tag $TC_VERSION — using $REF" >&2
  fi
  # `-f`: this script overwrote `lean-toolchain` on a previous run, and
  # git refuses to check out over a modified tracked file.
  git -C "$CLONE" checkout --quiet --force --detach "$REF" >&2 \
    || die no-exporter "lean4export has no ref $REF"
  # The exporter must run under the TARGET toolchain, not the one the
  # tag was cut against (they agree at an exact tag and differ at a
  # fallback).
  printf '%s\n' "$TC" > "$CLONE/lean-toolchain"
  echo "natop-matrix: building lean4export@$REF against $TC" >&2
  ( cd "$CLONE" && timeout "$BUILD_TIMEOUT" lake build >&2 ) \
    || die no-exporter "lean4export@$REF does not build against $TC"
  EXPORT_BIN="$CLONE/.lake/build/bin/lean4export"
  [ -x "$EXPORT_BIN" ] || die no-exporter "no binary at $EXPORT_BIN"
  EXPORTER="lean4export@$REF"
fi

# ---------------------------------------------------------------------
# 4. The export: the dependency cone of the pinned constants out of
# `Init` (transitive dependencies are pulled in by the exporter).
STREAM="$WORK/exports/natops-$(printf '%s' "$TC" | tr '/:' '--').ndjson"
echo "natop-matrix: exporting ${#CONSTANTS[@]} constant cones from Init" >&2
# `elan run` is what fixes the SYSROOT: the exporter calls
# `findSysroot`, which shells out to `lean --print-prefix`, and the bare
# `lean` on PATH is elan's shim — in a directory with a different
# `lean-toolchain` it would answer for the wrong toolchain and the
# import would fail on an incompatible olean header.
if ! timeout "$BUILD_TIMEOUT" elan run "$TC" "$EXPORT_BIN" Init -- "${CONSTANTS[@]}" \
       > "$STREAM" 2> "$STREAM.err"; then
  echo "natop-matrix: the exporter failed:" >&2
  tail -20 "$STREAM.err" >&2
  die export-failed "$EXPORT_BIN Init -- ... exited non-zero"
fi
[ -s "$STREAM" ] || die export-failed "the exporter produced an empty stream"
echo "natop-matrix: $(wc -l < "$STREAM") stream lines in $STREAM" >&2

# A REQUESTED CONSTANT THAT NO LONGER EXISTS is itself pin drift, and
# it is a SILENT one: both exporters answer an unknown name with
# `panic! "Constant X not found in environment."` and still exit 0, so
# the stream comes back short and the checker never sees the record.
# (Measured 2026-09-10: `Lean.reduceBool` / `Lean.reduceNat` are gone
# from `Init` on lean4 master.)  The names are read off the exporter's
# stderr — the message is the same in lean4export and in the bundled
# leanexport.
MISSING="$(sed -n 's/.*Constant \([^ ]*\) not found in environment.*/\1/p' \
             "$STREAM.err" | sort -u | tr '\n' ' ' | sed 's/ $//')"
if [ -n "$MISSING" ]; then
  echo "natop-matrix: PINNED CONSTANTS ABSENT FROM Init: $MISSING" >&2
fi
if [ -s "$STREAM.err" ] && [ -z "$MISSING" ]; then
  echo "natop-matrix: the exporter wrote to stderr:" >&2
  head -5 "$STREAM.err" | sed 's/^/    /' >&2
fi

# ---------------------------------------------------------------------
# 5. The checker.
[ -x "$BINARY" ] || die no-binary "no con-leche binary at $BINARY"

LOG="$WORK/exports/$(basename "$STREAM" .ndjson).log"
(
  ulimit -v "$MEMKB"
  timeout "$CHECK_TIMEOUT" "$BINARY" --verified --jobs="$JOBS" "$STREAM"
) > "$LOG" 2>&1
rc=$?
sed 's/^/    /' "$LOG" >&2

# `con-leche: accepted N declarations (--verified)` on stdout;
# `con-leche: <error> [at <name>, fold position <i>] (--verified) t=...`
# on stderr.  Both are in the log.
RECORDS="$(sed -n 's/^con-leche: accepted \([0-9]*\) declarations.*/\1/p' "$LOG" | tail -1)"
[ -n "$RECORDS" ] || RECORDS="$(sed -n 's/^con-leche: declined (\([0-9]*\) declarations checked.*/\1/p' "$LOG" | tail -1)"
[ -n "$RECORDS" ] || RECORDS="?"
FAILREC="$(sed -n 's/.*\[at \([^]]*\)\].*/\1/p' "$LOG" | head -1 \
            | sed 's/, fold position \([0-9]*\)/ @\1/')"
[ -n "$FAILREC" ] || FAILREC="-"

case "$rc" in
  0) VERDICT="accept" ;;
  1) VERDICT="reject" ;;
  2) VERDICT="decline" ;;
  124) VERDICT="timeout" ;;
  *) VERDICT="error($rc)" ;;
esac

# An accept must actually have accepted something: a zero-declaration
# "accept" would mean the cone did not reach the pinned operations.
if [ "$rc" = 0 ]; then
  if [ "$RECORDS" = "?" ] || [ "$RECORDS" -le 0 ] 2>/dev/null; then
    VERDICT="no-declarations"
    rc=3
  fi
fi

# An accept over a stream the exporter could not complete is not an
# accept of the pins: the absent constants were never checked.
if [ -n "$MISSING" ]; then
  if [ "$rc" = 0 ]; then VERDICT="accept(incomplete)"; rc=1; fi
  if [ "$FAILREC" = "-" ]; then FAILREC="absent from Init: $MISSING"
  else FAILREC="$FAILREC; absent from Init: $MISSING"; fi
fi

emit_summary
exit "$rc"
