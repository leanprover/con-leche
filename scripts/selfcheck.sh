#!/usr/bin/env bash
# scripts/selfcheck.sh — THE SELF-CHECK.
#
# The checker checks that its own main theorems hold for the implementation
# the shipped binary is built from.  `comparator.json` names the pair:
# `ConLeche.Challenge` states the main theorems about the binary's runs with
# `sorry`, and the binary's functions they name (`runArgs`, `parseChunks`,
# `searchPathOf`, `trustedOr`, `CmpReq.solRoots`) are holes there,
# `def … := sorry` at their real names and types; `ConLeche.MainTheorem` is the
# solution, which proves the theorems over the real definitions.  Con-leche
# checks the challenge against the solution with `--compare`: both sides are
# checked in full, and every hole and every theorem of the challenge must be
# justified by the solution's constant of the same name and statement,
# everything the statement reads being the same constant in both or itself a
# justified hole.
#
# WHY IT MEANS SOMETHING.  The theorems constrain the solution's
# implementation of the hole functions, and the binary is built from that
# implementation (`Main.lean` runs `runArgs`).  An accept says: the
# statements a reader trusts (the challenge, specification imports only) are
# proved, over the code the binary runs, and the proofs pass this checker.
#
# THE TWO FORMS.  Both run by default; each must exit 0 and justify exactly
# `comparator.json`'s `theorem_names` and `definition_names`.
#
#   1. `.olean`: `con-leche --olean --compare -- ConLeche.Challenge
#      ConLeche.MainTheorem` over the built tree's `.olean` files and the
#      toolchain's.  Both import closures are checked whole.
#   2. lean4export JSON: the toolchain's `leanexport` exports the dependency
#      cone of the listed names from each side (the challenge declares nothing
#      else), and `con-leche --compare -- challenge.ndjson solution.ndjson`
#      checks them.  This runs the exporter and the JSON reader at scale.  The
#      exporter skips `unsafe` declarations (the `@[implemented_by]` fast
#      paths); an accept also shows that no exported constant refers to one
#      (an unknown constant is a rejection).
#
# THE VERDICT AND THE COST at `compare` 274f01384 (task #628), `--verified`,
# instructions:u, peak RSS as the checker reports it, wall on a 96-thread
# machine:
#
#   .olean   exit 0, challenge 95,586 declarations, solution 257,344,
#            15 justified; 1.92 T; 1.22 GiB / 48 s at --jobs=4,
#            6.15 GiB / 16 s at 96 workers.
#   export   challenge 32 MB, solution 0.92 GB / 16.5M lines; 0.35 T,
#            3.4 GB peak, 35 s (single-threaded).
#   JSON     exit 0, challenge 6,221 declarations, solution 48,683,
#            15 justified; 0.64 T; 0.92 GiB / 16 s at --jobs=4.
#
# USAGE
#     scripts/selfcheck.sh [--jobs=N] [--no-json] [OUTDIR]
#
#   The exit code is the checker's: the first form's that is not 0 (1 reject,
#   2 decline, 3 error); 1 also when an accepting run's justified names are
#   not `comparator.json`'s; 3 when the build or the export fails.
#   `--jobs=N` (default: 8, or the core count if lower) bounds the worker
#   pool, and with it the memory (one memo state per worker).  There is no
#   `ulimit -v` (CLAUDE.md); the bound is the `timeout`.  `--no-json` skips
#   the second form.
#
#   OUTDIR (default `_tmp/selfcheck`) receives, every run anew:
#     names.txt                         comparator.json's names
#     build.log                         the build of both sides and the binary
#     olean.out, olean.err              the first form's verdict and stats
#     challenge.ndjson, solution.ndjson the exports
#     json.out, json.err                the second form's verdict and stats
set -uo pipefail
cd "$(dirname "$0")/.."

usage() { echo "usage: scripts/selfcheck.sh [--jobs=N] [--no-json] [OUTDIR]" >&2; exit 3; }
OUTDIR=_tmp/selfcheck
JSON=on
JOBS=$(nproc 2>/dev/null || echo 8); [ "$JOBS" -gt 8 ] && JOBS=8
for a in "$@"; do
  case "$a" in
    --jobs=*)  JOBS=${a#--jobs=} ;;
    --no-json) JSON=off ;;
    -*) usage ;;
    *)  OUTDIR=$a ;;
  esac
done
mkdir -p "$OUTDIR"
OUTDIR=$(cd "$OUTDIR" && pwd)
say() { echo "[selfcheck] $*"; }

read -r C S <<< "$(python3 -c '
import json; c=json.load(open("comparator.json"))
print(c["challenge_module"], c["solution_module"])')" || { say "cannot read comparator.json"; exit 3; }
python3 -c '
import json; c=json.load(open("comparator.json"))
print("\n".join(sorted(c["theorem_names"]+c["definition_names"])))' > "$OUTDIR/names.txt" \
  || { say "cannot read comparator.json"; exit 3; }
mapfile -t NAMES < "$OUTDIR/names.txt"

# The challenge is in no default target, so a plain `lake build` leaves a
# stale `.olean` of it in place; build both sides here.
say "building $C $S con-leche"
timeout 3600 lake build "$C" "$S" con-leche > "$OUTDIR/build.log" 2>&1 \
  || { say "build FAILED"; tail -20 "$OUTDIR/build.log"; exit 3; }
LIBDIR=$(timeout 120 lake env lean --print-libdir) || { say "no toolchain libdir"; exit 3; }
BIN=.lake/build/bin/con-leche

verdict=0
# $1: form, $2: exit code, $3: output file
judge() {
  local code=$2
  if [ "$code" != 0 ]; then
    say "$1: exit $2"; grep -v '^con-leche: stats' "$3" | tail -10
  elif ! diff <(sed -n 's/^con-leche: [a-z]* \(.*\) justified by the solution$/\1/p' "$3" | sort) \
              "$OUTDIR/names.txt" > "$OUTDIR/names.diff"; then
    say "$1: the justified names are not comparator.json's (< run, > config):"
    head -20 "$OUTDIR/names.diff"
    code=1
  else
    say "$1: $(grep -o 'accepted [0-9]* declarations, [0-9]* axioms justified' "$3") \
($(grep -o '[0-9]* declarations accepted' "$3") in the solution)"
  fi
  if [ "$verdict" = 0 ]; then verdict=$code; fi
}

# ---------------------------------------------------------------- the .olean form
say "olean: --olean --compare -- $C $S (--verified --jobs=$JOBS)"
timeout 3600 "$BIN" --verified --jobs="$JOBS" --olean --compare \
  --search-path="$PWD/.lake/build/lib/lean:$LIBDIR" -- "$C" "$S" \
  > "$OUTDIR/olean.out" 2> "$OUTDIR/olean.err"
judge olean $? "$OUTDIR/olean.out"

# ---------------------------------------------------------------- the JSON form
if [ "$JSON" = on ]; then
  EXPORT_BIN="$(timeout 120 lake env lean --print-prefix)/bin/leanexport"
  [ -x "$EXPORT_BIN" ] || { say "the toolchain ships no leanexport ($EXPORT_BIN)"; exit 3; }
  say "exporting the cones of ${#NAMES[@]} names from $C and $S"
  timeout 1800 lake env "$EXPORT_BIN" "$C" -- "${NAMES[@]}" > "$OUTDIR/challenge.ndjson" \
    && timeout 1800 lake env "$EXPORT_BIN" "$S" -- "${NAMES[@]}" > "$OUTDIR/solution.ndjson" \
    || { say "export FAILED"; exit 3; }
  say "json: --compare -- challenge.ndjson solution.ndjson (--verified --jobs=$JOBS)"
  timeout 3600 "$BIN" --verified --jobs="$JOBS" --compare \
    -- "$OUTDIR/challenge.ndjson" "$OUTDIR/solution.ndjson" \
    > "$OUTDIR/json.out" 2> "$OUTDIR/json.err"
  judge json $? "$OUTDIR/json.out"
fi

say "exit $verdict"
exit $verdict
