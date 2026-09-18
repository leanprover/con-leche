#!/usr/bin/env bash
# tests/warning-free.sh — THE SOUND "is the build warning-free?" CHECK
# (task #315 L-B, 2026-09-18).
#
# WHY THIS EXISTS.  `lake build > log 2>&1` followed by a grep for
# `warning` is SOUND ON A COLD BUILD AND USELESS ON A WARM ONE: Lake
# does not re-emit a module's diagnostics when the module is already up
# to date, so every build after the one that first compiled a file shows
# a clean log for a tree that is not clean.  Two warnings stood in this
# tree for several reported-green sessions that way, and the merge that
# recompiled the file is what surfaced them.
#
# THE GENERAL RULE, which is worth more than this script:
#
#     A NEGATIVE CLAIM NEEDS A COMMAND THAT CAN EXPRESS THE NEGATIVE.
#     Before reporting "X does not occur", ask what the command would
#     have printed if X did.  If the answer is "the same thing", the
#     check proves nothing.
#
# It is this project's most reliable source of confident false
# negatives, and it is not specific to builds: the same shape produced a
# true observation about one lemma being read as a negative result about
# a whole question (DESIGN, lane L-B's entry at `519f610f`).
#
# WHAT THIS DOES.  Deletes the build artifacts of every module whose
# source differs from BASE (default: the merge base with `master`), so
# those modules and their dependents MUST recompile, then builds and
# counts warning lines with an unanchored, case-insensitive grep — a
# command that can express the negative.  Prints how many modules
# actually recompiled, which is the number that makes the result
# meaningful: if it is 0, the check proved nothing and says so.
#
# It does not replace `lake build`; it is what to run before REPORTING
# that a build is warning-free, and what to cite when you do.
#
# Usage: tests/warning-free.sh [BASE-REF]
set -u
cd "$(dirname "$0")/.."

BASE="${1:-}"
if [ -z "$BASE" ]; then
  BASE=$(git merge-base HEAD master 2>/dev/null || echo "")
fi
if [ -z "$BASE" ]; then
  echo "warning-free: no BASE ref (pass one; default is the merge base with master)" >&2
  exit 3
fi

LOG=_tmp/warning-free
mkdir -p "$LOG"

# The modules whose source moved: tracked changes since BASE, plus
# anything dirty in the working tree.
{ git diff --name-only "$BASE" HEAD; git status --porcelain | awk '{print $2}'; } \
  | grep -E '^(ConLeche|tests)/.*\.lean$|^ConLeche\.lean$|^Main\.lean$' \
  | sort -u > "$LOG/changed.txt"

NCHANGED=$(wc -l < "$LOG/changed.txt")
echo "warning-free: $NCHANGED changed module(s) since $BASE"

while read -r f; do
  m="${f%.lean}"
  for ext in olean ilean trace c; do
    rm -f ".lake/build/lib/lean/$m.$ext" ".lake/build/ir/$m.$ext"
  done
done < "$LOG/changed.txt"

FAIL=0
TOTBUILT=0
for target in build test; do
  if ! lake "$target" > "$LOG/$target.log" 2>&1; then
    echo "warning-free: lake $target FAILED"
    FAIL=1
  fi
  BUILT=$(grep -c 'Built ' "$LOG/$target.log" || true)
  WARN=$(grep -ic warning "$LOG/$target.log" || true)
  echo "warning-free: lake $target — $BUILT module(s) recompiled, $WARN warning line(s)"
  if [ "$WARN" != "0" ]; then
    grep -i warning "$LOG/$target.log" | head -20
    FAIL=1
  fi
  TOTBUILT=$((TOTBUILT + BUILT))
done

# `lake test` legitimately recompiles nothing once `lake build` has done
# the work, so the meaningful count is the TOTAL: only a run in which
# nothing anywhere recompiled proves nothing.
if [ "$TOTBUILT" = "0" ] && [ "$NCHANGED" != "0" ]; then
  echo "warning-free: NOTHING RECOMPILED — this run proves nothing about warnings" >&2
  FAIL=1
fi

if [ "$FAIL" = "0" ]; then
  echo "warning-free: OK (a run that could have failed)"
fi
exit "$FAIL"
