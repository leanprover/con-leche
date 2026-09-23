#!/usr/bin/env bash
# tests/nested-shadow.sh — POSITIVITY THROUGH CONTAINERS, measured
# against official (lane NESTPOS, deliverable 3's checker side).
#
# The check (`nestedBlockPositivity`, ConLeche/Kernel/Inductives/
# Positivity.lean) is GATED: the recogniser still routes every nested
# block to the modelled path, so no verdict of the shipped checker
# depends on it.  `--nested-shadow` runs it BESIDE the install at every
# block with a block shape and prints
#
#     con-leche: nested-shadow <block> <accept|reject|decline|error> ...
#
# (a plain accept that located no container instance, at a block the
# recogniser takes, is not printed).  This gate runs each fixture of
# `tests/nested-shadow-expected.txt` and compares the printed verdict
# WORDS, in fold order, with the row:
#
#     <fixture> <INMODEL> <block=word,block=word,...>
#
# `INMODEL=0` runs with `CON_LECHE_INMODEL=0`: the in-process modeller
# declines those blocks at parse time, so only with it off does the
# fold reach them.  A `.ndjson.gz` fixture is decompressed first.
#
# Usage: tests/nested-shadow.sh
set -u
cd "$(dirname "$0")/.."
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"

BIN=.lake/build/bin/con-leche
[ -x "$BIN" ] || { echo "nested-shadow: $BIN not built"; exit 1; }
WORK=$(mktemp -d "$TMPDIR/nested-shadow.XXXXXX")
trap 'rm -rf "$WORK"' EXIT

ok=0; total=0; fail=0
while read -r fx inmodel want; do
  case "$fx" in ''|'#'*) continue;; esac
  total=$((total + 1))
  f="$fx"
  if [ ! -f "$f" ] && [ -f "$f.gz" ]; then
    f="$WORK/$(basename "$fx")"; zcat "$fx.gz" > "$f"
  fi
  got=$(CON_LECHE_INMODEL="$inmodel" timeout 600 "$BIN" --nested-shadow "$f" 2>&1 >/dev/null \
        | sed -n 's/^con-leche: nested-shadow \([^ ]*\) \([a-z]*\).*/\1=\2,/p' | tr -d '\n')
  if [ "$got" = "$want" ]; then ok=$((ok + 1))
  else echo "  FAIL $fx: got '$got', want '$want'"; fail=1
  fi
done < tests/nested-shadow-expected.txt
echo "nested-shadow gate: $ok/$total as expected"
exit $fail
