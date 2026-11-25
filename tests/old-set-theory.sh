#!/usr/bin/env bash
# tests/old-set-theory.sh — THE OLD SET THEORY GATE.
#
# Before the first-order rewrite, `ConLeche.SetTheory` was second-order.
# `ConLecheTests.SetTheoryFO.setTheoryOfSecondOrder`
# (`tests/ConLecheTests/SetTheoryFO.lean`, built by `lake test`) proves
# that every model of the old class is a model of the current one:
#
#     ConLecheOld.SetTheory V → ConLeche.SetTheory V
#
# That theorem is only worth what its starting point is.
# `ConLecheOld.SetTheory` is declared by
# `tests/ConLecheTests/OldSetTheory.lean`, and this gate holds that file to
# the old one: `ConLeche/SetTheory/Core.lean` at commit bc6676101
# (2026-11-21), the last commit with the second-order class, with ONE name
# changed — its namespace, `ConLeche` to `ConLecheOld`, on the `namespace`
# and the `end` line.  (Unchanged, the file would declare
# `ConLeche.SetTheory` again, and Lean cannot import two declarations of
# one name.)
#
# The check undoes that rename and compares the git blob id, which needs
# no history:
#     git rev-parse bc6676101:ConLeche/SetTheory/Core.lean
# prints the same id where that commit is reachable.
#
# Source-tree only, no build, milliseconds.  Runs from `tests/arena.sh`
# and from CI's ci.yml.

set -u
cd "$(dirname "$0")/.." || exit 3

old=tests/ConLecheTests/OldSetTheory.lean
old_blob=b4dde49694f5729c5f5dc7e9d6c92744d80233d5
got=$(sed -e 's/^namespace ConLecheOld$/namespace ConLeche/' \
          -e 's/^end ConLecheOld$/end ConLeche/' "$old" | git hash-object --stdin) || exit 3
if [ "$got" != "$old_blob" ]; then
  echo "old-set-theory: FAIL — $old is not the old file with its namespace renamed" >&2
  echo "  blob id after undoing the rename: $got, expected $old_blob" >&2
  echo "  (ConLeche/SetTheory/Core.lean at commit bc6676101)" >&2
  exit 1
fi
if [ "$(grep -c -x -e 'namespace ConLecheOld' -e 'end ConLecheOld' "$old")" != 2 ]; then
  echo "old-set-theory: FAIL — $old does not carry the renamed namespace" >&2
  exit 1
fi
echo "old-set-theory: OK — the old file, identical but for its namespace"
