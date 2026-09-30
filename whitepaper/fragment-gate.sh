#!/usr/bin/env bash
# whitepaper/fragment-gate.sh — THE WHITEPAPER FRAGMENT GATE (task #324).
#
# `whitepaper/Fragment/*.lean` is the self-contained Lean verification
# of the fragment the whitepaper presents: its own lake library
# `WhitepaperFragment`, deliberately NOT a default target (`lake build`
# never builds it, so it could rot unseen — exactly the way the
# challenge module did, task #281).  This gate is the one thing that
# builds it, and it holds the library to the tree's own rules:
#
#   * it must build, WARNING-FREE — Lake exits 0 on warnings, so the
#     grep on the log is the gate, as in CI's `lake build` step;
#   * `sorry` is a warning ("declaration uses `sorry`"), so it is caught
#     by the same grep;
#   * its theorems use exactly Lean's three standard axioms —
#     `whitepaper/Fragment/Axioms.lean` pins that with
#     `#guard_msgs in #print axioms` guards, which are build errors when
#     the list changes, and the library's root imports that file.
#
# Needs a toolchain (elan) like every `lake build`; runs from
# `tests/arena.sh` and from CI's ci.yml after the main build.

set -u
cd "$(dirname "$0")/.." || exit 3

log=$(mktemp) || exit 3
trap 'rm -f "$log"' EXIT

if ! timeout 3600 lake build WhitepaperFragment >"$log" 2>&1; then
  cat "$log"
  echo "fragment-gate: FAIL — whitepaper/Fragment does not build" >&2
  exit 1
fi
if grep -n 'warning:' "$log"; then
  echo "fragment-gate: FAIL — whitepaper/Fragment builds with warnings" >&2
  exit 1
fi
echo "fragment-gate: OK — WhitepaperFragment builds warning-free, axioms pinned"
