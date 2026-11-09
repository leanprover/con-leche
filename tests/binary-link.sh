#!/usr/bin/env bash
# tests/binary-link.sh — THE BINARY LINK GATE (task #498 L3).
#
# The shipped binary links every module `main` imports, proof modules included
# (`Driver/*` may import `Verify/*`).  A proof module that reaches the core's
# simulation modules (`Verify/Cached/DiscC*`, `Grind`, `GrindAttr`) brings
# `Lean.Meta` along, whose module initialisers then run at every start: once
# measured at 19 -> 135 MB of binary and +110..160 M instructions per run.  The
# checker itself needs no part of the `Lean` package, so the gate fails if the
# built binary carries any `initialize_Lean…` symbol.  Needs the built tree
# (`lake build`); seconds.
set -euo pipefail
cd "$(dirname "$0")/.."
BIN=.lake/build/bin/con-leche
if [ ! -x "$BIN" ]; then
  echo "binary-link: $BIN missing (run lake build)" >&2
  exit 1
fi
n=$(nm "$BIN" | awk '$3 ~ /^initialize_Lean/' | wc -l)
if [ "$n" -ne 0 ]; then
  echo "binary-link: FAIL: the binary links $n Lean package module initialisers, e.g.:" >&2
  nm "$BIN" | awk '$3 ~ /^initialize_Lean/ {print "  " $3}' | head -5 >&2
  echo "binary-link: a module the driver imports pulls in Lean.Meta (look for an import of Verify/Cached/DiscC*, Grind or GrindAttr)" >&2
  exit 1
fi
echo "binary-link: no Lean package module linked ($(du -h "$BIN" | cut -f1) binary)"
