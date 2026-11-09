#!/usr/bin/env bash
# tests/plain-reach.sh — THE PLAIN-TIER REACH GATE (task #497).
#
# The plain tier (`ConLeche/Kernel/*` and every other module of ours outside
# `ConLeche/Cached/*`, `ConLeche/Driver/*` and `Main`) is the specification the
# proofs are about.  The binary may run a plain definition only where it is the
# best code there is; everywhere else the cached tier has a twin.  This gate
# walks the compiled IR from `main` (`scripts/executed-decls.lean --edges`, so
# `@[csimp]`, `@[implemented_by]` and specializations are resolved as the binary
# links them) and checks every reached plain declaration against
# `tests/plain-reach-allow.txt`, which says why each may run.  A new reach fails
# the gate, and so does an allowlisted name nothing reaches any more (remove it).
#
# Needs the built tree (`lake build`); about a minute, most of it the import of
# `Main`'s environment.
set -euo pipefail
cd "$(dirname "$0")/.."
exec python3 scripts/plain-reach.py --allow tests/plain-reach-allow.txt
