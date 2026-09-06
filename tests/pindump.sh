#!/usr/bin/env bash
# tests/pindump.sh — THE PIN-DUMP FRESHNESS GATE (task #176).
#
# WHY THIS EXISTS.  The pinned `Nat`-operation declarations and their
# certificate proof blobs used to be computed while
# `Setlec/Kernel/NatOpPins.lean` elaborated, out of an olean loaded BY
# NAME (`Setlec/PinGen/Certs.olean`).  That is not an import edge, Lake
# never ordered the two, and on a cold tree `lake build setlec` failed
# outright.  Per the user's ruling the pins are now a COMMITTED file,
#
#     Setlec/Kernel/NatOpPins/<toolchain>.json
#
# written by the `natop-pins-export` executable, which lives in the
# certificate library's world (its root imports `Setlec.PinGen.Certs`,
# so the proof bodies are visible and Lake orders the build).
#
# A committed generator output needs a staleness ratchet — regenerate,
# `diff -q`, fail loudly.  (The discipline used to be named after
# `annotate-basis`, the offline generator whose `Repr` output was pasted
# into the basis pin modules.  That generator is gone as of 2026-09-06:
# the basis literals are computed by the checker's own annotation pass
# at elaboration time, `#annotate_basis` in Setlec/Kernel/BasisGen.lean,
# so they cannot go stale and need no gate.  This dump still can.)  This
# gate regenerates into a scratch directory under `_tmp/` and diffs.  A
# difference means the dump no longer matches what the certificates,
# `scripts/natop_prefix.json`, `Setlec/PinGen.lean` or the toolchain
# produce; the fix is ALWAYS to regenerate and commit, never to edit the
# json:
#
#     lake exe natop-pins-export
#
# It also checks that the committed dump is named after, and records,
# the toolchain in `lean-toolchain` — a bump must add a dump for the new
# toolchain and re-point the `include_str` in
# `Setlec/Kernel/NatOpPins.lean`.  (The loader independently refuses a
# dump whose `leanVersion` is not the running one, so a forgotten bump
# is a build error, never a silent wrong pin.)
#
# Usage: tests/pindump.sh
set -u
cd "$(dirname "$0")/.."

TC=$(tr -d ' \t\n\r' < lean-toolchain)
# the generator's own sanitisation (Setlec.PinGen.toolchainFileName):
# everything outside [A-Za-z0-9._-] becomes '-'
BASE=$(printf '%s' "$TC" | sed 's/[^A-Za-z0-9._-]/-/g').json
COMMITTED=Setlec/Kernel/NatOpPins/$BASE
SCRATCH=_tmp/pindump-gate

if [ ! -f "$COMMITTED" ]; then
  echo "PINDUMP FAIL — no committed dump for toolchain $TC:"
  echo "    expected $COMMITTED"
  echo "    regenerate with: lake exe natop-pins-export"
  exit 1
fi

if ! grep -q "include_str \"NatOpPins/$BASE\"" Setlec/Kernel/NatOpPins.lean; then
  echo "PINDUMP FAIL — Setlec/Kernel/NatOpPins.lean does not embed $BASE;"
  echo '    a toolchain bump must re-point the include_str at the new dump.'
  exit 1
fi

# The generator is not a default target (`lake build` does not reach
# it), so the tree's warning-free rule is enforced here instead.
BUILDLOG=$(lake build natop-pins-export 2>&1) || {
  echo 'PINDUMP FAIL — the generator did not build:'
  printf '%s\n' "$BUILDLOG" | tail -20
  exit 1
}
if printf '%s\n' "$BUILDLOG" | grep -q 'warning:'; then
  echo 'PINDUMP FAIL — the generator built with warnings:'
  printf '%s\n' "$BUILDLOG" | grep -A3 'warning:' | sed 's/^/    /'
  exit 1
fi

rm -rf "$SCRATCH"
mkdir -p "$SCRATCH"
FRESH=$(lake env ./.lake/build/bin/natop-pins-export "$SCRATCH") || {
  echo 'PINDUMP FAIL — the generator did not run:'
  lake env ./.lake/build/bin/natop-pins-export "$SCRATCH" 2>&1 | tail -20
  exit 1
}

if [ "$FRESH" != "$SCRATCH/$BASE" ]; then
  echo "PINDUMP FAIL — the generator wrote $FRESH, expected $SCRATCH/$BASE"
  echo "    (the toolchain the generator embedded disagrees with lean-toolchain)"
  exit 1
fi

if diff -q "$COMMITTED" "$FRESH" >/dev/null; then
  echo "pindump: $COMMITTED fresh ($(wc -l < "$COMMITTED") lines, toolchain $TC)"
  rm -rf "$SCRATCH"
  exit 0
fi

echo "PINDUMP FAIL — the committed pin dump is STALE:"
echo "    $COMMITTED differs from a fresh regeneration ($FRESH)"
diff "$COMMITTED" "$FRESH" | head -20 | sed 's/^/    /'
echo '    regenerate and commit:  lake exe natop-pins-export'
exit 1
