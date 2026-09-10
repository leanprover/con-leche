#!/usr/bin/env bash
# tests/pindump.sh — THE PIN-DUMP FRESHNESS GATE (task #176).
#
# WHY THIS EXISTS.  The pinned `Nat`-operation declarations and their
# certificate proof blobs used to be computed while
# `ConLeche/Kernel/NatOpPins.lean` elaborated, out of an olean loaded BY
# NAME (`ConLeche/PinGen/Certs.olean`).  That is not an import edge, Lake
# never ordered the two, and on a cold tree `lake build con-leche` failed
# outright.  Per the user's ruling the pins are now a COMMITTED file,
#
#     pins/<toolchain>.json
#
# written by the `natop-pins-export` executable, which lives in the
# certificate library's world (its root imports `ConLeche.PinGen.Certs`,
# so the proof bodies are visible and Lake orders the build).
#
# A committed generator output needs a staleness ratchet — regenerate,
# `diff -q`, fail loudly.  (The discipline used to be named after
# `annotate-basis`, the offline generator whose `Repr` output was pasted
# into the basis pin modules.  That generator is gone as of 2026-09-06:
# the basis literals are computed by the checker's own annotation pass
# at elaboration time, `#annotate_basis` in ConLeche/Kernel/BasisGen.lean,
# so they cannot go stale and need no gate.  This dump still can.)  This
# gate regenerates into a scratch directory under `_tmp/` and diffs.  A
# difference means the dump no longer matches what the certificates,
# `scripts/natop_prefix.json`, `ConLeche/PinGen.lean` or the toolchain
# produce; the fix is ALWAYS to regenerate and commit, never to edit the
# json:
#
#     lake exe natop-pins-export
#
# It also checks that the committed dump is named after, and records,
# the toolchain in `lean-toolchain` — a bump must add a dump for the new
# toolchain and list it in `ConLeche/Kernel/NatOpPins.lean`.
#
# PIN VARIANTS (task #273).  `pins/` holds one dump PER SUPPORTED
# TOOLCHAIN and `ConLeche/Kernel/NatOpPins.lean` embeds ALL of them (the
# install gate tries them in that order).  Only the CURRENT toolchain's
# dump can be regenerated here — a dump is computed by the generator
# running ON its toolchain — so this gate regenerates and diffs that
# one, and for the others checks only that every committed `pins/*.json`
# is embedded and every embedded dump is committed.  The other dumps
# are exercised by the cross-toolchain matrix lane (`scripts/
# natop-matrix.sh`, task #274): a toolchain whose export declines
# there is the signal that a new dump is needed; the recipe is in
# `pins/README.md`.  (The loader accepts dumps from any Lean version
# since #273 — a binary built on one toolchain carries several
# toolchains' pins — so a forgotten regeneration after a bump is
# caught HERE, in the standard battery, not at build time.)
#
# Usage: tests/pindump.sh
set -u
cd "$(dirname "$0")/.."

TC=$(tr -d ' \t\n\r' < lean-toolchain)
# the generator's own sanitisation (ConLeche.PinGen.toolchainFileName):
# everything outside [A-Za-z0-9._-] becomes '-'
BASE=$(printf '%s' "$TC" | sed 's/[^A-Za-z0-9._-]/-/g').json
COMMITTED=pins/$BASE
# the built-in prelude (task #191): the sidecar the same generator
# writes, embedded by ConLeche/Frontend/Prelude.lean
PBASE=${BASE%.json}.prelude.ndjson
PCOMMITTED=pins/$PBASE
SCRATCH=_tmp/pindump-gate

if [ ! -f "$COMMITTED" ]; then
  echo "PINDUMP FAIL — no committed dump for toolchain $TC:"
  echo "    expected $COMMITTED"
  echo "    regenerate with: lake exe natop-pins-export"
  exit 1
fi

if ! grep -q "include_str \"../../pins/$BASE\"" ConLeche/Kernel/NatOpPins.lean; then
  echo "PINDUMP FAIL — ConLeche/Kernel/NatOpPins.lean does not embed $BASE;"
  echo '    a toolchain bump must list the new dump in its #load_natop_pins.'
  exit 1
fi

# every committed dump is embedded, every embedded dump is committed
for f in pins/*.json; do
  b=$(basename "$f")
  if ! grep -q "include_str \"../../pins/$b\"" ConLeche/Kernel/NatOpPins.lean; then
    echo "PINDUMP FAIL — committed dump $f is not embedded by ConLeche/Kernel/NatOpPins.lean"
    exit 1
  fi
done
for b in $(grep -o 'include_str "../../pins/[^"]*\.json"' ConLeche/Kernel/NatOpPins.lean | sed 's#.*/pins/##; s/"$//'); do
  if [ ! -f "pins/$b" ]; then
    echo "PINDUMP FAIL — ConLeche/Kernel/NatOpPins.lean embeds pins/$b, which is not committed"
    exit 1
  fi
done

if [ ! -f "$PCOMMITTED" ]; then
  echo "PINDUMP FAIL — no committed built-in prelude for toolchain $TC:"
  echo "    expected $PCOMMITTED"
  echo "    regenerate with: lake exe natop-pins-export"
  exit 1
fi

if ! grep -q "include_str \"../../pins/$PBASE\"" ConLeche/Frontend/Prelude.lean; then
  echo "PINDUMP FAIL — ConLeche/Frontend/Prelude.lean does not embed $PBASE;"
  echo '    a toolchain bump must re-point the include_str at the new prelude.'
  exit 1
fi

if ! grep -q "\"preludeFile\":\"$PBASE\"" "$COMMITTED"; then
  echo "PINDUMP FAIL — $COMMITTED does not name $PBASE as its prelude"
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
# the generator prints two paths: the dump, then the prelude
FRESHOUT=$(lake env ./.lake/build/bin/natop-pins-export "$SCRATCH") || {
  echo 'PINDUMP FAIL — the generator did not run:'
  lake env ./.lake/build/bin/natop-pins-export "$SCRATCH" 2>&1 | tail -20
  exit 1
}
FRESH=$(printf '%s\n' "$FRESHOUT" | sed -n 1p)
PFRESH=$(printf '%s\n' "$FRESHOUT" | sed -n 2p)

if [ "$FRESH" != "$SCRATCH/$BASE" ] || [ "$PFRESH" != "$SCRATCH/$PBASE" ]; then
  echo "PINDUMP FAIL — the generator wrote $FRESH and $PFRESH,"
  echo "    expected $SCRATCH/$BASE and $SCRATCH/$PBASE"
  echo "    (the toolchain the generator embedded disagrees with lean-toolchain)"
  exit 1
fi

stale=0
if ! diff -q "$COMMITTED" "$FRESH" >/dev/null; then
  echo "PINDUMP FAIL — the committed pin dump is STALE:"
  echo "    $COMMITTED differs from a fresh regeneration ($FRESH)"
  diff "$COMMITTED" "$FRESH" | head -20 | sed 's/^/    /'
  stale=1
fi
if ! diff -q "$PCOMMITTED" "$PFRESH" >/dev/null; then
  echo "PINDUMP FAIL — the committed built-in prelude is STALE:"
  echo "    $PCOMMITTED differs from a fresh regeneration ($PFRESH)"
  diff "$PCOMMITTED" "$PFRESH" | head -20 | sed 's/^/    /'
  stale=1
fi
if [ "$stale" = 1 ]; then
  echo '    regenerate and commit:  lake exe natop-pins-export'
  exit 1
fi

echo "pindump: $COMMITTED fresh ($(wc -l < "$COMMITTED") lines, toolchain $TC)"
echo "pindump: $(ls pins/*.json | wc -l) dump(s) embedded: $(ls pins/*.json | xargs -n1 basename | tr '\n' ' ')"
echo "pindump: $PCOMMITTED fresh ($(wc -l < "$PCOMMITTED") lines, $(grep -c '"inductive"\|"quot"\|"axiom"\|"def"\|"thm"\|"opaque"' "$PCOMMITTED") declaration records)"
rm -rf "$SCRATCH"
exit 0
