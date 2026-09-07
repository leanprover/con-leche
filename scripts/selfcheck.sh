#!/usr/bin/env bash
# scripts/selfcheck.sh — THE SELF-CHECK (task #199).
#
# Export lech's own Lean development with `lean4export` and run lech on
# the result.  The checker whose consistency the tree proves is asked to
# accept the proof that says so.
#
# WHAT IS EXPORTED.  Not "the whole imported environment": `Lech` reaches
# `Lean` (through `Lech/Kernel/BasisGen.lean`'s elaborator and
# `Lech/Frontend/Export.lean`'s JSON reader), and that environment holds
# ~233k constants, the overwhelming majority of them elaborator internals
# no declaration of ours depends on.  What is exported is **every
# non-internal constant declared by a lech module, plus its transitive
# dependency cone** — `scripts/SelfcheckDecls.lean` prints the root list,
# `lean4export` walks the cone.  On master `2d36855d` (task #199) that
# is 15,738 roots and 34,417 exported declarations (17,062 theorems,
# 16,315 definitions, 781 inductive blocks, 252 opaques, 4 quotient
# constants, and exactly the 3 standard axioms `propext`, `Quot.sound`,
# `Classical.choice`), 533 MB / 9.64M NDJSON lines.
#
# THE VERDICT at that tree, both modes: **exit 0, 37,198 declarations
# accepted**, ~3.5 min, 1.5 GB peak RSS, ~1.5 T instructions:u — no
# declines, no rejections, no internal errors.  See DESIGN.md
# "TASK #199 — THE SELF-CHECK".
#
# WHAT IS NOT EXPORTED, and why.
#
#   * `Lech.Challenge` — the Palomar challenge statement is a deliberate
#     `sorry` (see `tests/trust-surface.sh`).  It roots its own library,
#     is in no default target, has no `.olean` in a normal build, and
#     nothing imports it, so it cannot enter the cone.
#   * `LechPreprocess` — the `lech-preprocess` executable is a five-line
#     front end for the external `lean-inductive-models` tool.  Its cone
#     is that tool plus the whole Lean elaborator, i.e. someone else's
#     code; nothing in `Lech.*` imports it (that is the point of the
#     lakefile's note on the dependency).
#   * `LechTests` — fixtures, not the development.
#   * `unsafe` declarations.  `lean4export` skips them unless
#     `--export-unsafe` is given, and skips them even when they are
#     reached as dependencies.  This is SAFE here and it was checked:
#     the only `isUnsafe` constants in the cone are `Lech.Expr.beqB`,
#     `Lech.Expr.beqFast`, `Lech.Expr.beqGo` (the `@[implemented_by]`
#     pointer-equality fast path, `Lech/Kernel/Expr.lean`) and
#     `ptrAddrUnsafe` itself, and **no safe constant in the cone refers
#     to any of them** — an `@[implemented_by]` attribute is not part of
#     the kernel declaration, so `Lech.Expr.beq` exports as the ordinary
#     definition it is.  The stream therefore has no dangling reference.
#     `Lech/Kernel/Expr.lean`'s `@[computed_field]` words are likewise
#     invisible to the kernel and so to the export.
#   * `partial def` bodies.  Each `partial def f` is two declarations:
#     the internal `f._unsafe_rec` (`unsafe`, skipped as above) and `f`
#     itself, an `opaque` constant.  The opaques ARE exported — 252 of
#     them — and lech installs opaques as non-unfoldable constants
#     (task #95).  There are no `.partial`-safety definitions in the
#     cone at all.
#
# USAGE
#     scripts/selfcheck.sh [--trusted] [--pre] [OUTDIR]
#
#   OUTDIR defaults to `_tmp/selfcheck`.  Steps are skipped when their
#   output is already there, so a re-run only redoes the check:
#     $OUTDIR/lean4export/   the exporter, built at THIS tree's toolchain
#     $OUTDIR/lech-decls.txt the root declaration list
#     $OUTDIR/lech-export.ndjson  the export
#     $OUTDIR/check.log      the checker's stderr, timestamped
#
# THE EXPORTER RECIPE.  `lean4export`'s output format tracks the Lean
# version, so it must be built at the *same* toolchain as the tree.  The
# upstream repo carries one `chore: bump toolchain to vX` commit per
# release; this script finds the one whose `lean-toolchain` equals ours
# and builds that.  (`_tmp/lean4export` in a dev checkout is a v4.29.1
# build and is NOT usable here.)
set -euo pipefail
cd "$(dirname "$0")/.."
ROOT=$PWD

MODE=--verified
PRE=()
OUTDIR=_tmp/selfcheck
for a in "$@"; do
  case "$a" in
    --trusted)  MODE=--trusted ;;
    --verified) MODE=--verified ;;
    --pre)      PRE=(--pre) ;;
    -*) echo "usage: scripts/selfcheck.sh [--trusted] [--pre] [OUTDIR]" >&2; exit 3 ;;
    *)  OUTDIR=$a ;;
  esac
done
mkdir -p "$OUTDIR"
OUTDIR=$(cd "$OUTDIR" && pwd)

TOOLCHAIN=$(cat lean-toolchain)
# The library roots (the lakefile's `defaultTargets` plus the certificate
# library and the `lech` executable's root).  `Lech.Challenge` and the
# test library are deliberately absent; see the header.
ROOTS=(Lech Lech.TT Lech.SetModel Lech.Semantics Lech.SetP
       Lech.Verify.Cached Lech.MainTheorem Lech.PinGen.Certs Main)

# ---------------------------------------------------------------- 1/4
L4E=$OUTDIR/lean4export
if [ ! -x "$L4E/.lake/build/bin/lean4export" ]; then
  echo "[selfcheck] building lean4export for $TOOLCHAIN"
  rm -rf "$L4E"
  git clone -q https://github.com/leanprover/lean4export "$L4E"
  ( cd "$L4E"
    # the newest commit whose lean-toolchain is ours
    for c in $(git log --format=%H -- lean-toolchain); do
      if [ "$(git show "$c:lean-toolchain")" = "$TOOLCHAIN" ]; then
        git checkout -q "$c"; break
      fi
    done
    [ "$(cat lean-toolchain)" = "$TOOLCHAIN" ] || {
      echo "[selfcheck] no lean4export commit for $TOOLCHAIN" >&2; exit 3; }
    lake build )
fi

# ---------------------------------------------------------------- 2/4
if [ ! -s "$OUTDIR/lech-decls.txt" ]; then
  echo "[selfcheck] collecting the root declaration list"
  lake env lean --run scripts/SelfcheckDecls.lean "${ROOTS[@]}" \
    > "$OUTDIR/lech-decls.txt"
fi
echo "[selfcheck] $(wc -l < "$OUTDIR/lech-decls.txt") root declarations"

# ---------------------------------------------------------------- 3/4
# The exporter is cheap (2.4 GB peak RSS, ~25 s at task #199) — it is the
# CHECK that is Mathlib-scale, not this.
if [ ! -s "$OUTDIR/lech-export.ndjson" ]; then
  echo "[selfcheck] exporting"
  ( ulimit -v 22000000
    timeout 3600 lake env "$L4E/.lake/build/bin/lean4export" "${ROOTS[@]}" \
      -- $(cat "$OUTDIR/lech-decls.txt") > "$OUTDIR/lech-export.ndjson" )
fi
echo "[selfcheck] export: $(du -h "$OUTDIR/lech-export.ndjson" | cut -f1), \
$(wc -l < "$OUTDIR/lech-export.ndjson") lines"

# ---------------------------------------------------------------- 4/4
lake build lech lech-preprocess
echo "[selfcheck] checking ($MODE)"
# `LECH_PROGRESS` is deliberately NOT set by default: the heartbeat lane
# is the driver's one unverified fold (Main.lean, user ruling
# 2026-09-07), so a run with it set does not stand behind the verified
# capstone.  Set it in the environment for a diagnostic run.
(
  ulimit -v 22000000
  set +e
  timeout 4h ./.lake/build/bin/lech "$MODE" "${PRE[@]+"${PRE[@]}"}" \
    "$OUTDIR/lech-export.ndjson" \
    2> >(while IFS= read -r l; do printf '%s %s\n' "$(date +%H:%M:%S)" "$l"; done \
          | tee "$OUTDIR/check.log" >&2)
  echo "[selfcheck] exit $?"
)
