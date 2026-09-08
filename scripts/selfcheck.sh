#!/usr/bin/env bash
# scripts/selfcheck.sh — THE SELF-CHECK (task #199).
#
# Export con-leche's own Lean development with `lean4export` and run con-leche on
# the result.  The checker whose consistency the tree proves is asked to
# accept the proof that says so.
#
# WHAT IS EXPORTED.  Not "the whole imported environment": `ConLeche` reaches
# `Lean` (through `ConLeche/Kernel/BasisGen.lean`'s elaborator and
# `ConLeche/Frontend/Export.lean`'s JSON reader), and that environment holds
# ~233k constants, the overwhelming majority of them elaborator internals
# no declaration of ours depends on.  What is exported is **every
# non-internal constant declared by a con-leche module, plus its transitive
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
#   * `ConLeche.Challenge` — the Palomar challenge statement is a deliberate
#     `sorry` (see `tests/trust-surface.sh`).  It roots its own library,
#     is in no default target, has no `.olean` in a normal build, and
#     nothing imports it, so it cannot enter the cone.
#   * `ConLecheTests` — fixtures, not the development.
#   * `unsafe` declarations.  `lean4export` skips them unless
#     `--export-unsafe` is given, and skips them even when they are
#     reached as dependencies.  This is SAFE here and it was checked:
#     the only `isUnsafe` constants in the cone are `ConLeche.Expr.beqB`,
#     `ConLeche.Expr.beqFast`, `ConLeche.Expr.beqGo` (the `@[implemented_by]`
#     pointer-equality fast path, `ConLeche/Kernel/Expr.lean`) and
#     `ptrAddrUnsafe` itself, and **no safe constant in the cone refers
#     to any of them** — an `@[implemented_by]` attribute is not part of
#     the kernel declaration, so `ConLeche.Expr.beq` exports as the ordinary
#     definition it is.  The stream therefore has no dangling reference.
#     `ConLeche/Kernel/Expr.lean`'s `@[computed_field]` words are likewise
#     invisible to the kernel and so to the export.
#   * `partial def` bodies.  Each `partial def f` is two declarations:
#     the internal `f._unsafe_rec` (`unsafe`, skipped as above) and `f`
#     itself, an `opaque` constant.  The opaques ARE exported — 252 of
#     them — and con-leche installs opaques as non-unfoldable constants
#     (task #95).  There are no `.partial`-safety definitions in the
#     cone at all.
#
# USAGE
#     scripts/selfcheck.sh [--trusted] [OUTDIR]
#
#   OUTDIR defaults to `_tmp/selfcheck`.  Steps are skipped when their
#   output is already there, so a re-run only redoes the check:
#     $OUTDIR/lean4export/   the exporter, built at THIS tree's toolchain
#     $OUTDIR/con-leche-decls.txt the root declaration list
#     $OUTDIR/con-leche-export.ndjson  the export
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
OUTDIR=_tmp/selfcheck
for a in "$@"; do
  case "$a" in
    --trusted)  MODE=--trusted ;;
    --verified) MODE=--verified ;;
    -*) echo "usage: scripts/selfcheck.sh [--trusted] [OUTDIR]" >&2; exit 3 ;;
    *)  OUTDIR=$a ;;
  esac
done
mkdir -p "$OUTDIR"
OUTDIR=$(cd "$OUTDIR" && pwd)

TOOLCHAIN=$(cat lean-toolchain)
# The library roots (the lakefile's `defaultTargets` plus the certificate
# library and the `con-leche` executable's root).  `ConLeche.Challenge` and the
# test library are deliberately absent; see the header.
ROOTS=(ConLeche ConLeche.Term ConLeche.SetModel ConLeche.Semantics ConLeche.Model
       ConLeche.Verify.Cached ConLeche.MainTheorem ConLeche.PinGen.Certs Main)

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
if [ ! -s "$OUTDIR/con-leche-decls.txt" ]; then
  echo "[selfcheck] collecting the root declaration list"
  lake env lean --run scripts/SelfcheckDecls.lean "${ROOTS[@]}" \
    > "$OUTDIR/con-leche-decls.txt"
fi
echo "[selfcheck] $(wc -l < "$OUTDIR/con-leche-decls.txt") root declarations"

# ---------------------------------------------------------------- 3/4
# The exporter is cheap (2.4 GB peak RSS, ~25 s at task #199) — it is the
# CHECK that is Mathlib-scale, not this.
if [ ! -s "$OUTDIR/con-leche-export.ndjson" ]; then
  echo "[selfcheck] exporting"
  ( ulimit -v 22000000
    timeout 3600 lake env "$L4E/.lake/build/bin/lean4export" "${ROOTS[@]}" \
      -- $(cat "$OUTDIR/con-leche-decls.txt") > "$OUTDIR/con-leche-export.ndjson" )
fi
echo "[selfcheck] export: $(du -h "$OUTDIR/con-leche-export.ndjson" | cut -f1), \
$(wc -l < "$OUTDIR/con-leche-export.ndjson") lines"

# ---------------------------------------------------------------- 4/4
lake build con-leche
echo "[selfcheck] checking ($MODE)"
# `CON_LECHE_PROGRESS` is deliberately NOT set by default: the heartbeat lane
# is the driver's one unverified fold (Main.lean, user ruling
# 2026-09-07), so a run with it set does not stand behind the verified
# capstone.  Set it in the environment for a diagnostic run.
(
  ulimit -v 22000000
  set +e
  timeout 4h ./.lake/build/bin/con-leche "$MODE" \
    "$OUTDIR/con-leche-export.ndjson" \
    2> >(while IFS= read -r l; do printf '%s %s\n' "$(date +%H:%M:%S)" "$l"; done \
          | tee "$OUTDIR/check.log" >&2)
  echo "[selfcheck] exit $?"
)
