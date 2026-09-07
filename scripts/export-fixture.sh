#!/usr/bin/env bash
# scripts/export-fixture.sh — regenerate an e2e fixture stream from its
# `.lean` source (task #219).
#
#   scripts/export-fixture.sh                     # every tests/e2e/src/*.lean
#   scripts/export-fixture.sh direct_nested_dep   # just these
#
# `tests/e2e/src/<name>.lean` becomes `tests/e2e/<name>.ndjson`: RAW
# `lean4export` output and nothing else.  Until task #207 the recipe
# lived in lean-inductive-models (`scripts/export-fixture.sh`, with a
# model-splicing filter after the export); the tool is gone, the filter
# with it, and since task #219 a `_model` record in a stream is an
# ordinary declaration with no effect on any inductive block — the
# models are generated in process, by `ConLeche/Frontend/InModel/*`.
#
# The toolchain is PINNED where the arena corpus was built — Lean
# v4.29.1 and `lean4export` at `caccfbe` — so a fixture regenerated
# here and a corpus fixture differ in their content and in nothing
# else.  `LEAN4EXPORT_DIR` reuses an existing clone (default
# `_tmp/lean4export`, which the reference checkouts already provide).
#
# Sources are `prelude` modules (no imports), so the export is small;
# a source may list the declarations to export on a line
#
#     --#export Name1 Name2 ...
#
# which becomes lean4export's `--` filter (transitive dependencies are
# pulled in automatically).  A source needing other exporter flags
# carries the recipe in its own header and is NOT regenerated here.
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
SRC="$ROOT/tests/e2e/src"
OUT="${OUT_DIR:-$ROOT/tests/e2e}"
TOOLCHAIN="leanprover/lean4:v4.29.1"
EXPORT_DIR="${LEAN4EXPORT_DIR:-$ROOT/_tmp/lean4export}"

command -v elan >/dev/null || { echo "elan is not on PATH" >&2; exit 2; }
BIN="$EXPORT_DIR/.lake/build/bin/lean4export"
[ -x "$BIN" ] || { echo "no lean4export at $BIN (set LEAN4EXPORT_DIR)" >&2; exit 2; }
EXPORT_LEAN_PATH="$(cd "$EXPORT_DIR" && lake env printenv LEAN_PATH)"

declare -a SOURCES=()
if (($#)); then
  for a in "$@"; do SOURCES+=("$SRC/$(basename "${a%.lean}").lean"); done
else
  while IFS= read -r f; do SOURCES+=("$f"); done < <(find "$SRC" -name '*.lean' | sort)
fi

WORK="$(mktemp -d)"
trap 'rm -rf "$WORK"' EXIT

for src in "${SOURCES[@]}"; do
  base="$(basename "$src" .lean)"
  # lean4export takes a MODULE name, so the source is compiled under a
  # capitalised, identifier-shaped module name in a scratch directory.
  mod="$(printf '%s' "$base" | sed -E 's/(^|_)([a-z])/\U\2/g')"
  cp "$src" "$WORK/$mod.lean"
  ( cd "$WORK" && elan run "$TOOLCHAIN" lean -o "$mod.olean" "$mod.lean" )
  declare -a ONLY=()
  while IFS= read -r name; do ONLY+=("$name"); done \
    < <(sed -n 's/^--#export  *//p' "$src" | tr ' ' '\n' | grep -v '^$')
  if ((${#ONLY[@]})); then
    LEAN_PATH="$WORK:$EXPORT_LEAN_PATH" "$BIN" "$mod" -- "${ONLY[@]}" > "$OUT/$base.ndjson"
  else
    LEAN_PATH="$WORK:$EXPORT_LEAN_PATH" "$BIN" "$mod" > "$OUT/$base.ndjson"
  fi
  unset ONLY
  echo "$base.ndjson: $(wc -l < "$OUT/$base.ndjson") lines" >&2
done
