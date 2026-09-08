#!/usr/bin/env bash
# scripts/shake-setup.sh — build the import minimizer for THIS tree (task #223).
#
# `shake` was upstreamed from Mathlib into Lake (mathlib4#27632, 2025-07-29);
# our toolchain ships it as `lake shake`, sources at
#   $(lean --print-prefix)/src/lean/lake/Lake/CLI/Shake.lean
# but `Lake.Shake.run` REFUSES a tree that contains a classic (non-`module`)
# file — and 529 of our 547 `.lean` files are classic.  So this script vendors
# that one file into a scratch Lake project under `_tmp/shake-tool/`
# (gitignored; NOTHING is added to this package's manifest) and applies three
# patches, each of which is about classic files only:
#
#   1. drop the `only works with `module`s currently` guard.  A classic file
#      records every import as `isExported := true, importAll := false` —
#      exactly `public import`, which IS classic re-export semantics — so the
#      analysis core needs no change.
#   2. `decodeImport` must read a classic file's `import X` as exported.
#      Upstream keys it off the `public` token, which a classic header cannot
#      carry, so the decoded `Import` never matches the one in the olean and
#      `--fix`/`--explain` silently do nothing on classic files.
#   3. the `--fix` writer must spell an ADDED import in the file's own
#      dialect: `import X`, not `public import X`, in a classic file.
#
# Usage:
#     scripts/shake-setup.sh          # builds _tmp/shake-tool/.lake/build/bin/shaketool
# then, from the worktree root, after a full `lake build`:
#     SHAKE_SRC=.:tests LEAN_PATH=.lake/build/lib/lean \
#       _tmp/shake-tool/.lake/build/bin/shaketool --keep-implied \
#       ConLeche.MainTheorem ConLeche.Verify.Cached ConLeche.Model \
#       ConLeche.Semantics ConLeche.SetModel ConLeche.Term ConLeche \
#       ConLeche.PinGen.Certs Main
# (`PinDump` must be a separate run: it and `Main` both define `main`.)
# See DESIGN.md task #223 for the noise floor this run has and why.
set -euo pipefail
root="$(cd "$(dirname "$0")/.." && pwd)"
dir="$root/_tmp/shake-tool"
src="$(lean --print-prefix)/src/lean/lake/Lake/CLI/Shake.lean"
mkdir -p "$dir"
cp "$root/lean-toolchain" "$dir/"
cp "$src" "$dir/Shake.lean"

python3 - "$dir/Shake.lean" <<'PY'
import sys
p = sys.argv[1]; s = open(p).read()

g = """  if env.header.moduleData.any (!·.isModule) then
    throw <| .userError "`lake shake` only works with `module`s currently"
"""
assert g in s, "patch 1: guard not found (toolchain drift?)"
s = s.replace(g, "  -- PATCH 1 (con-leche #223): upstream's `module`-only guard dropped.\n")

d = """def decodeImport : TSyntax ``Parser.Module.import → Import
  | `(Parser.Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    { module := id.getId, isExported := pubTk?.isSome, isMeta := metaTk?.isSome, importAll := allTk?.isSome }
  | stx => panic! s!"unexpected syntax {stx}\""""
assert d in s, "patch 2: decodeImport not found (toolchain drift?)"
s = s.replace(d, """-- PATCH 2 (con-leche #223): a classic file has no `public` token, yet its
-- olean records the import as exported.
def decodeImport (isModuleFile : Bool) : TSyntax ``Parser.Module.import → Import
  | `(Parser.Module.import| $[public%$pubTk?]? $[meta%$metaTk?]? import $[all%$allTk?]? $id) =>
    { module := id.getId, isExported := pubTk?.isSome || !isModuleFile,
      isMeta := metaTk?.isSome, importAll := allTk?.isSome }
  | stx => panic! s!"unexpected syntax {stx}\"""")

s = s.replace("""  for impStx in imports do
    let imp := decodeImport impStx""",
              """  for impStx in imports do
    let imp := decodeImport module?.isSome impStx""", 1)
s = s.replace("""      let (_, _, imports) := decodeHeader stx
      for stx in imports do
        if toRemove.any fun imp => imp == decodeImport stx then""",
              """      let (module?, _, imports) := decodeHeader stx
      for stx in imports do
        if toRemove.any fun imp => imp == decodeImport module?.isSome stx then""", 1)
s = s.replace("""    let (_, _, imports) := decodeHeader stx
    let text := inputCtx.fileMap.source""",
              """    let (module?, _, imports) := decodeHeader stx
    let text := inputCtx.fileMap.source""", 1)
s = s.replace("""      let mod := decodeImport stx""",
              """      let mod := decodeImport module?.isSome stx""", 1)

a = """    for mod in add do
      if !seen.contains mod then
        seen := seen.insert mod
        out := out ++ s!"{mod}\\n\""""
assert a in s, "patch 3: fix writer not found (toolchain drift?)"
s = s.replace(a, """    for mod in add do
      if !seen.contains mod then
        seen := seen.insert mod
        -- PATCH 3 (con-leche #223): a classic file has no `public import` syntax.
        out := out ++ (if module?.isSome then s!"{mod}\\n" else s!"import {mod.module}\\n")""", 1)

s = s.replace("\nprelude\n", "\n\n", 1)   # the vendored copy is not part of Init
open(p, "w").write(s)
print("Shake.lean vendored and patched")
PY

cat > "$dir/lakefile.toml" <<'EOF'
name = "shaketool"
defaultTargets = ["shaketool"]

[[lean_lib]]
name = "Shake"

[[lean_exe]]
name = "shaketool"
root = "Tool"
EOF

cat > "$dir/Tool.lean" <<'EOF'
module
import Shake
import Lean.Util.Path
open Lean
/-- A driver for the vendored `Lake.Shake.run`.  Source roots come from
`SHAKE_SRC` (colon-separated), oleans from `LEAN_PATH`. -/
public def main (args : List String) : IO UInt32 := do
  initSearchPath (← findSysroot)
  let mut a : Lake.Shake.Args := {}
  let mut mods := #[]
  let mut only := #[]
  let mut nextOnly := false
  for s in args do
    if nextOnly then only := only.push s.toName; nextOnly := false
    else if s == "--explain" then a := { a with explain := true }
    else if s == "--trace" then a := { a with trace := true }
    else if s == "--fix" then a := { a with fix := true }
    else if s == "--keep-implied" then a := { a with keepImplied := true }
    else if s == "--keep-prefix" then a := { a with keepPrefix := true }
    else if s == "--only" then nextOnly := true
    else mods := mods.push s.toName
  a := { a with mods := mods, onlyMods := only }
  let sp : SearchPath := ((← IO.getEnv "SHAKE_SRC").getD ".").splitOn ":" |>.map (⟨·⟩)
  Lake.Shake.run a sp
EOF

cd "$dir" && lake build
echo "built: $dir/.lake/build/bin/shaketool"
