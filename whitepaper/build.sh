#!/usr/bin/env bash
# whitepaper/build.sh — render the whitepaper (task #323).
#
# ONE source (main.typ + sections/*.typ + lib.typ + style.css), TWO
# renderings by the same typst, both with `--features html` so that
# lib.typ's `target()` branches are reachable in either:
#
#   _build/whitepaper.pdf   paged, embedded fonts only (reproducible)
#   _build/index.html       self-contained (inline CSS, MathML, SVG)
#
# then synced to <repo root>/_out/whitepaper/ (gitignored) so the
# maintainer can read it.  Runnable as
#   nix develop ./whitepaper -c whitepaper/build.sh     (from the root)
#   ./build.sh                                          (in the dev shell)
#
# EXIT NON-ZERO ON ANY WARNING.  typst exits 0 on warnings; this script
# keeps its stderr, drops the one warning that is not about our
# document (the "html export is under active development" banner and
# its hint lines) and fails if anything remains.
set -u
here=$(cd "$(dirname "$0")" && pwd)
root=$(cd "$here/.." && pwd)
cd "$here" || exit 3

command -v typst >/dev/null || { echo "build.sh: typst not found (run inside \`nix develop ./whitepaper\`)" >&2; exit 3; }

mkdir -p _build
fail=0

render() {  # render <format> <output>
  local fmt=$1 out=$2 log=_build/typst-$1.log
  typst compile --features html --format "$fmt" --ignore-system-fonts \
    --root "$root" main.typ "$out" 2> "$log"
  local rc=$?
  # Drop the export banner: the `warning:` line and its ` = hint:` lines.
  local rest
  rest=$(awk '
    /^warning: html export is under active development/ { skip=1; next }
    skip && /^ *= hint:/ { next }
    { skip=0 } NF { print }' "$log")
  if [ $rc -ne 0 ] || [ -n "$rest" ]; then
    echo "build.sh: typst ($fmt) exit $rc, diagnostics:" >&2
    printf '%s\n' "$rest" >&2
    fail=1
  else
    echo "build.sh: $out"
  fi
}

render pdf  _build/whitepaper.pdf
render html _build/index.html

if [ $fail -ne 0 ]; then
  echo "build.sh: FAIL" >&2
  exit 1
fi

outdir=$root/_out/whitepaper
mkdir -p "$outdir"
cp -f _build/whitepaper.pdf _build/index.html "$outdir/"
echo "build.sh: synced to $outdir"
