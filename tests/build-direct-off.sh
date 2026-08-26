#!/usr/bin/env bash
# Build a second `setlec` binary with the direct simple-structure master
# switch flipped off, i.e. with
#
#     Setlec.directStructsEnabled : Bool := false
#
# (`Setlec/Kernel/Direct.lean`, task #119) instead of the shipped `true`.
# The switch is a compile-time constant, so the only way to exercise the
# switched-off configuration is a second build; this script produces it
# *without* mutating the source tree, so nobody has to hand-edit
# `Direct.lean` and forget to put it back.
#
# Mechanics: the tracked sources (minus `tests/`, which this build does
# not need — only the executable is built, and the harness feeds it
# fixtures from the main tree) are mirrored into `_tmp/direct-off/`
# (gitignored), the one flag line is rewritten there, and `lake build
# setlec` runs in that copy.  The copy gets its own `.lake`, seeded once
# from the main tree's so that only `Direct.lean`'s cone is rebuilt.
#
# Prints the path of the resulting binary on stdout; all build chatter
# goes to stderr.  Used by `tests/arena.sh --direct-off`.
set -eu
cd "$(dirname "$0")/.."
SRC=$PWD
OUT=$SRC/_tmp/direct-off
FLAGFILE=Setlec/Kernel/Direct.lean

mkdir -p "$OUT"

# 1. mirror the tracked sources
git -C "$SRC" ls-files -z ':!:tests/**' |
  rsync -a --files-from=- --from0 "$SRC/" "$OUT/" >&2

# 2. seed the build cache once (a cold `lake build` here would repeat the
#    whole ~245-job build; with the main tree's oleans in place only the
#    switched module and its dependents are rebuilt)
mkdir -p "$OUT/.lake"
for d in packages build; do
  if [ ! -e "$OUT/.lake/$d" ] && [ -e "$SRC/.lake/$d" ]; then
    cp -a "$SRC/.lake/$d" "$OUT/.lake/$d"
  fi
done

# 3. flip the switch in the copy.
#
#    THE GUARD BELOW IS LOAD-BEARING — do not "simplify" it into a bare
#    `sed`.  A `sed` that matches nothing exits 0 and leaves the copy
#    with the shipped `:= true`, so `tests/arena.sh --direct-off` would
#    then build the shipped configuration, run it against the *off*
#    column of the expectations, and — since the two columns agree
#    everywhere except the five known fixtures — report a confident
#    green for a configuration that was never built.  That is a silent
#    false pass, the worst failure mode a test harness has.  Insisting
#    on exactly one pristine occurrence turns every way of losing the
#    flip (renamed, reworded, reformatted, already flipped, moved to
#    another module) into a loud exit 3 instead.
n=$(grep -c '^def directStructsEnabled : Bool := true$' "$OUT/$FLAGFILE" || true)
if [ "$n" != 1 ]; then
  echo "build-direct-off: expected exactly one" \
       "'def directStructsEnabled : Bool := true' in $FLAGFILE, found $n" >&2
  exit 3
fi
sed -i 's/^def directStructsEnabled : Bool := true$/def directStructsEnabled : Bool := false/' \
  "$OUT/$FLAGFILE"

# 4. build just the executable (the proof libraries are parametric in the
#    switch and are covered by the ordinary `lake build`)
( cd "$OUT" && lake build setlec ) >&2

echo "$OUT/.lake/build/bin/setlec"
