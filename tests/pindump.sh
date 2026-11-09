#!/usr/bin/env bash
# tests/pindump.sh — THE PIN-DUMP FRESHNESS GATE (tasks #176, #273, #275, #328).
#
# WHY THIS EXISTS.  The pinned `Nat`-operation declarations and their
# certificate proof blobs used to be computed while
# `ConLeche/Kernel/NatOpPins.lean` elaborated, out of an olean loaded BY
# NAME (`ConLeche/PinGen/Certs.olean`).  That is not an import edge, Lake
# never ordered the two, and on a cold tree `lake build con-leche` failed
# outright.  Per the user's ruling the pins are now COMMITTED files,
#
#     pins/<toolchain>.json
#
# written by the `natop-pins-export` executable, which lives in the
# certificate library's world (its root imports `ConLeche.PinGen.Certs`,
# so the proof bodies are visible and Lake orders the build).
#
# A committed generator output needs a staleness ratchet — regenerate,
# `diff -q`, fail loudly.  This gate does that for EVERY committed dump.
#
# PIN VARIANTS AND PINNERS (tasks #273, #275).  `pins/` holds one dump
# per supported toolchain and `ConLeche/Kernel/NatOpPins.lean` embeds
# ALL of them (the install gate tries them in order).  A dump is
# computed by the generator running ON its toolchain, so each one has
# its own self-contained Lake project — a PINNER —
#
#     pinners/<sanitised toolchain>/{lean-toolchain,lakefile.toml}
#
# whose sources are the repository's own generator (`srcDir = "../.."`;
# see `pinners/README.md`).  This gate walks `pinners/*/`, and for each
# pinner whose toolchain elan has, builds it, regenerates into a scratch
# directory and diffs against the committed files.  A pinner whose
# toolchain is NOT installed is reported as a labelled SKIP — unless
# `PINDUMP_INSTALL=1`, when elan installs it first (that is how CI runs
# it, so every dump is reproduced there).  The repository's own
# toolchain need not have a pinner (below); its generator is the root
# project, which always runs, for the prelude.
#
# THE REPOSITORY TOOLCHAIN NEED NOT HAVE A DUMP OF ITS OWN (task #328).
# A dump is named after the toolchain that first needed it.  When a
# toolchain bump leaves the pinned definitions alone, a committed pin
# set still matches the new Init, and the maintainer's ruling is that
# no new dump is added then: *"if the previous works with the new Init
# we should not add one"*.  Matching is what the install gate decides —
# the stream's stored value DEFINITIONALLY EQUAL to a variant's pin,
# and that variant's certificates checking — so this gate asks the
# checker: it runs `scripts/natop-matrix.sh` on the repository
# toolchain (export the pinned operations' cone out of its `Init`, run
# the freshly built binary over it) and fails unless that ACCEPTS.  A
# decline there ("no pin variant matched") means the pinned definitions
# drifted and a new dump (and pinner) is needed: `pins/README.md`,
# "Adding a toolchain's variant".
#
# It also checks the embed/commit correspondence: every committed dump
# is embedded by `ConLeche/Kernel/NatOpPins.lean` and has a pinner,
# every embedded dump is committed, and the repository toolchain's
# prelude exists and is the one `ConLeche/Frontend/Prelude.lean`
# embeds.
#
# THE PRELUDE IS ONE FILE, the repository toolchain's — the pinned
# basis blocks and `Bool`/`And`, which have not drifted across the
# supported toolchains.  It is named after `lean-toolchain` and the root
# generator's regeneration must reproduce it byte-for-byte (its meta
# line carries the generating Lean's version and githash).  A pinner's
# regenerated prelude is diffed against it BELOW ITS META LINE; a
# difference there is prelude drift and needs the prelude generalised
# the way the pins were.
#
# Usage: tests/pindump.sh            [PINDUMP_INSTALL=1 to install
#                                     missing toolchains with elan;
#                                     PINDUMP_BINARY=<path> to use a
#                                     prebuilt con-leche binary]
set -u
cd "$(dirname "$0")/.."

# the generator's own sanitisation (ConLeche.PinGen.toolchainFileName):
# everything outside [A-Za-z0-9._-] becomes '-'
sanitise () { printf '%s' "$1" | sed 's/[^A-Za-z0-9._-]/-/g'; }

TC=$(tr -d ' \t\n\r' < lean-toolchain)
BASE=$(sanitise "$TC").json
# the built-in prelude (task #191): the sidecar the same generator
# writes, embedded by ConLeche/Frontend/Prelude.lean
PBASE=${BASE%.json}.prelude.ndjson
PCOMMITTED=pins/$PBASE
SCRATCH=_tmp/pindump-gate

fail () { echo "PINDUMP FAIL — $*"; exit 1; }

# the embedded dumps, in `#load_natop_pins` order
EMBEDDED=$(grep -o 'include_str "../../pins/[^"]*\.json"' ConLeche/Kernel/NatOpPins.lean |
             sed 's#.*/pins/##; s/"$//')

# ---------------------------------------------------------------- the
# committed set: dumps, preludes, embeds and pinners agree.

for f in pins/*.json; do
  b=$(basename "$f")
  grep -q "include_str \"../../pins/$b\"" ConLeche/Kernel/NatOpPins.lean ||
    fail "committed dump $f is not embedded by ConLeche/Kernel/NatOpPins.lean"
  [ -d "pinners/${b%.json}" ] ||
    fail "committed dump $f has no pinner:
    expected pinners/${b%.json}/ — see pinners/README.md"
done
for b in $EMBEDDED; do
  [ -f "pins/$b" ] ||
    fail "ConLeche/Kernel/NatOpPins.lean embeds pins/$b, which is not committed"
done

[ -f "$PCOMMITTED" ] || fail "no committed built-in prelude for toolchain $TC:
    expected $PCOMMITTED"

grep -q "include_str \"../../pins/$PBASE\"" ConLeche/Frontend/Prelude.lean ||
  fail "ConLeche/Frontend/Prelude.lean does not embed $PBASE;
    a toolchain bump must re-point the include_str at the new prelude."


# ---------------------------------------------------------------- the
# repository's own generator target.  `lake build` does not reach it
# (it is not a default target), so the tree's warning-free rule is
# enforced here.
BUILDLOG=$(lake build natop-pins-export 2>&1) ||
  fail "the repository's generator did not build:
$(printf '%s\n' "$BUILDLOG" | tail -20)"
if printf '%s\n' "$BUILDLOG" | grep -q 'warning:'; then
  fail "the repository's generator built with warnings:
$(printf '%s\n' "$BUILDLOG" | grep -A3 'warning:' | sed 's/^/    /')"
fi

rm -rf "$SCRATCH"
mkdir -p "$SCRATCH"
ROOT=$PWD

# ---------------------------------------------------------------- the
# repository toolchain: some committed pin set must match its Init.
# The checker decides, exactly as on any stream: `natop-matrix.sh`
# exports the pinned operations' cone out of `Init` (the toolchain's
# bundled `leanexport`) and runs the binary in verified mode; an accept
# means every pin-certified operation found a variant whose pin is
# definitionally equal to the stored value and whose certificates check.
# `PINDUMP_BINARY=<path>` uses a prebuilt binary instead (CI's
# `regenerate` job downloads the one its `build` job made).
if [ -n "${PINDUMP_BINARY:-}" ]; then
  BINARY=$(cd "$(dirname "$PINDUMP_BINARY")" && pwd)/$(basename "$PINDUMP_BINARY")
else
  lake build con-leche >/dev/null 2>&1 ||
    fail "the con-leche binary did not build:
$(lake build con-leche 2>&1 | tail -20 | sed 's/^/    /')"
  BINARY=$ROOT/.lake/build/bin/con-leche
fi
MATRIX_LOG=$ROOT/$SCRATCH/natop-matrix.log
mline=$(bash scripts/natop-matrix.sh --binary "$BINARY" --work "$ROOT/$SCRATCH/matrix" "$TC" 2> "$MATRIX_LOG")
mrc=$?
[ "$mrc" = 0 ] || fail "NO COMMITTED PIN SET MATCHES the repository toolchain $TC:
    natop-matrix.sh on its Init: $mline
$(grep -i 'pin variant\|declin\|error' "$MATRIX_LOG" | head -10 | sed 's/^/    /')
    If the checker declined with \"no pin variant matched\", the pinned
    definitions drifted and a new dump is needed: add
    pinners/$(sanitise "$TC")/ and its dump as pins/README.md (\"Adding a
    toolchain's variant\") describes, and list it FIRST in
    #load_natop_pins.  (Full log: $MATRIX_LOG)"
echo "pindump: a committed pin set matches $TC's Init ($mline)"

# ... and the built-in prelude is the repository toolchain's own,
# reproduced byte-for-byte by the root generator (the dump it writes
# beside it is not committed unless the check above needed a new one).
out=$ROOT/$SCRATCH/repository
mkdir -p "$out"
runout=$(timeout 3600 lake env ./.lake/build/bin/natop-pins-export "$out") ||
  fail "the repository's generator did not run on $TC:
$(lake env ./.lake/build/bin/natop-pins-export "$out" 2>&1 | tail -20)"
pfresh=$(printf '%s\n' "$runout" | sed -n 2p)
[ "$pfresh" = "$out/$PBASE" ] ||
  fail "the repository's generator wrote $pfresh, expected $out/$PBASE"
diff -q "$PCOMMITTED" "$pfresh" >/dev/null ||
  fail "the committed built-in prelude $PCOMMITTED is STALE:
$(diff "$PCOMMITTED" "$pfresh" | head -20 | sed 's/^/    /')
    regenerate it with \`lake exe natop-pins-export _tmp/x\` and copy
    $(basename "$pfresh") into pins/"
echo "pindump: the root generator reproduces $PCOMMITTED byte-for-byte"

# ---------------------------------------------------------------- the
# pinners: one per committed dump, each on its own toolchain.
ran=0
skipped=0

installed_toolchains=$(elan toolchain list 2>/dev/null | sed 's/ (default)$//')

for p in pinners/*/; do
  d=$(basename "$p")
  [ -f "$p/lean-toolchain" ] || fail "$p has no lean-toolchain"
  [ -f "$p/lakefile.toml" ] || fail "$p has no lakefile.toml"
  ptc=$(tr -d ' \t\n\r' < "$p/lean-toolchain")
  [ "$(sanitise "$ptc")" = "$d" ] ||
    fail "$p names toolchain $ptc, whose dump would be $(sanitise "$ptc").json —
    the pinner directory must be named after its own toolchain."
  pbase=$d.json
  [ -f "pins/$pbase" ] ||
    fail "$p has no committed dump (expected pins/$pbase);
    regenerate with: cd $p && lake exe natop-pins-export ../../pins"

  if ! printf '%s\n' "$installed_toolchains" | grep -Fxq "$ptc"; then
    if [ "${PINDUMP_INSTALL:-0}" = 1 ]; then
      echo "pindump: installing $ptc for $p"
      # elan's exit code is not the answer here (it fails with "already
      # installed" on a race, and prints progress to stderr either way);
      # the list is.
      elan toolchain install "$ptc" >/dev/null 2>&1
      installed_toolchains=$(elan toolchain list 2>/dev/null | sed 's/ (default)$//')
      printf '%s\n' "$installed_toolchains" | grep -Fxq "$ptc" ||
        fail "elan could not install $ptc for $p"
    else
      echo "pindump: SKIP $p — toolchain $ptc is not installed"
      echo "         (set PINDUMP_INSTALL=1 to let elan install it and reproduce the dump)"
      skipped=$((skipped + 1))
      continue
    fi
  fi

  out=$ROOT/$SCRATCH/$d
  mkdir -p "$out"
  log=$ROOT/$SCRATCH/$d.build.log
  # A foreign toolchain may deprecate a name the shared sources use;
  # that is a warning there, not here, and it does not change the dump.
  # The warning-free rule is the repository toolchain's, enforced on
  # the root target above.
  ( cd "$p" && timeout 3600 lake build ) > "$log" 2>&1 ||
    fail "$p did not build on $ptc:
$(tail -20 "$log" | sed 's/^/    /')"

  # `lake env` rather than `lake exe`: the latter replays the build's
  # warnings onto stdout, which is where the two written paths are.
  # The generator reads `lean-toolchain` by searching upward from the
  # working directory, so it must run IN the pinner.
  runout=$( cd "$p" && timeout 3600 lake env ./.lake/build/bin/natop-pins-export "$out" ) ||
    fail "$p: the generator did not run on $ptc:
$( cd "$p" && lake env ./.lake/build/bin/natop-pins-export "$out" 2>&1 | tail -20 )"
  fresh=$(printf '%s\n' "$runout" | sed -n 1p)
  pfresh=$(printf '%s\n' "$runout" | sed -n 2p)
  [ "$fresh" = "$out/$pbase" ] ||
    fail "$p: the generator wrote $fresh, expected $out/$pbase
    (the toolchain it read disagrees with $p/lean-toolchain)"

  diff -q "pins/$pbase" "$fresh" >/dev/null ||
    fail "the committed pin dump pins/$pbase is STALE:
    it differs from a fresh regeneration on $ptc
$(diff "pins/$pbase" "$fresh" | head -20 | sed 's/^/    /')
    regenerate and commit:  cd $p && lake exe natop-pins-export ../../pins"

  # only the repository toolchain's prelude is committed; a pinner's
  # must agree with it below the meta line (the generating Lean's
  # version and githash live there).
  diff <(tail -n +2 "$PCOMMITTED") <(tail -n +2 "$pfresh") >/dev/null ||
    fail "PRELUDE DRIFT — $ptc's built-in prelude differs from $PCOMMITTED
    below its meta line.  The prelude is one file for all supported
    toolchains (pins/README.md); a drifting one needs it generalised
    the way the pins were.
$(diff <(tail -n +2 "$PCOMMITTED") <(tail -n +2 "$pfresh") | head -20 | sed 's/^/    /')"
  echo "pindump: $p reproduces pins/$pbase byte-for-byte (prelude matches below its meta line)"
  ran=$((ran + 1))
done
echo "pindump: $(ls pins/*.json | wc -l) dump(s) embedded: $(ls pins/*.json | xargs -n1 basename | tr '\n' ' ')"
echo "pindump: $PCOMMITTED fresh ($(wc -l < "$PCOMMITTED") lines, $(grep -c '"inductive"\|"quot"\|"axiom"\|"def"\|"thm"\|"opaque"' "$PCOMMITTED") declaration records)"
echo "pindump: $ran pinner(s) reproduced, $skipped skipped"
rm -rf "$SCRATCH"
exit 0
