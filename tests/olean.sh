#!/usr/bin/env bash
# THE OLEAN GATE: `con-leche --olean`, and a home's read of all three views
# (`olean-compare --views`), on the committed fixtures of
# tests/olean/lib (compiled from tests/olean/src by tests/olean/build.sh
# with the toolchain's own `lean`), and on corrupted copies of them made
# here.  Every verdict is pinned below; the comment on a case names what
# it guards.  Run from the repository root after `lake build`; the
# arena battery (tests/arena.sh) runs it.
#
# Exit codes (arena convention): 0 accept, 1 reject, 2 decline, 3 error.
set -u
BIN=${BIN:-.lake/build/bin/con-leche}
export TMPDIR="${TMPDIR:-$PWD/_tmp/tmp}"
mkdir -p "$TMPDIR"
LIB=tests/olean/lib
fail=0
ok=0
total=0
case_() { # <description> <expected-exit> <args...>
  local desc=$1 want=$2; shift 2
  total=$((total+1))
  timeout 60 "$BIN" "$@" >"$TMPDIR/olean-case.out" 2>&1
  local got=$?
  # OLEAN_VERBOSE=1 shows each case's verdict line
  if [ -n "${OLEAN_VERBOSE:-}" ]; then
    echo "-- $desc"; grep -v "stats:" "$TMPDIR/olean-case.out" | tail -1
  fi
  if [ "$got" = "$want" ]; then ok=$((ok+1))
  else echo "OLEAN FAIL ($desc): expected exit $want, got $got"; fail=1; fi
}
CMP=${CMP:-.lake/build/bin/olean-compare}
lake build olean-compare >/dev/null || exit 3
views_() { # <description> <expected-exit> <pattern> <search path> <module>: all views parsed whole
  cmp_ --views "$@"
}
cmp_() { # <mode> <description> <expected-exit> <pattern> <search path> <module>
  local mode=$1; shift
  total=$((total+1))
  timeout 60 "$CMP" $mode "$4" "$5" >"$TMPDIR/olean-case.out" 2>&1
  local got=$?
  if [ "$got" != "$2" ]; then echo "OLEAN FAIL ($1): expected exit $2, got $got"; fail=1
  elif ! grep -q -- "$3" "$TMPDIR/olean-case.out"; then
    echo "OLEAN FAIL ($1): the output lacks \"$3\""; fail=1
  else ok=$((ok+1)); fi
}

case_grep() { # <description> <expected-exit> <pattern the output must hold> <args...>
  local desc=$1 want=$2 pat=$3; shift 3
  case_ "$desc" "$want" "$@"
  if ! grep -q -- "$pat" "$TMPDIR/olean-case.out"; then
    echo "OLEAN FAIL ($desc): the output lacks \"$pat\""; fail=1; ok=$((ok-1))
  fi
}

# --- well-formed closures ---------------------------------------------
case_ "a module-system module" 0 --olean --search-path=$LIB Tiny
views_ "all three views agree with each view's read" 0 "agrees" "$LIB" TinyUse
cmp_ --home "a home's read: the load and its parts' check" 0 "hidden" "$LIB" TinyUse
case_ "…at one worker" 0 --jobs=1 --olean --search-path=$LIB Tiny
case_ "a module outside the module system (one .olean)" 0 --olean --search-path=$LIB TinyClassic
case_ "a module and its import" 0 --olean --search-path=$LIB TinyUse
case_ "two roots" 0 --olean --search-path=$LIB TinyUse TinyClassic
case_ "a search path of two directories" 0 --olean --search-path=$TMPDIR:$LIB TinyUse
# two modules storing different constants under one name: Lean's own
# import refuses the pair ("environment already contains"), and so does
# the merge (a reject: the input says two contradicting things)
case_ "conflicting constants in two modules" 1 --olean --search-path=$LIB ClashA ClashB
INIT="$(dirname "$(dirname "$(elan which lean 2>/dev/null || command -v lean)")")/lib/lean"
MSP="$LIB:$INIT"
# the same, the two reached through a private import of an import
case_ "conflicting constants in one closure" 1 --olean --search-path=$MSP NlM

# an axiom at a certified `Nat` operation's name (Lean accepts the module):
# the name holds its certified definition or nothing, so the record is
# rejected (the fixture's comment, and task #397's ruling)
case_grep "an axiom at a certified Nat operation's name" 1 "a certified Nat operation's name, not a definition: Nat.div" --olean --search-path=$LIB NpAx
# a module hiding the value of a kind-pinned constant (`Lean.reduceBool` an
# opaque constant): the merged read has its value
case_ "a hidden kind-pinned value" 0 --olean --search-path=$LIB RbM

# --- usage --------------------------------------------------------------
case_ "--olean without a search path" 3 --olean Tiny
case_ "--olean without a module" 3 --olean --search-path=$LIB
case_ "--search-path without --olean" 3 --search-path=$LIB tests/mode/split_good.ndjson
case_ "a module not on the search path" 3 --olean --search-path=$LIB NoSuchModule

# patch any of a module's three parts, objects found by name across them:
# <dir> <module> <python over consts(part) / fld / setfld>
xpatch() {
  python3 -I - "$1" "$2" "$3" <<'PY'
import struct, sys
d, m, expr = sys.argv[1], sys.argv[2], sys.argv[3]
parts = {}
import os
for ext in ['olean', 'olean.server', 'olean.private']:
    if not os.path.exists(f'{d}/{m}.{ext}'): continue
    b = bytearray(open(f'{d}/{m}.{ext}', 'rb').read())
    parts[ext] = (struct.unpack_from('<Q', b, 80)[0], b)
def at(a):
    for ext, (base, b) in parts.items():
        if 0 <= a - base < len(b): return b, a - base
    raise Exception('address outside the parts')
def fld(a, i): b, o = at(a); return struct.unpack_from('<Q', b, o + 8 + 8 * i)[0]
def setfld(a, i, v): b, o = at(a); struct.pack_into('<Q', b, o + 8 + 8 * i, v)
def name(a):
    if a == 1: return ''
    pre = name(fld(a, 0))
    b0, o0 = at(a)
    if b0[o0 + 7] == 2: return pre + '.' + str(fld(a, 1) >> 1)
    b, s = at(fld(a, 1))
    sz = struct.unpack_from('<Q', b, s + 8)[0]
    return (pre + '.' if pre else '') + b[s + 32:s + 32 + sz - 1].decode()
def consts(ext):
    base, b = parts[ext]
    ab, ao = at(fld(struct.unpack_from('<Q', b, 88)[0], 2))
    n = struct.unpack_from('<Q', ab, ao + 8)[0]
    # a ConstantInfo's field 0 is its XxxVal, whose field 0 is the ConstantVal
    return {name(fld(fld(fld(c, 0), 0), 0)): c for c in
            (struct.unpack_from('<Q', ab, ao + 24 + 8 * i)[0] for i in range(n))}
exec(expr)
for ext, (base, b) in parts.items(): open(f'{d}/{m}.{ext}', 'wb').write(b)
PY
}
# --- which constants ----------------------------------------------------
# a private theorem nothing refers to is checked, whatever its name: its proof
# replaced by a term of another type
d="$TMPDIR/con-leche-olean-priv"
rm -rf "$d"; cp -r "$LIB" "$d"
xpatch "$d" PrivUnused "
cs = consts('olean.private')
setfld(fld(cs['_private.tests.olean.src.PrivUnused.0.secret'], 0), 1, fld(fld(cs['two'], 0), 1))"
case_ "an unreferenced private theorem is checked" 0 --olean --search-path=$LIB PrivUnused
case_ "an unreferenced private theorem with a bad proof" 1 --olean --search-path=$d PrivUnused
# --constant: that constant and what it mentions, as lean4export's -- does
case_ "--constant leaves out what it does not reach" 0 --olean --constant=two --search-path=$d PrivUnused
case_ "--constant of a number component" 1 --olean --constant=_private.tests.olean.src.PrivUnused.0.secret --search-path=$d PrivUnused
case_ "--constant given twice" 1 --olean --constant=two --constant=_private.tests.olean.src.PrivUnused.0.secret --search-path=$d PrivUnused
rm -rf "$d"
case_grep "--constant the closure does not hold" 3 "not in the import closure" --olean --constant=noSuch --search-path=$LIB PrivUnused
case_grep "--constant that is no name" 3 "not a constant's name" --olean --constant=a.. --search-path=$LIB PrivUnused
case_ "--constant without --olean" 3 --constant=two tests/mode/split_good.ndjson

# --- a theorem's value stays in the file until its check ------------------
# (task #481) a bad index on a bound variable only a theorem's value holds, which nothing
# but that theorem's check decodes: exit 3 there, at its place; and no verdict at all
# where no check asks for the value.  Before, the load decoded every value, so the second
# was 3 as well.  A value that is not read is no concern here (maintainer's ruling).
d="$TMPDIR/con-leche-olean-lazy"
case_ "a theorem's value read in its check" 0 --olean --search-path=$LIB LazyVal
rm -rf "$d"; cp -r "$LIB" "$d"
xpatch "$d" LazyVal "
c = consts('olean.private')['lazyProof']
tag = lambda a: at(a)[0][at(a)[1] + 7]
f = fld(fld(c, 0), 1)
while tag(f) == 5: f = fld(f, 0)
while tag(f) == 6: f = fld(f, 2)
assert tag(f) == 0
setfld(f, 0, fld(fld(fld(c, 0), 0), 0))"
case_grep "a bad value of a theorem: found by its check" 3 "malformed .olean data" \
  --olean --search-path=$d LazyVal
case_grep "…at one worker" 3 "malformed .olean data" --jobs=1 --olean --search-path=$d LazyVal
case_ "…and read by no check where --constant leaves the theorem out" 0 \
  --olean --constant=other --search-path=$d LazyVal
# a value of no expression's shape: the load's walk over what it mentions finds that,
# for every theorem of the closure, --constant or not
rm -rf "$d"; cp -r "$LIB" "$d"
xpatch "$d" LazyVal "
t = fld(consts('olean.private')['lazyProof'], 0)
setfld(t, 1, fld(t, 0))"
case_grep "a theorem's value of no expression's shape: found by the load" 3 "malformed .olean data" \
  --olean --search-path=$d LazyVal
case_ "…with --constant too" 3 --olean --constant=other --search-path=$d LazyVal
rm -rf "$d"

# --- what --progress says of the read (task #484) ----------------------
for line in "read: tracing the import closure" "read: loading 1 modules" "read: loaded 1 modules (100%)" \
    "read: merging the constants of 1 modules" "read: checking the blocks of" \
    "read: emitting records from"; do
  case_grep "--progress: $line" 0 "$line" --progress --olean --search-path=$LIB PrivUnused
done
total=$((total+1))
if timeout 60 "$BIN" --olean --search-path=$LIB PrivUnused 2>&1 | grep -q "read:"; then
  echo "OLEAN FAIL (no --progress, no read: lines)"; fail=1
else ok=$((ok+1)); fi

# --- corrupted files ----------------------------------------------------
# Each case copies the fixtures and changes bytes of Tiny's files.
# patch <file> <python expression over b (bytearray), base, root>
patch() {
  python3 -I - "$1" "$2" <<'PY'
import struct, sys
p, expr = sys.argv[1], sys.argv[2]
b = bytearray(open(p, 'rb').read())
base = struct.unpack_from('<Q', b, 80)[0]
root = struct.unpack_from('<Q', b, 88)[0]
ro = root - base                      # the root object's offset
exec(expr)
open(p, 'wb').write(b)
PY
}
corrupt() { # <description> <expected-exit> <file> <expr> [<root module>]
  local d="$TMPDIR/con-leche-olean-$total"
  rm -rf "$d"; cp -r "$LIB" "$d"
  if [ "$4" = TRUNCATE ]; then head -c 60 "$LIB/$3" > "$d/$3"; else patch "$d/$3" "$4"; fi
  case_ "$1" "$2" --olean --search-path=$d "${5:-Tiny}"
  rm -rf "$d"
}
corrupt "a truncated file: malformed input" 3 Tiny.olean.private TRUNCATE
corrupt "a wrong marker: malformed input" 3 Tiny.olean "b[0:5] = b'oleam'"
# the toolchain the header names is not looked at: the format version says
# how a file is laid out
corrupt "another toolchain's githash: read" 0 Tiny.olean "b[40:48] = b'00000000'"
corrupt "another toolchain's version: read" 0 Tiny.olean "b[7:15] = b'9.99.0\\0\\0'"
corrupt "another format version: a decline" 2 Tiny.olean "b[5] = 3"
corrupt "non-GMP bignums: a decline" 2 Tiny.olean.private "b[6] = 0"
corrupt "parts out of address order" 3 Tiny.olean.server "struct.pack_into('<Q', b, 80, 8)"
corrupt "a root pointer outside the files" 3 Tiny.olean.private "struct.pack_into('<Q', b, 88, 16)"
corrupt "a misaligned root pointer" 3 Tiny.olean.private "struct.pack_into('<Q', b, 88, root + 4)"
corrupt "a field pointing at its own object (a cycle)" 3 Tiny.olean.private "struct.pack_into('<Q', b, ro + 8, root)"
corrupt "a field pointing above its object" 3 Tiny.olean.private "struct.pack_into('<Q', b, ro + 8, root + 64)"
corrupt "the root's constructor tag changed" 3 Tiny.olean.private "b[ro + 7] = 200"
corrupt "the root's field count changed" 3 Tiny.olean.private "b[ro + 6] = 1"
# (the next two patch objects reachable from the root, so they use the
# classic module, whose one file holds all of them: a module-system
# module's private part points into its exported part)
# every constant of the module, its ConstantInfo tag set past recInfo
corrupt "a ConstantInfo of no kind" 3 TinyClassic.olean "
cs = struct.unpack_from('<Q', b, ro + 8 + 16)[0] - base
n = struct.unpack_from('<Q', b, cs + 8)[0]
for i in range(n):
    c = struct.unpack_from('<Q', b, cs + 24 + 8 * i)[0] - base
    b[c + 7] = 9" TinyClassic
# every string object's last byte (its NUL) replaced: not a string
corrupt "strings without their terminator" 3 TinyClassic.olean "
i = 96
while i + 32 <= len(b):
    if b[i + 7] == 249:
        sz = struct.unpack_from('<Q', b, i + 8)[0]
        if 0 < sz < len(b) and i + 32 + sz <= len(b): b[i + 32 + sz - 1] = 65
    i += 8" TinyClassic

# the name table (ModuleData.constNames: the keys Lean's loader stores the
# constants under) must list the constants' names (task #383): two of
# its entries swapped, in each part
cswap="
nt = struct.unpack_from('<Q', b, ro + 16)[0] - base
x, y = (struct.unpack_from('<Q', b, nt + 24 + 8 * i)[0] for i in (0, 1))
struct.pack_into('<Q', b, nt + 24, y); struct.pack_into('<Q', b, nt + 32, x)"
corrupt "a name table that names the constants differently (classic)" 3 TinyClassic.olean "$cswap" TinyClassic
corrupt "a name table that names the constants differently (private part)" 3 Tiny.olean.private "$cswap"
# (a part the private view does not read as a ModuleData: `--olean` reads the private
# view, as Lean's import outside the module system does; a home's read rejects it)
# (the home's check of its parts, `checkViews`, rejects a mismatch, exit 1; reading all
# three views whole first, as `--views` does, finds a part that is not a view, exit 3)
home_rejects() { # <description> <pattern> <search path> <module> <exit of --views>
  case_ "$1 [--olean, the private view]" 0 --olean --search-path=$3 "$4"
  views_ "$1 [all views parsed]" "$5" "$2" "$3" "$4"
  cmp_ --home "$1 [a home's read]" 1 "$2" "$3" "$4"
  case_grep "$1 [the worker]" 1 "$2" --olean --module --search-path=$3 -- "$4"
}
d="$TMPDIR/con-leche-olean-home"
rm -rf "$d"; cp -r "$LIB" "$d"; patch "$d/Tiny.olean" "$cswap"
home_rejects "a name table that names the constants differently (exported part)" "name table" "$d" Tiny 3
rm -rf "$d"
corrupt "a name table shorter than the constants" 3 TinyClassic.olean "
nt = struct.unpack_from('<Q', b, ro + 16)[0] - base
struct.pack_into('<Q', b, nt + 8, struct.unpack_from('<Q', b, nt + 8)[0] - 1)" TinyClassic
# one module storing `idU` twice (in place of U.recOn, which nothing
# uses): malformed (task #383: the merge rejected two definitions of one
# name, the modular emission kept the later one only, below)
cdup="
nt = struct.unpack_from('<Q', b, ro + 16)[0] - base
cs = struct.unpack_from('<Q', b, ro + 24)[0] - base
for a in (nt, cs):
    struct.pack_into('<Q', b, a + 24 + 16, struct.unpack_from('<Q', b, a + 24 + 32)[0])"
corrupt "one module storing a name twice" 3 TinyClassic.olean "$cdup" TinyClassic

# the private part's header (task #383): its module-system flag cleared
d="$TMPDIR/con-leche-olean-home"
rm -rf "$d"; cp -r "$LIB" "$d"; patch "$d/Tiny.olean.private" "b[ro + 48] = 0"
home_rejects "a private part outside the module system" "not of a module of the module system" "$d" Tiny 1
rm -rf "$d"
xcorrupt0() { # <description> <expected-exit> <module> <expr> <args...>   (mode: $MOD)
  local desc=$1 want=$2 m=$3 expr=$4; shift 4
  local d="$TMPDIR/con-leche-olean-$total"
  rm -rf "$d"; cp -r "$LIB" "$d"
  xpatch "$d" "$m" "$expr"
  case_ "$desc${MOD:+ [$MOD]}" "$want" --olean $MOD --search-path=$d:$INIT "$@"
  rm -rf "$d"
}
rcases() {
  # the exported axiom standing for the safe definition idT made unsafe:
  # not the private constant with its value hidden
  local d="$TMPDIR/con-leche-olean-home"
  rm -rf "$d"; cp -r "$LIB" "$d"
  xpatch "$d" Tiny "
b, o = at(fld(consts('olean')['idT'], 0))
b[o + 16] = 1"
  home_rejects "an exported constant that is not its private one" "not a refinement" "$d" Tiny 1
  rm -rf "$d"
  # the stored recursor rules (Lean's kernel runs them on a loaded
  # .olean; con-leche installs the generated ones): T.rec's two rules in
  # the other order, and T.b's rule with T.a's right-hand side
  xcorrupt0 "recursor rules in another order than the generated ones" 1 Tiny "
r = fld(consts('olean.private')['T.rec'], 0)
c1 = fld(r, 6); c2 = fld(c1, 1); r1 = fld(c1, 0); r2 = fld(c2, 0)
setfld(c1, 0, r2); setfld(c2, 0, r1)" Tiny
  xcorrupt0 "a recursor rule of another right-hand side than the generated one" 1 Tiny "
r = fld(consts('olean.private')['T.rec'], 0)
c1 = fld(r, 6); c2 = fld(c1, 1); r1 = fld(c1, 0); r2 = fld(c2, 0)
setfld(r2, 2, fld(r1, 2))" Tiny
  # an import cycle: HidA's import of Init.Prelude renamed to HidUse,
  # which imports HidA (Lean's import refuses a cycle)
  xcorrupt0 "an import cycle" 3 HidA "
base, b = parts['olean']
root = struct.unpack_from('<Q', b, 88)[0]
imp0 = struct.unpack_from('<Q', b, fld(root, 0) - base + 24)[0]
n = fld(imp0, 0)
setfld(n, 0, 1)
sb, so = at(fld(n, 1))
struct.pack_into('<QQQ', sb, so + 8, 7, struct.unpack_from('<Q', sb, so + 16)[0], 6)
sb[so + 32:so + 39] = b'HidUse\\0'" HidUse
  # the server part's imports (shared with the exported part) replaced by
  # an empty array
  local d="$TMPDIR/con-leche-olean-$total"
  rm -rf "$d"; cp -r "$LIB" "$d"
  patch "$d/HidAll.olean.server" "struct.pack_into('<Q', b, ro + 8, struct.unpack_from('<Q', b, ro + 32)[0])"
  home_rejects "the server part's imports not the exported part's" "imports are not" "$d:$INIT" HidAll 3
  rm -rf "$d"
}
MOD=; rcases

# --- Lake's and Comparator's test suites, ported ------------------------
# The Up* fixtures (tests/olean/src/Up*.lean; each header names the
# upstream test, its path and its outcome there), as plain developments:
# a challenge, with its sorry, declines
for m in UpComm UpDefHole UpDefHoleTy UpKindDef UpKindThm 'UpNum.«12.34».«5»' UpBoom UpGcd UpProj \
    UpThmHole UpSorry UpCommAxSol UpCommMisSol UpDefHoleAxSol UpDefHoleKindSol UpDefHoleTySol \
    UpBoomOpqSol UpBoomCharSol UpGcdSol; do
  case_ "upstream merged: $m" 2 --olean --search-path=$MSP "$m"
done
for m in UpCommSol UpDefHoleSol UpKindDefOpqSol UpKindThmOpqSol UpKindThmDefSol UpHidDefSol UpNumSol \
    UpProjSol UpThmHoleSol; do
  case_ "upstream merged: $m" 0 --olean --search-path=$MSP "$m"
done
case_ "upstream merged: check-multi's two roots" 0 --olean --search-path=$MSP UpMultiA UpMultiB
# quot_mismatch's modules both store Quot.lift: rejected
case_ "upstream merged: UpQuot" 1 --olean --search-path=$MSP UpQuot
case_ "upstream merged: UpQuotSol" 1 --olean --search-path=$MSP UpQuotSol
case_grep "upstream merged: UpBoomOleanSol (olean-issue, check-audit-reject)" 3 "malformed .olean data" \
  --olean --search-path=$MSP UpBoomOleanSol
# module names on the command line: an unclosed escape
case_ "a module name with an unclosed «" 3 --olean --search-path=$MSP 'UpNum.«12.34'

# --- the search path, strictly -------------------------------------------
# A module's files are in the search-path directory holding its ROOT (a
# directory <Root>/ or a file <Root>.olean), as Lean looks them up: one
# location only for each root, up to real paths; there M.olean, and for a
# module-system module all three parts; no part without its .olean or
# beside a classic one.  Another directory is never looked at for a module.
spd="$TMPDIR/con-leche-olean-sp"
NUM='UpNum.«12.34».«5»'
sp_cases() {
  rm -rf "$spd"; mkdir -p "$spd"
  cp -r "$LIB" "$spd/a"; cp -r "$LIB" "$spd/b"
  case_grep "search path: a root in two directories${MOD:+ [$MOD]}" 3 "its root TinyUse is in more than one location" \
    --olean $MOD --search-path=$spd/a:$spd/b TinyUse
  # the copy of one module only (the closure's others found once)
  rm -rf "$spd/b"; mkdir -p "$spd/b"; cp "$LIB"/Tiny.olean* "$spd/b/"
  case_grep "search path: an imported module's root in two directories${MOD:+ [$MOD]}" 3 "module Tiny: its root Tiny is in more than one location" \
    --olean $MOD --search-path=$spd/a:$spd/b TinyUse
  case_ "search path: one directory listed twice${MOD:+ [$MOD]}" 0 \
    --olean $MOD --search-path=$LIB:$LIB TinyUse
  ln -s "$PWD/$LIB" "$spd/link"
  case_ "search path: a directory and a symbolic link to it${MOD:+ [$MOD]}" 0 \
    --olean $MOD --search-path=$spd/link:$LIB TinyUse
  # a root's directory, without the module, in front of the directory holding it: the root
  # is in two places (Lean would look in the first one only, and not find the module there)
  mkdir -p "$spd/c/UpNum"
  case_grep "search path: a module under a later directory holding its root too${MOD:+ [$MOD]}" 3 "its root UpNum is in more than one location" \
    --olean $MOD --search-path=$spd/c:$LIB "$NUM"
  # the root's directory without the module: not on the search path
  case_grep "search path: a module missing in its root's directory${MOD:+ [$MOD]}" 3 "the search-path directory holding its root UpNum" \
    --olean $MOD --search-path=$spd/c "$NUM"
  rm -f "$spd/a/Tiny.olean.private"
  case_grep "search path: a missing private part${MOD:+ [$MOD]}" 3 "without its Tiny.olean.private in" \
    --olean $MOD --search-path=$spd/a TinyUse
  # the private part in a directory that does not hold the root: never looked at
  rm -rf "$spd/b"; mkdir -p "$spd/b"; cp "$LIB/Tiny.olean.private" "$spd/b/"
  case_grep "search path: a part outside its root's directory${MOD:+ [$MOD]}" 3 "without its Tiny.olean.private in $spd/a" \
    --olean $MOD --search-path=$spd/a:$spd/b TinyUse
  # parts without their .olean: of a root module, the root is on no directory; of a module
  # below a root, an error at the root's directory
  cp "$LIB/Tiny.olean.private" "$spd/a/"; rm -f "$spd/a/Tiny.olean"
  case_grep "search path: a root module's parts without its .olean${MOD:+ [$MOD]}" 3 "module Tiny: no .olean on the search path" \
    --olean $MOD --search-path=$spd/a TinyUse
  mkdir -p "$spd/c/UpNum/12.34"; cp "$LIB/Tiny.olean.private" "$spd/c/UpNum/12.34/5.olean.private"
  case_grep "search path: parts without their .olean${MOD:+ [$MOD]}" 3 "olean.private without" \
    --olean $MOD --search-path=$spd/c "$NUM"
  cp "$LIB/Tiny.olean" "$spd/a/"; cp "$LIB/Tiny.olean.private" "$spd/a/TinyClassic.olean.private"
  case_grep "search path: a private part beside a classic .olean${MOD:+ [$MOD]}" 3 "TinyClassic.olean.private beside it" \
    --olean $MOD --search-path=$spd/a TinyClassic
  rm -rf "$spd"
}
MOD=; sp_cases

# the private part's imports replaced by an empty array (the root's
# extraConstNames): not the exported part's
d="$TMPDIR/con-leche-olean-imports"
rm -rf "$d"; cp -r "$LIB" "$d"
patch "$d/HidAll.olean.private" "struct.pack_into('<Q', b, ro + 8, struct.unpack_from('<Q', b, ro + 32)[0])"
case_ "the private part's imports not the exported part's [merged]" 3 --olean --search-path=$d:$INIT HidAll
rm -rf "$d"

# --- reads through a private level ---------------------------------------
case_ "an exported value unfolding to a private-only constant" 0 --olean --search-path=$MSP WvM
# an exported definition whose value reads a private aux lemma, one reading a
# private theorem, one a private definition: the importer's `rfl` is accepted
for m in DgFlagB DgLiftB DgInferB; do
  case_ "private level: $m" 0 --olean --search-path=$MSP $m
done
# the importer's own declaration takes a name an exported constant reads
case_ "the importer declares a read name" 1 --olean --search-path=$MSP DgColM
# Lean proves False with no axiom, the exported `bar.eq_1` rebound to another
# module's `foo`; the merge holds both `foo`s
case_ "a captured name" 1 --olean --search-path=$MSP DgCapM
case_ "an inferred private theorem" 0 --olean --search-path=$MSP HiLamB
for m in HiInhM HiInhM2; do
  case_ "an import-all chain, $m" 0 --olean --search-path=$MSP $m
done
# a name declared by two modules as theorems of one statement: Lean's merge
# keeps one; of another statement: rejected
case_ "proofs of one statement, two homes" 0 --olean --search-path=$MSP TeqM
case_ "two statements under one name" 1 --olean --search-path=$MSP TeqDM

# --- an exported constant read by the parts' refinement check -------------
# `yes`, exported with a statement of 80 doubling applications (a DAG of 80
# objects, a tree of 2^80): the check that it refines the private constant
# reads it with a memo, and answers at once.  Appended to the exported file,
# in the address gap before the server part, as a new root's constants.
d="$TMPDIR/con-leche-olean-dag"
rm -rf "$d"; cp -r "$LIB" "$d"
xpatch "$d" Tiny "
base, b = parts['olean']
def push(o):
    while len(b) % 8: b.append(0)
    a = base + len(b); b.extend(o)
    while len(b) % 8: b.append(0)
    return a
def size(a): c, o = at(a); return struct.unpack_from('<H', c, o + 4)[0]
def copy(a): c, o = at(a); return push(bytes(c[o:o + size(a)]))
c = consts('olean')['yes']
top = fld(fld(fld(c, 0), 0), 2)
for _ in range(80):
    top = push(struct.pack('<iHBBQQQ', 0, 32, 2, 5, top, top, 0))
cv2 = copy(fld(fld(c, 0), 0))
setfld(cv2, 2, top)
v2 = copy(fld(c, 0)); setfld(v2, 0, cv2)
c2 = copy(c); setfld(c2, 0, v2)
root = struct.unpack_from('<Q', b, 88)[0]
arr = fld(root, 2)
ab, ao = at(arr)
n = struct.unpack_from('<Q', ab, ao + 8)[0]
arr2 = push(bytes(ab[ao:ao + 24 + 8 * n]))
for i in range(n):
    if struct.unpack_from('<Q', b, arr2 - base + 24 + 8 * i)[0] == c:
        struct.pack_into('<Q', b, arr2 - base + 24 + 8 * i, c2)
root2 = copy(root); setfld(root2, 2, arr2)
struct.pack_into('<Q', b, 88, root2)"
home_rejects "an exported statement of 2^80 nodes as a tree" "not a refinement" "$d" Tiny 1
rm -rf "$d"

# --- the imports at the start of the file --------------------------------
# the root's imports field pointed at its constants array, the prefix
# unchanged: the full read finds the two different, malformed
g="$TMPDIR/con-leche-olean-graph"
rm -rf "$g"; mkdir -p "$g"
cp -r "$LIB" "$g/root"
xpatch "$g/root" TinyClassic "
base, b = parts['olean']
root = struct.unpack_from('<Q', b, 88)[0]
setfld(root, 0, fld(root, 2))"
case_grep "a root that disagrees with the header prefix" 3 "malformed .olean data" --olean --search-path=$g/root TinyClassic
# the graph check reads the prefix alone, and accepts it (every reader of the whole file
# finds the two different, above)
case_ "graph: a root that disagrees with the header prefix" 0 \
  --check-graph --search-path=$g/root TinyClassic
rm -rf "$g"

# --- the import graph of a closure (task #467) -----------------------------
# `--check-graph`: the closure's import graph, over edges of every kind, acyclic and every
# import on the search path, read off the start of each exported file
case_grep "graph: a DAG" 0 "graph: acyclic: 3 modules, 3 import edges" \
  --check-graph --search-path=$LIB:$INIT HidUse
case_ "graph: …at one job" 0 --check-graph --jobs=1 --search-path=$LIB:$INIT HidUse
case_ "graph: …of a part of the closure" 0 --check-graph --search-path=$LIB:$INIT HidA
case_ "graph: two roots" 0 --check-graph --search-path=$LIB:$INIT HidUse TeqBoth
case_grep "graph: Init's closure, private and meta imports included" 0 "graph: acyclic" \
  --check-graph --search-path=$MSP TeqBoth
case_grep "graph: a missing import" 1 "Init.Prelude: no .olean on the search path" \
  --check-graph --search-path=$LIB HidUse
case_grep "graph: a missing root" 1 "NoSuchModule: no .olean on the search path" \
  --check-graph --search-path=$LIB NoSuchModule
# a module missing in its root's directory does not resolve either (exit 1); its root in two
# directories is malformed (exit 3)
d="$TMPDIR/con-leche-olean-graph-root"
rm -rf "$d"; mkdir -p "$d/UpNum"
case_grep "graph: a module missing in its root's directory" 1 "no .olean on the search path" \
  --check-graph --search-path=$d "$NUM"
case_grep "graph: a module's root in two directories" 3 "its root UpNum is in more than one location" \
  --check-graph --search-path=$d:$LIB "$NUM"
rm -rf "$d"
case_ "graph: with --olean, a usage error" 3 --check-graph --olean --search-path=$LIB HidUse
case_ "graph: without a search path, a usage error" 3 --check-graph HidUse
# an import cycle: HidA's import of Init.Prelude renamed to HidUse, which imports HidA
# (Lean's import refuses a cycle); no numbering is topological
g="$TMPDIR/con-leche-olean-graph"
rm -rf "$g"; mkdir -p "$g"
cp -r "$LIB" "$g/cyc"
xpatch "$g/cyc" HidA "
base, b = parts['olean']
root = struct.unpack_from('<Q', b, 88)[0]
imp0 = struct.unpack_from('<Q', b, fld(root, 0) - base + 24)[0]
n = fld(imp0, 0)
setfld(n, 0, 1)
sb, so = at(fld(n, 1))
struct.pack_into('<QQQ', sb, so + 8, 7, struct.unpack_from('<Q', sb, so + 16)[0], 6)
sb[so + 32:so + 39] = b'HidUse\\0'"
case_grep "graph: an import cycle" 1 "import cycle: HidUse → HidA → HidUse" \
  --check-graph --search-path=$g/cyc:$INIT HidUse
case_grep "graph: an import cycle, from the other root" 1 "import cycle: HidA → HidUse → HidA" \
  --check-graph --search-path=$g/cyc:$INIT HidA
# an unreadable header: HidA's exported file cut short
cp -r "$LIB" "$g/cut"
head -c 40 "$LIB/HidA.olean" > "$g/cut/HidA.olean"
case_ "graph: a header cut short" 3 --check-graph --search-path=$g/cut:$INIT HidUse
rm -rf "$g"

# --- a worker's reads: the header fixpoint, the name index, the clash rule, freshness ---
# (task #464, `olean-compare --reads`; the levels and the loaded names are Lean's own
# `importModules`', compared by hand on every fixture and on two Mathlib modules)
reads_() { cmp_ --reads "$@"; }
reads_ "an import all of a module with a plain import: LvA whole, LvB exported, LvC not loaded" 0 \
  "loads 2 modules (1 private, 1 exported)" "$LIB" LvM
reads_ "a public import and an import all: LvA exported, LvB and LvC whole" 0 \
  "loads 3 modules (2 private, 1 exported)" "$LIB" LvN
reads_ "a private import of an import is not loaded: NlX's nl never meets NlY's" 0 \
  "0 names held twice" "$MSP" NlM
reads_ "two proofs of one statement, both loaded: merged" 0 "83 names held twice" "$MSP" TeqBoth
swap_() { # <dir> <stand-in module> <module whose files take its place>
  rm -f "$1/$2".olean*
  for f in "$LIB/$3".olean*; do cp "$f" "$1/$2${f#$LIB/$3}"; done
}
d="$TMPDIR/con-leche-olean-reads"
rm -rf "$d"; cp -r "$LIB" "$d"
swap_ "$d" ClashX ClashB
reads_ "two different constants of one name loaded together" 1 "ClashA and ClashX store different constants named clash" "$d" ClashM
swap_ "$d" TeqX TeqQ2
reads_ "two theorems of one name and two statements loaded together" 1 "store different constants named teq" "$d:$INIT" TeqBad
swap_ "$d" FrX FrY
reads_ "a module declaring a loaded name" 1 "declares fresh, which the module FrX" "$d" FrM
swap_ "$d" MoX TinyClassic
reads_ "a module importing one outside the module system" 1 "imports MoX, which is not" "$d" MoM
rm -rf "$d"

# --- a worker's context: the reach, the completion, the capture check ------
# (task #465, `olean-compare --reach`: from the names the module's own records
# read, every reached name presented as its record, groups whole, an imported
# theorem's value and a hidden definition's never read)
reach_() { cmp_ --reach "$@"; }
for m in TinyUse DgFlagB DgLiftB DgInferB HiLamB HiInhM HiInhM2 TeqM TeqBoth NsM NsN LdgM LdvM GrN; do
  reach_ "the reach of $m" 0 "reach" "$MSP" $m
done
# an exported value unfolding to a private-only constant (WvA's wv_secret):
# completed as its statement, located in WvA's view; no override
reach_ "an exported value reading a private-only constant: completed" 0 "1 completed" "$MSP" WvM
# M's own foo and the foo H's exported records read: no record of M's context
# reads it, so the reach accepts, as Lean does (the merged read rejects the pair)
reach_ "the importer declares a name an unreached record reads" 0 "reach" "$MSP" DgColM
# the name H's teqN reads is not reached (teqN is not exposed): accepted, as by
# Lean (the merged read rejects the two teq)
reach_ "two statements under one name, neither reached" 0 "reach" "$MSP" TeqDM
# Lean proves False with no axiom: H's bar.eq_1 reads Q's foo, M holds Q2's;
# the two copies are definitions of Nat, not one key
reach_ "a captured name" 1 "name capture at foo, read by module DgCapH" "$MSP" DgCapM
# PdA's definition of `id True` (exported as an axiom) and PdB's theorem meet:
# one copy is a theorem, so they agree with no inference (task #506; Lean merges
# them)
reach_ "a definition of a proposition meets a theorem: no inference" 0 "0 flags inferred" "$MSP" PdM
# AxA's and AxB's `axiom Lean.trustCompiler : True` meet, both axioms at their homes: Lean
# merges them (`isPropCheap`), so must the reach (task #444): the flag inferred, one key.
# Every home accepts its own axiom (the pinned statement), and the merged read the closure
reach_ "two axioms of one propositional statement meet: the flag inferred" 0 "1 flags inferred" "$MSP" AxM
case_ "…the homes and the merged read" 0 --olean --search-path=$MSP AxA AxB AxM
# AxI's `axiom axi : id True` meets AxIT's theorem (Lean's theorem/axiom arm, no isPropCheap):
# one copy is a theorem, so no inference (task #506; the home's check declines the axiom)
reach_ "an axiom of a proposition meets a theorem: no inference" 0 "0 flags inferred" "$MSP" AxIM
case_ "…the axiom's home declines it" 2 --olean --search-path=$MSP AxI
# AxNA's `axiom axn : Nat` and AxNB's (as AxNX's files; Lean's import refuses the pair):
# not a proposition, rejected by the clash rule, as by Lean
d="$TMPDIR/con-leche-olean-axn"
rm -rf "$d"; cp -r "$LIB" "$d"
swap_ "$d" AxNX AxNB
reach_ "two axioms of one type that is not a proposition meet" 1 "AxNA and AxNX store different constants named axn" "$d:$INIT" AxNM
rm -rf "$d"
# LdgA's and LdvA's import of their Q made private (a header Lean does not
# write for a public statement reading Q): the group's constructor reads a name
# N's view lacks, completed in LdgA's (LdvA's) view as its statement; with the
# import dropped, located nowhere
patch_import() { # <file> private|drop: the module's last import made private, or dropped
python3 -I - "$1" "$2" <<'PY'
import struct, sys
p, mode = sys.argv[1], sys.argv[2]
b = bytearray(open(p, 'rb').read())
base = struct.unpack_from('<Q', b, 80)[0]
ro = struct.unpack_from('<Q', b, 88)[0] - base
arr = struct.unpack_from('<Q', b, ro + 8)[0] - base
n = struct.unpack_from('<Q', b, arr + 8)[0]
assert n == 3, n          # Init (twice), the module's own import
if mode == 'private':
    q = struct.unpack_from('<Q', b, arr + 24 + 16)[0] - base
    assert b[q + 17] == 1     # the import's isExported flag
    b[q + 17] = 0
else:
    struct.pack_into("<Q", b, arr + 8, 2)
    struct.pack_into("<Q", b, arr + 16, 2)
open(p, 'wb').write(b)
PY
}
d="$TMPDIR/con-leche-olean-reach"
for a in Ldg Ldv; do
  rm -rf "$d"; cp -r "$LIB" "$d"
  patch_import "$d/${a}A.olean" private
  reach_ "a group's read completed ($a)" 0 "1 completed" "$d:$INIT" ${a}N
  rm -rf "$d"; cp -r "$LIB" "$d"
  patch_import "$d/${a}A.olean" drop
  reach_ "a group's read located nowhere ($a)" 1 "which no module of its view holds" "$d:$INIT" ${a}N
done
rm -rf "$d"

# --- the worker: one module checked against its context ---------------------
# (task #466, `con-leche --olean --module`: the home's read and check, the reads,
# the own records, the reach, the own records' jobs over the context.  Lean
# compiled every module below, so Lean accepts each one; a verdict that is not
# 0 names why.)
work_() { # <description> <expected-exit> <pattern> <search path> <module> [flag]
  case_grep "$1" "$2" "$3" --olean --module ${6:-} --search-path=$4 -- "$5"
}
for m in Tiny TinyUse TinyClassic LazyVal PrivUnused HidA HidAll HidUse RbH RbM \
    DgFlagA DgFlagB DgLiftA DgLiftB DgInferA DgInferB DgCapQ DgCapQ2 DgCapH DgColQ DgColH \
    HiLamA HiLamB HiInhD HiInhL HiInhT HiInhX HiInhM HiInhM2 \
    TeqH TeqP1 TeqP2 TeqQ2 TeqX TeqM TeqBoth NsC NsH NsM NsN \
    LdgQ LdgA LdgM LdgN LdvQ LdvA LdvM LdvN GrN LvA LvB LvC LvM LvN \
    PdA PdB WvA WvB ClashA ClashB ClashX FrX FrY MoX NlB NlX NlY PpA PpB DnM1 DnM2 DnH \
    GbG GbG2 TdA TdB TdH TdM; do
  work_ "the worker at $m" 0 "accepted" "$MSP" $m
done
# RtA's theorem at the compiler-trust name Lean.reduceBool: the name is reserved to the opaque
# constant of the pin's shape, so RtA's own worker refuses it, a reject Lean does not make
work_ "a theorem at a compiler-trust name" 1 "a compiler-trust name, not an opaque constant" "$MSP" RtA
# RtA's theorem at the compiler-trust name Lean.reduceBool, read by RtM: its statement as an
# axiom at that name presents nothing RtA declares (a record there is presented as itself), so
# the reach refuses it (task #448); Lean accepts the module
work_ "a theorem at a compiler-trust name, read" 1 "Lean.reduceBool, a compiler-trust name, as neither" "$MSP" RtM
# an own unsafe definition is no record, and what it reads is no root of the reach: UsM's
# usUse reads UsA's unsafe usPeek, and the module is accepted, as by Lean (task #468)
work_ "an own unsafe definition reading an imported unsafe one" 0 "accepted 1 declarations" "$MSP" UsM
# NlX's nl and NlY's nl, behind a private import of an import, are never loaded
# together: accepted, as by Lean (the merged read of the closure rejects the pair)
work_ "two modules of one name never loaded together" 0 "accepted" "$MSP" NlM
# M's own foo and the foo H's exported records read: no record of M's context
# reads it: accepted, as by Lean (the merged read rejects the pair)
work_ "the importer declares a name an unreached record reads" 0 "accepted" "$MSP" DgColM
# H's teqN is not exposed, so the teq it reads is not reached: accepted, as by
# Lean (the merged read rejects the two teq)
work_ "two statements under one name, neither reached" 0 "accepted" "$MSP" TeqDM
# WvA's wv_secret, read by exported values, is completed as its statement: no
# override flag
work_ "an exported value reading a private-only constant" 0 "1 completed" "$MSP" WvM --progress
# PdA's definition of `id True` meets PdB's theorem: no inference, one copy being a theorem
# (task #506), as Lean merges
work_ "a definition of a proposition meets a theorem" 0 "0 flags inferred" "$MSP" PdM --progress
# PdA's definition (by `import all`) and PdB's theorem loaded together: the clash rule refuses
# them, as Lean's import does (no theorem/definition arm); PdN is compiled against a stand-in
work_ "a definition and a theorem of one name loaded together" 1 \
  "modules PdA and PdB store different constants named pd" "$MSP" PdN
# PpA's and PpB's definitions of `2 + 2 = 4`, with different bodies, meet: Lean merges them,
# and the copies agree in every model because the statement is a proposition (task #500)
work_ "two definitions of one proposition with different bodies" 0 "1 flags inferred" "$MSP" PpM --progress
# the merged read compares the private parts, two different definitions: rejected (Lean,
# importing the exported parts, merges the two statements)
case_ "two definitions of one proposition, merged" 1 --olean --search-path=$MSP PpM
# Lean proves False with no axiom here (H's bar.eq_1 reads Q's foo, M holds Q2's):
# rejected, the target verdict
work_ "a captured name" 1 "name capture at foo, read by module DgCapH" "$MSP" DgCapM
# Exports completed on demand (task #501).  DnM1 and DnM2 each export a theorem y : foo = foo
# (the type patched in: Lean writes no exported statement reading a privately imported name),
# foo dangling in each export, DgCapQ's in DnM1's and DgCapQ2's in DnM2's.  DnH loads both y,
# which merge as two theorems of one statement; completing both exports gives two foo, which
# clash: rejected.  Lean, importing the files, completes nothing and merges the two y (it then
# refuses DnH's own z, elaborated against y : True); a completing Lean would refuse the two foo.
d="$TMPDIR/con-leche-olean-dangling"
rm -rf "$d"; cp -r "$LIB" "$d"
for k in 1 2; do
  xpatch "$d" DnM$k "K='$k'
# Each new object goes at the end of its part, after everything it points to (the reader
# asks a child to come before its parent): the type foo = foo, then y's chain up to a new
# root (ConstantVal, its theorem or axiom value, the ConstantInfo, the constants array, the
# ModuleData), the header's root pointer moved to it.
def obj(a):
    bb, o = at(a)
    if bb[o + 7] == 246:  # an array: its header, size, capacity, elements
        return bytes(bb[o:o + 24 + 8 * struct.unpack_from('<Q', bb, o + 16)[0]])
    return bytes(bb[o:o + struct.unpack_from('<H', bb, o + 4)[0]])
def clone(ext, a, i, v, arr=False):
    base, bb = parts[ext]; n = base + len(bb); bb.extend(obj(a))
    if arr: struct.pack_into('<Q', bb, n - base + 24 + 8 * i, v)
    else: setfld(n, i, v)
    return n
for ext in ['olean', 'olean.private']:
    base, bb = parts[ext]
    root = struct.unpack_from('<Q', bb, 88)[0]
    cs = consts(ext)
    eq = next(c for n, c in cs.items() if n.endswith('.bar' + K + '.eq_1'))
    t = fld(fld(fld(eq, 0), 0), 2)
    foo = fld(t, 1)
    n1 = clone(ext, fld(t, 0), 1, foo)
    n2 = clone(ext, t, 0, n1)
    y = cs['y']
    cv = clone(ext, fld(fld(y, 0), 0), 2, n2)
    val = clone(ext, fld(y, 0), 0, cv)
    ci = clone(ext, y, 0, val)
    arr = fld(root, 2)
    ab, ao = at(arr)
    k = next(j for j in range(struct.unpack_from('<Q', ab, ao + 8)[0])
             if struct.unpack_from('<Q', ab, ao + 24 + 8 * j)[0] == y)
    arr2 = clone(ext, arr, k, ci, arr=True)
    root2 = clone(ext, root, 2, arr2)
    struct.pack_into('<Q', bb, 88, root2)
"
done
work_ "two copies of a theorem whose exports complete to different names" 1 \
  "name capture at foo, read by module DnM2" "$d:$INIT" DnH
rm -rf "$d"
# A definition and a theorem of one statement meet through a home's view (task #506).  TdH
# loads TdB privately, so the `td` its exported `tdn.eq_1` reads is dangling in its export;
# the gate patches TdH's exported theorem `ty` to `(fun _ => True) td` (Lean writes no
# exported statement reading a privately imported name), still True by β.  TdM loads TdA's
# definition `td` and reads `ty`; TdH's view locates `td` as TdB's theorem: two proofs of
# `id True`, which `isPropCheap` does not see as a proposition.  One copy is a theorem, so they
# agree with no inference.  Lean, importing the patched files, compares nothing: it never loads
# TdB's `td` at TdM (it refuses the pair loaded together, PdN).
d="$TMPDIR/con-leche-olean-thmdef"
rm -rf "$d"; cp -r "$LIB" "$d"
xpatch "$d" TdH "
def obj(a):
    bb, o = at(a)
    if bb[o + 7] == 246:
        return bytes(bb[o:o + 24 + 8 * struct.unpack_from('<Q', bb, o + 16)[0]])
    return bytes(bb[o:o + struct.unpack_from('<H', bb, o + 4)[0]])
def clone(ext, a, i, v, arr=False):
    base, bb = parts[ext]; n = base + len(bb); bb.extend(obj(a))
    if arr: struct.pack_into('<Q', bb, n - base + 24 + 8 * i, v)
    else: setfld(n, i, v)
    return n
for ext in ['olean', 'olean.private']:
    base, bb = parts[ext]
    root = struct.unpack_from('<Q', bb, 88)[0]
    cs = consts(ext)
    eq = next(c for n, c in cs.items() if n.endswith('tdn.eq_1'))
    t = fld(fld(fld(eq, 0), 0), 2)
    rhs = fld(t, 1)
    y = cs['ty']
    tru = fld(fld(fld(y, 0), 0), 2)
    lam = clone(ext, fld(rhs, 0), 2, tru)
    n2 = clone(ext, rhs, 0, lam)
    cv = clone(ext, fld(fld(y, 0), 0), 2, n2)
    val = clone(ext, fld(y, 0), 0, cv)
    ci = clone(ext, y, 0, val)
    arr = fld(root, 2)
    ab, ao = at(arr)
    k = next(j for j in range(struct.unpack_from('<Q', ab, ao + 8)[0])
             if struct.unpack_from('<Q', ab, ao + 24 + 8 * j)[0] == y)
    arr2 = clone(ext, arr, k, ci, arr=True)
    root2 = clone(ext, root, 2, arr2)
    struct.pack_into('<Q', bb, 88, root2)
"
work_ "a definition and a theorem of one statement meet in a home's view" 0 \
  "0 flags inferred" "$d:$INIT" TdM --progress
rm -rf "$d"
# A group's stored names (task #501): GbG's exported part without S.rec (no other name of the
# group reads it; Lean's exported parts need not hold every recursor), and GbG2's S.rec, which
# GbG2's exposed w reads.  GbH reaches S's group first, which stores S.rec, then w: the context
# reads S.rec from GbG2, and the group stores GbG's: rejected.  Lean, which loads no S.rec of
# GbG at GbH, accepts the module; the shape is one Lean never writes.
d="$TMPDIR/con-leche-olean-stored"
rm -rf "$d"; cp -r "$LIB" "$d"
xpatch "$d" GbG "
# Drop S.mk from GbG's exported part: new name and constant arrays without it (the last entry
# moved to its slot), and a new ModuleData pointing at them, each after what it points to.
def obj(a):
    bb, o = at(a)
    if bb[o + 7] == 246:
        return bytes(bb[o:o + 24 + 8 * struct.unpack_from('<Q', bb, o + 16)[0]])
    return bytes(bb[o:o + struct.unpack_from('<H', bb, o + 4)[0]])
def drop(ext, arr, k):
    base, bb = parts[ext]; n = base + len(bb); bb.extend(obj(arr)); o = n - base
    sz = struct.unpack_from('<Q', bb, o + 8)[0]
    struct.pack_into('<Q', bb, o + 24 + 8 * k, struct.unpack_from('<Q', bb, o + 24 + 8 * (sz - 1))[0])
    struct.pack_into('<Q', bb, o + 8, sz - 1)
    return n
ext = 'olean'
base, bb = parts[ext]
root = struct.unpack_from('<Q', bb, 88)[0]
cs = consts(ext)
mk = cs[\"S.rec\"]
ab, ao = at(fld(root, 2))
k = next(j for j in range(struct.unpack_from('<Q', ab, ao + 8)[0])
         if struct.unpack_from('<Q', ab, ao + 24 + 8 * j)[0] == mk)
names2 = drop(ext, fld(root, 1), k)
consts2 = drop(ext, fld(root, 2), k)
root2 = base + len(bb); bb.extend(obj(root)); setfld(root2, 1, names2); setfld(root2, 2, consts2)
struct.pack_into('<Q', bb, 88, root2)
"
work_ "a group's name the importer loads from another module" 1 \
  "a record read from module GbG stores S.rec, which the context reads from module GbG2" "$d:$INIT" GbH
# The reader's copy of a name unsafe (task #502, `agreeCheck`).  UfH's exported hz reads GbG's S
# and S.rec; with S.rec dropped from GbG's exported part, hz's read of S.rec is stored with S's
# group.  UfH holds an unsafe axiom in its private part, which the gate renames to S.rec (a safe
# theorem reading it: Lean's kernel refuses that, so Lean never writes this shape).  UfH's own
# worker accepts (hz is its own record).  UfM, which loads UfT's safe axiom S.rec and uses hz,
# passes hz's read of S.rec against UfH's copy of it: rejected, the copy is unsafe.  Lean, which
# imports the patched files of a module-system file (UfM, UfH, UfT, GbG) without a complaint,
# re-checks none of them and reads S.rec as UfT's; it never writes this shape.  The parent of the
# check rejects UfM earlier, "two context records store a name of S's record".
xpatch "$d" UfH "
ext = 'olean.private'
base, bb = parts[ext]
root = struct.unpack_from('<Q', bb, 88)[0]
cs = consts(ext)
# the name object S.rec, from hz's type
def find(e, seen):
    if e & 1 or e in seen: return None
    seen.add(e)
    b0, o0 = at(e)
    if b0[o0 + 7] == 4 and name(fld(e, 0)) == 'S.rec': return fld(e, 0)
    for i in range(b0[o0 + 6]):
        r = find(fld(e, i), seen)
        if r: return r
    return None
tgt = find(fld(fld(fld(cs['hz'], 0), 0), 2), set())
u = next(c for n, c in cs.items() if n.endswith('.u'))
cv = fld(fld(u, 0), 0)
old = fld(cv, 0)
setfld(cv, 0, tgt)
ab, ao = at(fld(root, 1))
for j in range(struct.unpack_from('<Q', ab, ao + 8)[0]):
    if struct.unpack_from('<Q', ab, ao + 24 + 8 * j)[0] == old:
        struct.pack_into('<Q', ab, ao + 24 + 8 * j, tgt)
"
work_ "the worker at UfH, which holds an unsafe S.rec" 0 "accepted" "$d:$INIT" UfH
work_ "a reader's copy of a name unsafe" 1 \
  "name capture at S.rec, read by module UfH: its copy of S.rec, of module UfH, is unsafe or partial" "$d:$INIT" UfM
rm -rf "$d"
# an axiom at a certified Nat operation's name (Lean accepts the module): its own
# record is rejected, as on the merged read (the fast path's names it reads are
# left to that record's check)
work_ "an axiom at a certified Nat operation's name" 1 "not a definition: Nat.div" "$LIB" NpAx
# two axioms of one propositional statement meet: the flag inferred; an axiom of a
# proposition and a theorem meet: no inference (task #506); Lean merges both
work_ "two axioms of one propositional statement meet" 0 "1 flags inferred" "$MSP" AxM --progress
work_ "an axiom of a proposition meets a theorem" 0 "0 flags inferred" "$MSP" AxIM --progress
for m in AxA AxB AxIT AxNM; do work_ "the worker at $m" 0 "accepted" "$MSP" $m; done
# QsA's and QsB's `axiom Quot.sound`, over QsP's quotient, meet at QsM (Lean merges the two
# axioms); QsM's context reads QsB's theorem, whose read of `Quot.sound` is QsB's own copy, a
# proof pair with the context's (QsA's): every worker accepts (task #501)
for m in QsP QsA QsB QsM; do work_ "the worker at $m" 0 "accepted" "$LIB" $m; done
# the toolchain's homes of certified Nat operations (Nat.gcd; Nat.land, Nat.lor, Nat.xor,
# Nat.shiftLeft, Nat.shiftRight): their pins' and certificates' constants are reached, so
# their install checks find them (exit 2 before task #446)
for m in Init.Data.Nat.Gcd Init.Data.Nat.Bitwise.Basic; do
  work_ "the worker at $m" 0 "accepted" "$INIT" $m
done
# a module declaring a user axiom: declined at its record, as on the merged read
# (Lean accepts it)
for m in AxI AxNA AxNB AxNX; do
  work_ "a user axiom at its home ($m)" 2 "non-standard axiom" "$MSP" $m
done
# the modules Lean refuses to compile, their files swapped in (as for --reads)
d="$TMPDIR/con-leche-olean-worker"
rm -rf "$d"; cp -r "$LIB" "$d"
swap_ "$d" ClashX ClashB
work_ "two different constants of one name loaded together" 1 "store different constants named clash" "$d" ClashM
swap_ "$d" TeqX TeqQ2
work_ "two theorems of one name and two statements loaded together" 1 "store different constants named teq" "$d:$INIT" TeqBad
swap_ "$d" FrX FrY
work_ "a module declaring a loaded name" 1 "declares fresh, which the module FrX" "$d" FrM
swap_ "$d" MoX TinyClassic
work_ "a module importing one outside the module system" 1 "imports MoX, which is not" "$d" MoM
rm -rf "$d"
# a group's constructor reading a name N's view lacks (the import made private):
# completed; with the import dropped, located nowhere
for a in Ldg Ldv; do
  rm -rf "$d"; cp -r "$LIB" "$d"
  patch_import "$d/${a}A.olean" private
  work_ "a group's read completed ($a)" 0 "1 completed" "$d:$INIT" ${a}N --progress
  rm -rf "$d"; cp -r "$LIB" "$d"
  patch_import "$d/${a}A.olean" drop
  work_ "a group's read located nowhere ($a)" 1 "which no module of its view holds" "$d:$INIT" ${a}N
done
rm -rf "$d"
# the usage: one module, no --constant, under --olean
case_ "--module takes one module" 3 --olean --module --search-path=$LIB Tiny TinyUse
case_ "--module takes no --constant" 3 --olean --module --constant=two --search-path=$LIB Tiny
case_ "--module takes --olean" 3 --module --search-path=$LIB Tiny

# --- every module of a closure: in one process, and one worker process each ---
# (task #468: `--modular` runs each module's worker steps over tables read once; the
# scheduler `--schedule` runs one `--module` process per module.  Same verdicts as the
# workers': exit 0 iff every module's is 0, else the first failing module in the graph's
# order is named, with its code)
for m in TinyUse NlM PdM WvM LvN; do
  case_grep "--modular at $m" 0 "accepted .* modules" --olean --modular --search-path=$MSP -- $m
done
case_grep "--modular at Init.Data.Nat.Gcd" 0 "accepted .* modules" --olean --modular \
  --search-path=$INIT -- Init.Data.Nat.Gcd
case_grep "--modular: a module's verdict named" 0 "module NlX: accepted" --olean --modular \
  --search-path=$MSP -- NlM
case_grep "--modular: the first failing module, its code" 1 "the first in the graph's order: NpAx" \
  --olean --modular --search-path=$LIB -- NpAx
case_grep "--modular at one job" 0 "accepted 4 modules" --jobs=1 --olean --modular \
  --search-path=$MSP -- PdM
case_ "--modular takes one module" 3 --olean --modular --search-path=$LIB Tiny TinyUse
case_ "--modular takes no --module" 3 --olean --modular --module --search-path=$LIB Tiny
case_ "--modular takes --olean" 3 --modular --search-path=$LIB Tiny
case_grep "--modular: a missing import" 1 "no .olean on the search path" --olean --modular \
  --search-path=$LIB -- NlM
d="$TMPDIR/olean-sched"
rm -rf "$d"; mkdir -p "$d"
case_grep "--schedule: one worker per module" 0 "accepted 5 modules, one worker each" --olean \
  --schedule --schedule-log="$d/log" --jobs=2 --search-path=$MSP -- NlM
case_grep "--schedule: the log resumed" 0 "5 modules logged, 0 to run" --olean \
  --schedule --schedule-log="$d/log" --jobs=2 --search-path=$MSP -- NlM
case_grep "--schedule: the first failing module, its code" 1 "the first in the graph's order: NpAx (1)" \
  --olean --schedule --search-path=$LIB -- NpAx
# (task #563: a non-zero finish line is marked FAILED, an accepted one shows no verdict)
case_grep "--schedule: a failing module's finish line" 1 "s .*FAILED 1  NpAx" \
  --olean --schedule --search-path=$LIB -- NpAx
# (task #569: a worker that overflows its thread stack is `stack`, not an anonymous signal; the
# log holds the stack size, and a resumed run retries the module only at another size.
# StackDeep needs a deeper stack than 1 MiB; the default 1 GiB takes it)
case_ "--schedule: a deep module at the default stack" 0 --olean --schedule --search-path=$LIB -- StackDeep
export LEAN_STACK_SIZE_KB=1024
case_grep "--schedule: a stack overflow is the verdict stack" 3 "FAILED stack  StackDeep" --olean \
  --schedule --schedule-log="$d/stack" --search-path=$LIB -- StackDeep
case_grep "--schedule: …with the hint" 3 "rerun with a larger LEAN_STACK_SIZE_KB" --olean \
  --schedule --schedule-log="$d/stack2" --search-path=$LIB -- StackDeep
total=$((total+1))
if grep -qP "^stack\t«StackDeep»\t.*\t1024$" "$d/stack"; then ok=$((ok+1))
else echo "OLEAN FAIL (--schedule: the stack log line)"; fail=1; fi
case_grep "--schedule: a stack verdict resumed at the same size" 3 "1 modules logged, 0 to run" --olean \
  --schedule --schedule-log="$d/stack" --search-path=$LIB -- StackDeep
export LEAN_STACK_SIZE_KB=2048
case_grep "--schedule: …retried at another size" 3 "FAILED stack  StackDeep" --olean \
  --schedule --schedule-log="$d/stack" --search-path=$LIB -- StackDeep
unset LEAN_STACK_SIZE_KB
case_ "--schedule: an unknown option" 3 --olean --schedule-frobnicate --search-path=$LIB -- Tiny
# (task #505: the module lines carry the counts; a budget takes a unit; a heartbeat in ms or s)
case_grep "--schedule: the last module's line, its counts" 0 "\[4 (100.0%)  0 wrkr" \
  --olean --schedule --schedule-memory=40G --progress=1000 --jobs=2 --search-path=$MSP -- PdM
case_grep "--schedule-memory: a bare number is no size" 3 "takes a size with a unit" --olean \
  --schedule --schedule-memory=6000 --search-path=$LIB -- Tiny
case_ "--schedule-memory: 512M" 0 --olean --schedule --schedule-memory=512M --search-path=$LIB \
  -- Tiny
case_grep "--schedule takes no --progress percentage" 3 "not a percentage" --olean --schedule \
  --progress=5% --search-path=$LIB -- Tiny
case_ "--schedule takes no --modular" 3 --olean --schedule --modular --search-path=$LIB -- Tiny
# (task #596: `--schedule-commands` starts nothing and prints the commands that check the
# closure: the graph check, then one `--module` run per module, shell-quoted; NlM's closure is
# five modules, so six lines; no `--jobs` unless given; nothing on stderr)
case_ "--schedule-commands: the commands" 0 --olean --schedule-commands --schedule-log="$d/nolog" \
  --search-path=$MSP -- NlM
total=$((total+1))
if [ "$(wc -l < "$TMPDIR/olean-case.out")" = 6 ] &&
   head -1 "$TMPDIR/olean-case.out" | grep -qE "^/[^ ]*con-leche --check-graph --search-path=[^ ]+ -- '«NlM»'$" &&
   sed -n 2p "$TMPDIR/olean-case.out" | grep -qE "^/[^ ]*con-leche --olean --module --verified --max-nat-size=[0-9]+ --search-path=[^ ]+ -- '«[A-Za-z.«»]+»'$" &&
   [ ! -e "$d/nolog" ]; then ok=$((ok+1))
else echo "OLEAN FAIL (--schedule-commands: six lines, the graph check first)"; fail=1; fi
case_grep "--schedule-commands: --jobs where given" 0 "^/.* --module --jobs=3 " --olean \
  --schedule-commands --jobs=3 --search-path=$MSP -- NlM
rm -rf "$d"

rm -f "$TMPDIR/olean-case.out"
# --- a challenge and its solution (--compare, task #607) ---------------------
# holes: the challenge module's own axioms and sorry declarations, met by the solution's
# constant of the name and type (up to level-parameter names), of any kind
cmp_case() { case_ "compare: $1" "$2" --olean --compare --search-path=$MSP -- "${@:3}"; }
cmp_grep() { case_grep "compare: $1" "$2" "$3" --olean --compare --search-path=$MSP -- "${@:4}"; }
cmp_grep "theorem holes filled" 0 "hole g_eq (theorem := sorry) filled by CmpSol's theorem" CmpChal CmpSol
cmp_grep "a definition that differs" 1 "g: the solution's definition differs" CmpChal CmpSolDef
cmp_grep "a hole stated differently" 1 "g_eq: the solution's theorem is not of the hole's type" CmpChal CmpSolStmt
cmp_grep "a constant the solution lacks" 1 "easy: the solution has no constant of this name" CmpChal CmpSolMissing
# the solution's check declines sorry, as every --olean run does
cmp_case "a solution that uses sorry" 2 CmpChal CmpSolSorry
cmp_grep "definition and opaque holes filled" 0 "hole answer (definition := sorry) filled by CmpOpqSol's definition" CmpOpq CmpOpqSol
cmp_grep "an opaque constant of another value" 1 "k: the solution's opaque constant differs" CmpOpq CmpOpqSolK
cmp_grep "an axiom hole filled by a theorem" 0 "hole ax (axiom) filled by CmpAxS's theorem" CmpAxC CmpAxS
# a non-standard axiom at the hole's name: the solution's check declines it, as always
cmp_case "a solution axiom at a hole's name" 2 CmpAxC CmpAxBadS
# a hole filled by an inductive type: not supported yet, declined
cmp_grep "a hole filled by an inductive type" 2 "T: the solution fills this hole with an inductive type" CmpIndC CmpIndS
cmp_grep "level parameters named otherwise" 0 "hole h (axiom) filled by CmpLvS's theorem" CmpLvC CmpLvS
cmp_grep "binders named otherwise" 0 "hole gt (theorem := sorry) filled by CmpBndS's theorem" CmpBndC CmpBndS
# holes con-leche cannot fill (declines; the target verdicts: Quot.sound and sorryAx filled by
# the same axiom accepted, once the comparison carries their pin copies; a definition at a
# compiler-trust name rejected, as the solution's own check rejects it)
cmp_grep "a hole at Quot.sound" 2 "declined: Quot.sound: a hole at the quotient's axiom" QsA QsB
cmp_grep "a hole at sorryAx" 2 "declined: sorryAx: a hole at the placeholder axiom" CmpSorryC CmpSorryS
cmp_grep "a compiler-trust hole filled by a definition" 2 \
  "declined: Lean.reduceBool: the solution fills this hole at a compiler-trust name with a definition" \
  CmpTrustC CmpTrustS
cmp_grep "a definition hole filled by an opaque constant" 0 "filled by UpKindDefOpqSol's opaque constant" UpKindDef UpKindDefOpqSol
cmp_grep "a theorem hole filled by a definition" 0 "filled by UpKindThmDefSol's definition" UpKindThm UpKindThmDefSol
cmp_grep "a hole filled by an imported definition" 0 "hole n (definition := sorry) filled by UpHidDef's definition" UpKindDef UpHidDefSol
# imported names are their home's: never compared by content
cmp_grep "an imported name declared by the solution" 1 "f: the challenge reads it from CmpHomeA, the solution's is CmpHomeS1's" CmpHomeC CmpHomeS1
cmp_grep "an imported name redeclared with its body" 1 "f: the challenge reads it from CmpHomeA, the solution's is CmpHomeS2's" CmpHomeC3 CmpHomeS2
cmp_grep "an imported name read from its home" 0 "hole t (theorem := sorry) filled by CmpHomeS3's theorem" CmpHomeC3 CmpHomeS3
# the ported upstream pairs (comparator's test suite)
cmp_grep "upstream simple-match" 0 "hole comm (theorem := sorry) filled by UpCommSol's theorem" UpComm UpCommSol
cmp_case "upstream simple-axiom-issue" 2 UpComm UpCommAxSol
cmp_grep "upstream simple-mismatch" 1 "comm: the solution's axiom is not of the hole's type" UpComm UpCommMisSol
cmp_grep "upstream def-hole" 0 "hole n (definition := sorry) filled by UpDefHoleSol's definition" UpDefHole UpDefHoleSol
cmp_case "upstream def-hole-axiom-issue" 2 UpDefHole UpDefHoleAxSol
cmp_case "upstream def-hole-kind-mismatch" 2 UpDefHole UpDefHoleKindSol
cmp_grep "upstream def-hole-type-mismatch" 1 "n: the solution's definition is not of the hole's type" UpDefHoleTy UpDefHoleTySol
cmp_grep "upstream numeric-namespace" 0 "hole «123».foo" 'UpNum.«12.34».«5»' UpNumSol
cmp_case "upstream opaque-value" 2 UpBoom UpBoomOpqSol
# (the solution imports less of Init than the challenge: a constant it lacks)
cmp_grep "upstream primitive-issue" 1 "the solution has no constant of this name" UpGcd UpGcdSol
cmp_grep "upstream proj_trick" 1 "S: the solution's inductive type differs" UpProj UpProjSol
cmp_case "upstream quot_mismatch" 1 UpQuot UpQuotSol
cmp_grep "upstream theorem_hole_issue" 0 "hole hw (theorem := sorry) filled by UpThmHoleSol's theorem" UpThmHole UpThmHoleSol
cmp_grep "upstream check-multi as a comparison" 1 "a_thm: the solution has no constant of this name" UpMultiA UpMultiB
# a solution importing its challenge is invalid input, as the modular run's cycle (task #608)
cmp_grep "a solution importing its challenge" 1 "the solution's closure holds the challenge" CmpChal CmpImpS
# --constant: declarations of the challenge module itself; the cone alone compared
case_grep "compare: --constant at a challenge declaration" 0 "hole foo (theorem := sorry)" \
  --olean --compare --constant=foo --search-path=$MSP -- UpDefHole UpDefHoleSol
case_grep "compare: --constant at an imported name" 1 \
  "--constant=Nat.add: not a declaration of the challenge module UpDefHole" \
  --olean --compare --constant=Nat.add --search-path=$MSP -- UpDefHole UpDefHoleSol
case_ "compare: a module compared with itself" 3 --olean --compare --search-path=$MSP -- CmpChal CmpChal
case_ "compare: one module name only" 3 --olean --compare --search-path=$MSP -- CmpChal
case_ "compare: --trusted-search-path without --compare" 3 --olean --trusted-search-path=$MSP -- CmpChal
# the trusted path: the challenge and its imports read from it alone
TRU="$TMPDIR/cmp-trusted"; BAD="$TMPDIR/cmp-bad"
rm -rf "$TRU" "$BAD"; mkdir -p "$TRU" "$BAD"
for f in "$LIB"/*; do case $(basename "$f") in CmpHomeA.*) ;; *) ln -s "$PWD/$f" "$TRU/";; esac; done
cp "$LIB"/CmpHomeA.* "$BAD/"
printf 'not an olean' > "$BAD/CmpHomeA.olean"
cp "$LIB"/CmpHomeC3.* "$BAD/"; printf 'not an olean' > "$BAD/CmpHomeC3.olean"
case_grep "compare: a challenge module only on the search path" 1 \
  "the challenge's module CmpHomeA is not on the trusted path" \
  --olean --compare --trusted-search-path=$TRU:$INIT --search-path=$LIB -- CmpHomeC3 CmpHomeS3
# the solution's module, only on the search path, read from it
cp -r "$TRU" "$TMPDIR/cmp-trusted2"; rm -f "$TMPDIR/cmp-trusted2"/CmpHomeS3.*; ln -s "$PWD/$LIB"/CmpHomeA.* "$TMPDIR/cmp-trusted2/"
case_ "compare: the solution read from the search path" 0 \
  --olean --compare --trusted-search-path=$TMPDIR/cmp-trusted2:$INIT --search-path=$LIB -- CmpHomeC3 CmpHomeS3
# a module in both paths is the trusted one: corrupted copies on the search path are never read
case_ "compare: the trusted path shadows the search path" 0 \
  --olean --compare --trusted-search-path=$LIB:$INIT --search-path=$BAD -- CmpHomeC3 CmpHomeS3
# locality: what is outside the trusted path does not change the verdict on the challenge
case_ "compare: the verdict without the search path" 0 \
  --olean --compare --trusted-search-path=$LIB:$INIT -- CmpHomeC3 CmpHomeS3
case_ "compare: the verdict with a corrupted search path" 1 \
  --olean --compare --trusted-search-path=$LIB:$INIT --search-path=$BAD -- CmpHomeC CmpHomeS1
case_ "compare: …and without it" 1 \
  --olean --compare --trusted-search-path=$LIB:$INIT -- CmpHomeC CmpHomeS1
rm -rf "$TRU" "$TMPDIR/cmp-trusted2" "$BAD"

# --- the challenge as one module of a modular run (task #608) ----------------
# `--schedule --compare`: the graph with the challenge's added import of its solution, a worker
# per module of the two closures but the challenge, and the compare worker at the challenge;
# the same verdicts as the merged comparison; `--modular --compare` is the same run in one
# process.  The compare worker alone: its own verdict and line (0 where only a worker of the
# solution's closure refuses).
mcmp() { # <description> <run's exit> <compare worker's exit> <its line's pattern> <C> <S>
  case_ "modular compare: $1" "$2" --olean --schedule --compare --jobs=2 --search-path=$MSP -- "$5" "$6"
  case_ "modular compare: $1 (one process)" "$2" \
    --olean --modular --compare --jobs=2 --search-path=$MSP -- "$5" "$6"
  case_grep "modular compare: $1 (the compare worker)" "$3" "$4" \
    --olean --module --compare --search-path=$MSP -- "$5" "$6"
}
mcmp "theorem holes filled" 0 0 "hole g_eq (theorem := sorry) filled by CmpSol's theorem" CmpChal CmpSol
mcmp "a definition that differs" 1 1 "g: the solution's definition differs" CmpChal CmpSolDef
mcmp "a hole stated differently" 1 1 "g_eq: the solution's theorem is not of the hole's type" CmpChal CmpSolStmt
mcmp "a constant the solution lacks" 1 1 "easy: the solution has no constant of this name" CmpChal CmpSolMissing
mcmp "a solution that uses sorry" 2 0 "hole easy (theorem := sorry) filled by CmpSolSorry's theorem" CmpChal CmpSolSorry
mcmp "definition and opaque holes filled" 0 0 "hole answer (definition := sorry) filled by CmpOpqSol's definition" CmpOpq CmpOpqSol
mcmp "an opaque constant of another value" 1 1 "k: the solution's opaque constant differs" CmpOpq CmpOpqSolK
mcmp "an axiom hole filled by a theorem" 0 0 "hole ax (axiom) filled by CmpAxS's theorem" CmpAxC CmpAxS
mcmp "a solution axiom at a hole's name" 2 0 "hole ax (axiom) filled by CmpAxBadS's axiom" CmpAxC CmpAxBadS
mcmp "a hole filled by an inductive type" 2 2 "T: the solution fills this hole with an inductive type" CmpIndC CmpIndS
mcmp "level parameters named otherwise" 0 0 "hole h (axiom) filled by CmpLvS's theorem" CmpLvC CmpLvS
mcmp "binders named otherwise" 0 0 "hole gt (theorem := sorry) filled by CmpBndS's theorem" CmpBndC CmpBndS
mcmp "a hole at Quot.sound" 2 2 "declined: Quot.sound: a hole at the quotient's axiom" QsA QsB
mcmp "a hole at sorryAx" 2 2 "a context record reads sorryAx" CmpSorryC CmpSorryS
mcmp "a compiler-trust hole filled by a definition" 2 2 \
  "declined: Lean.reduceBool: the solution fills this hole at a compiler-trust name with a definition" \
  CmpTrustC CmpTrustS
mcmp "a definition hole filled by an opaque constant" 0 0 "filled by UpKindDefOpqSol's opaque constant" UpKindDef UpKindDefOpqSol
mcmp "a theorem hole filled by a definition" 0 0 "filled by UpKindThmDefSol's definition" UpKindThm UpKindThmDefSol
mcmp "a hole filled by an imported definition" 0 0 "hole n (definition := sorry) filled by UpHidDef's definition" UpKindDef UpHidDefSol
# imported names are their home's: the solution's own `f` is loaded beside the home's
mcmp "an imported name declared by the solution" 1 1 "modules CmpHomeA and CmpHomeS1 store different constants named f" CmpHomeC CmpHomeS1
mcmp "an imported name redeclared with its body" 1 1 "modules CmpHomeA and CmpHomeS2 store different constants named f" CmpHomeC3 CmpHomeS2
mcmp "an imported name read from its home" 0 0 "hole t (theorem := sorry) filled by CmpHomeS3's theorem" CmpHomeC3 CmpHomeS3
mcmp "a solution importing its challenge" 1 1 "the solution's closure holds the challenge" CmpChal CmpImpS
mcmp "upstream simple-match" 0 0 "hole comm (theorem := sorry) filled by UpCommSol's theorem" UpComm UpCommSol
mcmp "upstream simple-axiom-issue" 2 0 "hole comm (theorem := sorry) filled by UpCommAxSol's theorem" UpComm UpCommAxSol
mcmp "upstream simple-mismatch" 1 1 "comm: the solution's axiom is not of the hole's type" UpComm UpCommMisSol
mcmp "upstream def-hole" 0 0 "hole n (definition := sorry) filled by UpDefHoleSol's definition" UpDefHole UpDefHoleSol
mcmp "upstream def-hole-axiom-issue" 2 2 "a context record reads sorryAx" UpDefHole UpDefHoleAxSol
mcmp "upstream def-hole-kind-mismatch" 2 0 "hole n (definition := sorry) filled by UpDefHoleKindSol" UpDefHole UpDefHoleKindSol
mcmp "upstream def-hole-type-mismatch" 1 1 "n: the solution's definition is not of the hole's type" UpDefHoleTy UpDefHoleTySol
mcmp "upstream numeric-namespace" 0 0 "hole «123».foo" 'UpNum.«12.34».«5»' UpNumSol
mcmp "upstream opaque-value" 2 0 "hole boom (theorem := sorry) filled by UpBoomOpqSol's theorem" UpBoom UpBoomOpqSol
mcmp "upstream primitive-issue" 1 1 "store different constants named Nat.gcd" UpGcd UpGcdSol
mcmp "upstream proj_trick" 1 1 "S: the solution's inductive type differs" UpProj UpProjSol
mcmp "upstream quot_mismatch" 1 1 "reads Nat.pred, which no module it loads holds" UpQuot UpQuotSol
mcmp "upstream theorem_hole_issue" 0 0 "hole hw (theorem := sorry) filled by UpThmHoleSol's theorem" UpThmHole UpThmHoleSol
mcmp "upstream check-multi as a comparison" 1 1 "a_thm: the solution has no constant of this name" UpMultiA UpMultiB
case_grep "modular compare: the graph with the solution added" 0 "acyclic: 4 modules, 4 import edges" \
  --check-graph --compare --search-path=$MSP -- CmpChal CmpSol
case_grep "modular compare: the graph of a solution importing its challenge" 1 \
  "import cycle: CmpChal → CmpImpS → CmpChal" --check-graph --compare --search-path=$MSP -- CmpChal CmpImpS
case_grep "modular compare: the commands" 0 "check-graph --compare --search-path=" \
  --olean --schedule-commands --compare --search-path=$MSP -- CmpChal CmpSol
case_grep "modular compare: the commands' compare worker" 0 "module --compare --verified --search-path=.* -- '«CmpChal»' '«CmpSol»'" \
  --olean --schedule-commands --compare --search-path=$MSP -- CmpChal CmpSol
case_ "modular compare: --check-graph with one module" 3 --check-graph --compare --search-path=$MSP -- CmpChal
case_ "modular compare: --check-graph with the module twice" 3 --check-graph --compare --search-path=$MSP -- CmpChal CmpChal
case_ "modular compare: --module with one module" 3 --olean --module --compare --search-path=$MSP -- CmpChal
case_ "modular compare: --modular and --module" 3 --olean --modular --module --compare --search-path=$MSP -- CmpChal CmpSol
case_ "modular compare: --modular and --schedule" 3 --olean --modular --schedule --compare --search-path=$MSP -- CmpChal CmpSol
case_ "modular compare: --trusted-search-path" 3 --olean --modular --compare --trusted-search-path=$MSP --search-path=$MSP -- CmpChal CmpSol
case_ "modular compare: --module and --schedule" 3 --olean --module --schedule --compare --search-path=$MSP -- CmpChal CmpSol
case_ "modular compare: --constant" 3 --olean --module --compare --constant=g --search-path=$MSP -- CmpChal CmpSol

echo "olean gate: $ok/$total as expected"
exit $fail
