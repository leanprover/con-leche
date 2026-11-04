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
views_() { # <description> <expected-exit> <pattern> <search path> <module>: a home's read
  total=$((total+1))
  timeout 60 "$CMP" --views "$4" "$5" >"$TMPDIR/olean-case.out" 2>&1
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
views_ "a home's read: all three views agree with each view's read" 0 "agrees" "$LIB" TinyUse
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
# any axiom but the three is declined
case_grep "an axiom at a certified Nat operation's name" 2 "non-standard axiom (Nat.div)" --olean --search-path=$LIB NpAx
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
    pre = name(fld(a, 0)); b, s = at(fld(a, 1))
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
home_rejects() { # <description> <pattern> <search path> <module>
  case_ "$1 [--olean, the private view]" 0 --olean --search-path=$3 "$4"
  views_ "$1 [a home's read]" 3 "$2" "$3" "$4"
}
d="$TMPDIR/con-leche-olean-home"
rm -rf "$d"; cp -r "$LIB" "$d"; patch "$d/Tiny.olean" "$cswap"
home_rejects "a name table that names the constants differently (exported part)" "name table" "$d" Tiny
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
home_rejects "a private part outside the module system" "not of a module of the module system" "$d" Tiny
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
  home_rejects "an exported constant that is not its private one" "not a refinement" "$d" Tiny
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
  home_rejects "the server part's imports not the exported part's" "imports are not" "$d:$INIT" HidAll
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
# Every module is looked up in every search-path directory: its files
# (M.olean, M.olean.server, M.olean.private) in one location only, up to
# real paths; a module-system module with all three parts; no part
# without its .olean or beside a classic one; no parts split across
# directories.
spd="$TMPDIR/con-leche-olean-sp"
sp_cases() {
  rm -rf "$spd"; mkdir -p "$spd"
  cp -r "$LIB" "$spd/a"; cp -r "$LIB" "$spd/b"
  case_grep "search path: a module in two directories${MOD:+ [$MOD]}" 3 "more than one location" \
    --olean $MOD --search-path=$spd/a:$spd/b TinyUse
  # the copy of one module only (the closure's others found once)
  rm -rf "$spd/b"; mkdir -p "$spd/b"; cp "$LIB"/Tiny.olean* "$spd/b/"
  case_grep "search path: an imported module in two directories${MOD:+ [$MOD]}" 3 "module Tiny: its files are in more than one location" \
    --olean $MOD --search-path=$spd/a:$spd/b TinyUse
  case_ "search path: one directory listed twice${MOD:+ [$MOD]}" 0 \
    --olean $MOD --search-path=$LIB:$LIB TinyUse
  ln -s "$PWD/$LIB" "$spd/link"
  case_ "search path: a directory and a symbolic link to it${MOD:+ [$MOD]}" 0 \
    --olean $MOD --search-path=$spd/link:$LIB TinyUse
  rm -f "$spd/a/Tiny.olean.private"
  case_grep "search path: a missing private part${MOD:+ [$MOD]}" 3 "without its Tiny.olean.private in" \
    --olean $MOD --search-path=$spd/a TinyUse
  rm -rf "$spd/b"; mkdir -p "$spd/b"; cp "$LIB/Tiny.olean.private" "$spd/b/"
  case_grep "search path: parts split across two directories${MOD:+ [$MOD]}" 3 "split across directories" \
    --olean $MOD --search-path=$spd/a:$spd/b TinyUse
  cp "$LIB/Tiny.olean.private" "$spd/a/"; rm -f "$spd/a/Tiny.olean"
  case_grep "search path: parts without their .olean${MOD:+ [$MOD]}" 3 "without Tiny.olean in" \
    --olean $MOD --search-path=$spd/a TinyUse
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
home_rejects "an exported statement of 2^80 nodes as a tree" "not a refinement" "$d" Tiny
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
rm -rf "$g"

rm -f "$TMPDIR/olean-case.out"
echo "olean gate: $ok/$total as expected"
exit $fail
