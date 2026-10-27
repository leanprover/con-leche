#!/usr/bin/env bash
# THE OLEAN GATE: `con-leche --olean` on the committed fixtures of
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

# --- well-formed closures ---------------------------------------------
case_ "a module-system module" 0 --olean --search-path=$LIB Tiny
case_ "…at one worker" 0 --jobs=1 --olean --search-path=$LIB Tiny
case_ "a module outside the module system (one .olean)" 0 --olean --search-path=$LIB TinyClassic
case_ "a module and its import" 0 --olean --search-path=$LIB TinyUse
case_ "two roots" 0 --olean --search-path=$LIB TinyUse TinyClassic
case_ "a search path of two directories" 0 --olean --search-path=$TMPDIR:$LIB TinyUse
# two modules storing different constants under one name: Lean's own
# import refuses the pair ("environment already contains"), and so does
# the merge (a reject: the input says two contradicting things)
case_ "conflicting constants in two modules" 1 --olean --search-path=$LIB ClashA ClashB

# --- usage --------------------------------------------------------------
case_ "--olean without a search path" 3 --olean Tiny
case_ "--olean without a module" 3 --olean --search-path=$LIB
case_ "--search-path without --olean" 3 --search-path=$LIB tests/mode/split_good.ndjson
case_ "a module not on the search path" 3 --olean --search-path=$LIB NoSuchModule

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
corrupt "another toolchain's githash: a decline" 2 Tiny.olean "b[40:48] = b'00000000'"
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

rm -f "$TMPDIR/olean-case.out"
echo "olean gate: $ok/$total as expected"
exit $fail
