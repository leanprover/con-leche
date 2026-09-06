#!/usr/bin/env python3
"""Generate a synthetic export stream of N trivial declarations.

    scripts/gen_linear_stream.py N OUT.ndjson

Each declaration is `def cI : Sort 1 := Sort 0` — that is, `Type := Prop`
— which type-checks against the empty environment: no basis block, no
prior constant, no binder, no literal.  The per-declaration checking work
is therefore CONSTANT, and the only thing that grows across the stream is
the environment and its name index.

**What it is for** (task #182).  Instructions on this stream must be
LINEAR in N.  A super-linear row means some structure that grows with the
environment is being *copied* rather than updated in place — the classic
Lean reference-counting failure, where a `Std.HashMap` is still reachable
from a second reference at the moment of `insert`, so `lean_array_uset`
takes `lean_copy_expand_array_nonlinear` and rewrites the whole bucket
array.  At 3 000 000 declarations that copy is unmissable; at the size of
`init-full` it hides inside the noise, which is exactly how task #179's
census passed over it.

Usage in a check (instructions per declaration must stay flat):

    for n in 100000 300000 1000000; do
      scripts/gen_linear_stream.py $n /tmp/syn-$n.ndjson
      perf stat -e instructions:u lech --verified --pre /tmp/syn-$n.ndjson
    done

Measured on master 339e026d: 89 851 / 88 941 / 88 823 instructions per
declaration at N = 100 000 / 300 000 / 1 000 000.
"""
import sys


def main() -> int:
    if len(sys.argv) != 3:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    n = int(sys.argv[1])
    out = sys.argv[2]
    with open(out, "w") as f:
        w = f.write
        w('{"meta":{"exporter":{"name":"gen_linear_stream","version":"1"},'
          '"format":{"version":"3.1.0"},'
          '"lean":{"githash":"0000000000000000000000000000000000000000",'
          '"version":"4.33.0"}}}\n')
        # level 0 is `.zero` by construction; level 1 = succ 0
        w('{"il":1,"succ":0}\n')
        # expr 0 = Sort 0 (Prop), expr 1 = Sort 1 (Type)
        w('{"ie":0,"sort":0}\n')
        w('{"ie":1,"sort":1}\n')
        # name 0 is `.anonymous` by construction; names 1..n are c1..cn
        for i in range(1, n + 1):
            w('{"in":%d,"str":{"pre":0,"str":"c%d"}}\n' % (i, i))
            w('{"def":{"all":[%d],"hints":{"regular":1},"levelParams":[],'
              '"name":%d,"safety":"safe","type":1,"value":0}}\n' % (i, i))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
