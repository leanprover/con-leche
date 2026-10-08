#!/usr/bin/env python3
"""Generate the parallel install's end-to-end fixtures (task #329).

    scripts/mk_pinstall_fixtures.py OUTDIR

Three streams of N = 3000 definitions over `Sort`, wide enough that a
pool of workers installs many of them at once.  Definition `c<i>` has
type `Type` and value `c<i // 2>` (`c1`'s value is `Prop`), so every
record depends on an earlier one and the dependency graph is a tree of
depth log N — the install pool runs it in parallel, the commit thread in
order.

* `pinstall_ok.ndjson` — accepted (exit 0); the arena battery also runs
  it with `--install-fallback-at=<k>`, which makes the commit thread
  abandon the pool at fold position `k` as on a misprediction and finish
  serially: same verdict, same count.
* `pinstall_reject_mid.ndjson` — record `c1500` has the type `nosuch`, a
  constant nobody declares: the install rejects it (exit 1), and the
  verdict names `c1500` at every worker count, although records after it
  may already be installed by the pool.
* `pinstall_dup.ndjson` — `c2500` is declared a second time, under the
  name `c7` (a duplicate of a record two thousand records earlier): the
  install rejects it with `duplicate declaration c7` at every worker
  count — the worker view sees `c7`'s first slot.
"""
import os
import sys

N = 3000
HEADER = ('{"meta":{"exporter":{"name":"mk_pinstall_fixtures","version":"1"},'
          '"format":{"version":"3.1.0"},'
          '"lean":{"githash":"0000000000000000000000000000000000000000",'
          '"version":"4.33.0"}}}\n')


def stream(path, bad=None, dup=None):
    with open(path, "w") as f:
        w = f.write
        w(HEADER)
        w('{"il":1,"succ":0}\n')
        # expr 0 = Prop, expr 1 = Type
        w('{"ie":0,"sort":0}\n')
        w('{"ie":1,"sort":1}\n')
        # name N+1 = nosuch, expr 2 = const nosuch
        w('{"in":%d,"str":{"pre":0,"str":"nosuch"}}\n' % (N + 1))
        w('{"ie":2,"const":{"name":%d,"us":[]}}\n' % (N + 1))
        nexpr = 3
        cexpr = {}
        for i in range(1, N + 1):
            w('{"in":%d,"str":{"pre":0,"str":"c%d"}}\n' % (i, i))
            if i == 1:
                val = 0
            else:
                val = cexpr[i // 2]
            ty = 2 if i == bad else 1
            name = dup[1] if dup is not None and i == dup[0] else i
            w('{"def":{"all":[%d],"hints":{"regular":1},"levelParams":[],'
              '"name":%d,"safety":"safe","type":%d,"value":%d}}\n' % (name, name, ty, val))
            w('{"ie":%d,"const":{"name":%d,"us":[]}}\n' % (nexpr, i))
            cexpr[i] = nexpr
            nexpr += 1


def main() -> int:
    if len(sys.argv) != 2:
        print(__doc__.strip(), file=sys.stderr)
        return 2
    out = sys.argv[1]
    stream(os.path.join(out, "pinstall_ok.ndjson"))
    stream(os.path.join(out, "pinstall_reject_mid.ndjson"), bad=1500)
    stream(os.path.join(out, "pinstall_dup.ndjson"), dup=(2500, 7))
    return 0


if __name__ == "__main__":
    sys.exit(main())
