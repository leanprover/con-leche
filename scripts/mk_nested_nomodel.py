#!/usr/bin/env python3
"""Task #315: the `*_nomodel` twins — a nested fixture's stream with the
OUTER block's in-process model REMOVED, so that `--nested-shadow`
reaches the outer block.

Why they exist.  The shadow (`--nested-shadow`) runs the native nested
route beside the fold's install, so it only ever sees a block the fold
REACHES.  On `nested_pin_collide`/`nested_pin_collide2` the fold does
not reach the outer block: the in-process modeller generates a model
for it whose records collide (`duplicate declaration
<T>._model._impl.pack_1`, the collapsing-pins false reject recorded in
DESIGN §WIDE (f1) (c)), and the fold stops there — one record short of
the `inductive` record the shadow would fire on.

The fix is not to repair the modeller (it is being retired); it is to
hand the fold a stream with NO model for the outer block.  This script
builds one:

  1. run the checker with `CON_LECHE_INMODEL_DUMP` — the raw input with
     every generated model spliced in ahead of its block
     (`ConLeche/Frontend/InModelDump.lean`);
  2. diff the dump against the input to recover the spliced chunks, and
     drop the LAST one, the outer block's;
  3. write the result.

Checked with `CON_LECHE_INMODEL=0` the product installs the inner
container from the stream's own model records, then reaches the outer
block's `inductive` record: the shadow prints its verdict and the fold
declines for want of an install route (exit 2).  That verdict is the
gated row in `tests/nested-shadow-expected.txt`.

Dropping the LAST chunk is safe because the outer block is the stream's
last modelled block: the splice writer's name/expression indices run
above the input's maximum and no later record refers to them.

Usage (from the project root, with the checker built):

    scripts/mk_nested_nomodel.py nested_pin_collide nested_pin_collide2
"""
import difflib
import os
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
BIN = os.path.join(ROOT, ".lake", "build", "bin", "con-leche")


def build(name: str) -> None:
    src = os.path.join(ROOT, "tests", "e2e", name + ".ndjson")
    out = os.path.join(ROOT, "tests", "e2e", name + "_nomodel.ndjson")
    with tempfile.TemporaryDirectory() as tmp:
        dump = os.path.join(tmp, "dump.ndjson")
        env = dict(os.environ, CON_LECHE_INMODEL_DUMP=dump)
        # the run itself need not accept -- it is the dump we want
        subprocess.run([BIN, "--jobs=1", src], env=env, cwd=ROOT,
                       stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)
        if not os.path.exists(dump):
            sys.exit(f"{name}: no model dump written (no block modelled?)")
        a = open(src, "rb").read().split(b"\n")
        b = open(dump, "rb").read().split(b"\n")
    ops = difflib.SequenceMatcher(a=a, b=b, autojunk=False).get_opcodes()
    chunks = [o for o in ops if o[0] == "insert"]
    if not chunks:
        sys.exit(f"{name}: the dump spliced nothing")
    if [o for o in ops if o[0] in ("delete", "replace")]:
        sys.exit(f"{name}: the dump is not an insertion-only edit of the input")
    _, _, _, lo, hi = chunks[-1]
    open(out, "wb").write(b"\n".join(b[:lo] + b[hi:]))
    print(f"{name}: dropped {hi - lo} lines of the outer block's model "
          f"-> tests/e2e/{os.path.basename(out)}")


if __name__ == "__main__":
    names = sys.argv[1:] or ["nested_pin_collide", "nested_pin_collide2"]
    for n in names:
        build(n)
