#!/usr/bin/env python3
"""Derive the `ind_numparams_*` twins of tests/e2e/direct_fix_nat.ndjson (task #228).

Both patch INDUCTIVE-RECORD METADATA only — no expression, no
constructor and no recursor record is touched — which is the point:
the declaration's own `numParams` is input official reads and checks
the block against, and its `numIndices` is input official never reads
at all.

  ind_numparams_bad     — the first block's type record declares
                          `numParams = 1` on a former with NO Pi binder
                          (`Nat' : Type`).  Official rejects at
                          "number of parameters mismatch in inductive
                          datatype declaration" (`check_inductive_types`
                          runs out of telescope before it has peeled
                          `nparams` binders); before task #228 the
                          checker read the count off the CONSTRUCTORS,
                          which all say 0, and ACCEPTED the block.
  ind_numparams_indices — every type record's nonzero `numIndices` is
                          bumped, `numParams` left alone.  Nothing ever
                          compares an inductive record against the
                          `InductiveVal` the kernel generates (only
                          constructors and recursors are postponed and
                          compared, `Lean4Checker/Replay.lean`), so the
                          declared index count is not input official
                          reads and the stream must still ACCEPT — the
                          guard on task #228's one-sidedness, and on the
                          parameter/index split of the block that
                          carries both (`numParams = 2`, one index).

Usage: scripts/mk_ind_numparams.py [tests/e2e/direct_fix_nat.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/direct_fix_nat.ndjson"
recs = [json.loads(l) for l in open(src).read().splitlines()]

blocks = [k for k, r in enumerate(recs) if "inductive" in r]
if not blocks:
    raise SystemExit(f"no inductive block in {src}")


def emit(path, patch):
    """Write a twin: `patch` applied to a deep copy of every block record."""
    out = []
    for k, r in enumerate(recs):
        if k in blocks:
            r = json.loads(json.dumps(r))
            patch(k, r)
        out.append(json.dumps(r))
    open(path, "w").write("\n".join(out) + "\n")


# --- the declared parameter count, one too large ------------------------
def patch_bad(k, r):
    if k == blocks[0]:
        for t in r["inductive"]["types"]:
            if t["numParams"] != 0:
                raise SystemExit("expected a parameterless first block")
            t["numParams"] = 1


emit("tests/e2e/ind_numparams_bad.ndjson", patch_bad)


# --- the declared index count, wrong on purpose -------------------------
def patch_indices(_k, r):
    for t in r["inductive"]["types"]:
        if t["numIndices"] != 0:
            t["numIndices"] += 3


emit("tests/e2e/ind_numparams_indices.ndjson", patch_indices)

print("wrote tests/e2e/ind_numparams_bad.ndjson "
      "tests/e2e/ind_numparams_indices.ndjson")
