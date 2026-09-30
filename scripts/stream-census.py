#!/usr/bin/env python3
"""Census of an arena stream (task #187; raw since task #207).

For every stream in the performance battery PERF.md wants three numbers
that are properties of the INPUT, not of anybody's environment
representation:

  * `records`   — declaration records in the file (def/thm/opaque/axiom/
                  inductive/quot lines).  This is what con-leche's verdict line
                  counts, up to the fold's own exact adjustments below.
  * `official`  — what the official kernel prints.  Its Main.lean says
                  `Accepted {constMap.size} declarations`, and its
                  constMap is the PARSED export: one entry per exported
                  constant — so an inductive record contributes its type
                  formers, its constructors AND its recursors — minus the
                  three `Quot.mk`/`Quot.lift`/`Quot.ind` entries it erases
                  before replay.  Hence
                      official = plain + types + ctors + recs - 3.
  * `fold`      — con-leche's accepted declaration records.  Since task
                  #293 that is `records` itself: the decoder emits the
                  file's records and nothing else, so the four `quot`
                  lines and the `Quot.sound` axiom record are five
                  records of the file and count as five (they install
                  ONE pinned block between them, which is a property of
                  the fold, not of the file).  The column is kept
                  because the adjustment used to be real: until #293 the
                  parse folded the quotient records into one
                  `basisDecl` (-3) and swallowed `Quot.sound` (-1).

and the BLOCK census: every inductive record con-leche installs itself
(`native`: the uniform fixpoint route),
split by shape — indexed (numIndices > 0), structure (no indices, one
constructor), sum (no indices, not one constructor) — beside the
pinned basis blocks.

`fold` PREDICTS THE VERDICT LINE: the checker's fold runs over the
file's own records (after the built-in prelude), and nothing is added
to them.  There is no `modeled` column: a `_model` record in a stream
is an ordinary declaration and has no effect on any block.

    scripts/stream-census.py STREAM.ndjson [...]
"""
import json
import sys

TOLERATED = {"sorryAx"}
QUOT_EXTRA = {"Quot.sound"}
# the pinned basis blocks (`ConLeche.reservedBasisNames`): recognised at the
# parse and folded to a `basisDecl`, so they are not installed by a route
PINNED = {"Eq", "Nat", "PUnit", "Empty", "False"}


def name_of(tbl, i):
    return tbl.get(i, f"?{i}")


def census(path):
    tbl = {0: ""}
    plain = types = ctors = recs = 0
    records = 0
    quot = 0
    tolerated = 0
    quot_axioms = 0
    inds = []          # (name, n_ctors, n_indices)
    ind_names = []
    with open(path, "r") as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            o = json.loads(line)
            if "in" in o and "str" in o:
                s = o["str"]
                pre = name_of(tbl, s["pre"]) if s["pre"] else ""
                tbl[o["in"]] = (pre + "." if pre else "") + s["str"]
                continue
            if "ii" in o and "str" in o:      # numeric name component
                s = o["str"]
                pre = name_of(tbl, s["pre"]) if s["pre"] else ""
                tbl[o["ii"]] = (pre + "." if pre else "") + str(s["str"])
                continue
            for kind in ("def", "thm", "opaque", "axiom", "quot"):
                if kind in o:
                    records += 1
                    plain += 1
                    nm = name_of(tbl, o[kind]["name"])
                    if kind == "quot":
                        quot += 1
                    if kind == "axiom":
                        if nm in TOLERATED:
                            tolerated += 1
                        if nm in QUOT_EXTRA:
                            quot_axioms += 1
                    break
            else:
                if "inductive" in o:
                    records += 1
                    v = o["inductive"]
                    ts = v.get("types", [])
                    types += len(ts)
                    ctors += sum(len(t.get("ctors", [])) for t in ts)
                    recs += len(v.get("recs", []))
                    head = name_of(tbl, ts[0]["name"]) if ts else "?"
                    ind_names.append(head)
                    inds.append((head, len(ts),
                                 sum(len(t.get("ctors", [])) for t in ts),
                                 max((t.get("numIndices", 0) for t in ts),
                                     default=0)))
    pinned = [b for b in inds if b[0] in PINNED]
    native = [b for b in inds if b[0] not in PINNED]
    idx = [b for b in native if b[3] > 0]
    struct = [b for b in native if b[3] == 0 and b[2] == 1]
    summ = [b for b in native if b[3] == 0 and b[2] != 1]
    return {
        "path": path,
        "records": records,
        "official": plain + types + ctors + recs - 3,
        "fold": records,
        "quot": quot,
        "quot_axioms": quot_axioms,
        "tolerated": tolerated,
        "inductive": len(inds),
        "pinned": len(pinned),
        "native": len(native),
        "native_structures": len(struct),
        "native_sums": len(summ),
        "native_indexed": len(idx),
    }


def main(argv):
    rows = [census(p) for p in argv[1:]]
    keys = ["records", "official", "fold", "quot", "quot_axioms", "tolerated",
            "inductive", "pinned", "native", "native_structures",
            "native_sums", "native_indexed"]
    print("stream\t" + "\t".join(keys))
    for r in rows:
        print(r["path"].split("/")[-1] + "\t"
              + "\t".join(str(r[k]) for k in keys))


if __name__ == "__main__":
    main(sys.argv)
