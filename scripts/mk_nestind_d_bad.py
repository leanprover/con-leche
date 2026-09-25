#!/usr/bin/env python3
"""Corner case of ruling (D) (lane NESTIND): the target check types a
call at an OUTSIDE class a second time with the family's classes
abstracted (the major's own group in the stored constructor, its
ancestor classes at their instantiations).  A container whose own
recursive occurrence is reached only through a redex.

  corner_nestind_d_redex_bad   `corner_nestind_d_free.ndjson` with the
      container constructor `CD.mk (z : CD α)` rewritten to
      `CD.mk (z : (fun X => CD X) α)` (everything else, the recursors
      included, unchanged).  The rule of `CD.mk` at the class `CD TD`
      calls `TD.rec_1` on `z`.  Official rejects the block: its
      auxiliary type replaces only the literal `CD TD`, so the auxiliary
      constructor keeps `(fun X => CD X) TD`, whose whnf is a non-valid
      occurrence (and from v4.33.1 `check_uniform_ind_occs` rejects `CD`
      itself: `CD X` is not at the parameters).  The class-abstracted
      typing abstracts the group IN THE STORED CONSTRUCTOR, so it sees
      `(fun X => #CD X) #TD`, whose whnf is the hole: an accept-superset
      (sound).  TARGET 0 (official 1).

Usage: scripts/mk_nestind_d_bad.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load(name):
    p = os.path.join(ROOT, "tests/e2e", name)
    return [json.loads(l) for l in open(p).read().splitlines()]


def dump(name, recs):
    p = os.path.join(ROOT, "tests/e2e", name)
    with open(p, "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s: %d lines" % (name, len(recs)))


def full_names(recs):
    names = {0: ""}
    for r in recs:
        if "in" in r and "str" in r:
            pre = names[r["str"]["pre"]]
            names[r["in"]] = (pre + "." if pre else "") + r["str"]["str"]
    return names


def main():
    recs = load("corner_nestind_d_free.ndjson")
    names = full_names(recs)
    exprs = {r["ie"]: r for r in recs if "ie" in r}
    nxt = max(exprs) + 1
    out = []
    for r in recs:
        ind = r.get("inductive")
        if ind is not None and any(names[c["name"]] == "CD.mk" for c in ind["ctors"]):
            c = next(c for c in ind["ctors"] if names[c["name"]] == "CD.mk")
            top = exprs[c["type"]]["forallE"]          # {α : Type} → …
            fld = exprs[top["body"]]["forallE"]        # (z : CD α) → CD α
            lam = {"ie": nxt, "lam": {"binderInfo": "default", "body": fld["type"],
                                      "name": top["name"], "type": top["type"]}}
            bv0 = next(i for i, e in exprs.items() if e.get("bvar") == 0)
            app = {"app": {"arg": bv0, "fn": nxt}, "ie": nxt + 1}
            f2 = {"forallE": dict(fld, type=nxt + 1), "ie": nxt + 2}
            t2 = {"forallE": dict(top, body=nxt + 2), "ie": nxt + 3}
            out += [lam, app, f2, t2]
            c["type"] = nxt + 3
        out.append(r)
    dump("corner_nestind_d_redex_bad.ndjson", out)


if __name__ == "__main__":
    main()
