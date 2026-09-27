#!/usr/bin/env python3
"""KEYNAMED lane (PRIMREC): forged D3 fixtures (spellings of one nested
class that official identifies and the key-named positivity check would
not).

  corner_keynamed_d3_level_split   `corner_keynamed_d3_level.ndjson` (source
      `tests/e2e/src/corner_keynamed_d3_level.lean`) with the phantom value's
      binder `List.{u} β` re-spelled `List.{max u u} β` in `D.mk`'s type and
      in `D.rec`'s two copies (the elaborator normalises `max u u`, so no
      source can say it); `R`'s recursors, which official generates from
      the simplified instance, keep `List.{0} R`.  Official 0: at the
      instance `D.{0} R` its `instantiate_lparams` simplifies `max 0 0` to
      `0` (`level.cpp` `mk_max`), one auxiliary type.  Today 1: this
      checker's `Level.subst` does not simplify, so the keys `List.{0} R`
      and `List.{max 0 0} R` differ (and the recursor's majors are
      official's simplified classes).

  corner_keynamed_ctor_occ_bad   `corner_keynamed_ctor_occ.ndjson` with the
      value's binder `List R` re-spelled `List ((fun x => x) R)` (the forge
      of `scripts/mk_checkdel_d_bad.py`).  Official 1 (two auxiliary types,
      the auxiliary constructor ill-typed), today 0 (D3).

Usage: scripts/mk_keynamed_fixtures.py [SRC_DIR] [OUT_DIR]   (default tests/e2e/)
"""
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load(path):
    recs = [json.loads(l) for l in open(path).read().splitlines()]
    names = {0: ""}
    for r in recs:
        if "in" in r:
            k = "str" if "str" in r else "num"
            pre = names[r[k]["pre"]]
            names[r["in"]] = (pre + "." if pre else "") + str(r[k].get(k, r[k].get("i")))
    return recs, names


def forge_level(src, dst):
    recs, names = load(src)
    exprs = {r["ie"]: r for r in recs if "ie" in r}
    levels = {r["il"]: r for r in recs if "il" in r}

    def is_const(i, n):
        e = exprs[i]
        return "const" in e and names[e["const"]["name"]] == n

    def head(i):
        while "app" in exprs[i]:
            i = exprs[i]["app"]["fn"]
        return i

    def list_u(i):
        e = exprs[i]
        return ("lam" in e and "app" in exprs[e["lam"]["type"]]
                and is_const(exprs[e["lam"]["type"]]["app"]["fn"], "List")
                and is_const(head(e["lam"]["body"]), "PUnit.unit")
                and "param" in (levels.get(exprs[exprs[e["lam"]["type"]]["app"]["fn"]]["const"]["us"][0]) or {}))

    # every `fun _ : List.{u} β => PUnit.unit` at the GENERIC level (D.mk's
    # type and D.rec's two copies); the instances at level 0 (R's
    # recursors, official-generated from the simplified instance) stay
    lams = sorted(i for i in exprs if list_u(i))
    assert len(lams) == 3, lams
    nl = max(levels) + 1
    nxt = max(exprs) + 1
    repl = {}
    new = {}
    for lam in lams:
        lty = exprs[exprs[lam]["lam"]["type"]]["app"]
        lconst = exprs[lty["fn"]]["const"]
        (u,) = lconst["us"]
        new[lam] = []
        if nl not in levels:
            new[lam].append({"il": nl, "max": [u, u]})
            new[lam].append({"const": {"name": lconst["name"], "us": [nl]}, "ie": nxt})
            levels[nl] = None
        new[lam].append({"app": {"arg": lty["arg"], "fn": nxt}, "ie": nxt + 1 + len(repl)})
        repl[lam] = nxt + 1 + len(repl)
    out = []
    for r in recs:
        if r.get("ie") in repl:
            out += new[r["ie"]]
            r = dict(r, lam=dict(r["lam"], type=repl[r["ie"]]))
        out.append(r)
    with open(dst, "w") as f:
        for r in out:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s: %d lines (λ nodes %s)" % (os.path.basename(dst), len(out), lams))


def main():
    src = sys.argv[1] if len(sys.argv) > 1 else os.path.join(ROOT, "tests/e2e")
    out = sys.argv[2] if len(sys.argv) > 2 else os.path.join(ROOT, "tests/e2e")
    forge_level(os.path.join(src, "corner_keynamed_d3_level.ndjson"),
                os.path.join(out, "corner_keynamed_d3_level_split.ndjson"))
    sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
    from mk_checkdel_d_bad import forge
    forge("corner_keynamed_ctor_occ")


if __name__ == "__main__":
    main()
