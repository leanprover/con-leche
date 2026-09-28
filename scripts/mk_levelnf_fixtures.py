#!/usr/bin/env python3
"""CC-LEVELNF lane: forged spellings of one nested class that official's
level instantiation identifies (`src/kernel/level.cpp`, `instantiate` →
`update_max` → `mk_max`/`mk_imax`) and `Level.simplify` would not.

Both twins start from `corner_levelnf_d3_param.ndjson` (source
`tests/e2e/src/corner_levelnf_d3_param.lean`: `corner_keynamed_d3_level`
nested at a level PARAMETER, `D.{w} R`) and re-spell the phantom value's
binder `List.{u} β` in `D.mk`'s type and in `D.rec`'s two copies (the
elaborator normalises these levels, so no source can say them); `R`'s
recursors, which official generates from the instantiated class, keep
`List.{w} R`.

  corner_levelnf_d3_param_dup     binder `List.{max u u} β`: at `D.{w} R`
      official's `mk_max(w, w)` is `w` (`l1 == l2`).
  corner_levelnf_d3_param_imax1   binder `List.{imax 1 u} β`: at `D.{w} R`
      official's `mk_imax(1, w)` is `w` (`is_one(l1)`).

Official 0 on both.  Ours 0 on both (`Level.canon`); under
`Level.simplify` the dup twin was a false reject (1: `max w w` stayed
apart), the imax1 twin 0 (`simplify` resolves `imax 1 w`).

Usage: scripts/mk_levelnf_fixtures.py [SRC_DIR] [OUT_DIR]   (default tests/e2e/)
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


def forge(src, dst, spell):
    """`spell(u, nl)`: new level records (from index `nl` on) whose LAST
    one is the re-spelling of level `u`."""
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
        if not ("lam" in e and "app" in exprs[e["lam"]["type"]]
                and is_const(exprs[e["lam"]["type"]]["app"]["fn"], "List")
                and is_const(head(e["lam"]["body"]), "PUnit.unit")):
            return False
        lv = levels.get(exprs[exprs[e["lam"]["type"]]["app"]["fn"]]["const"]["us"][0]) or {}
        return "param" in lv and names[lv["param"]] == "u"

    # every `fun _ : List.{u} β => PUnit.unit` at the GENERIC level `u`
    # (D.mk's type and D.rec's two copies); R's (at `w`) stay
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
            lrecs = spell(u, nl)
            new[lam] += lrecs
            for r in lrecs:
                levels[r["il"]] = r
            new[lam].append({"const": {"name": lconst["name"], "us": [lrecs[-1]["il"]]}, "ie": nxt})
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
    base = os.path.join(src, "corner_levelnf_d3_param.ndjson")
    forge(base, os.path.join(out, "corner_levelnf_d3_param_dup.ndjson"),
          lambda u, nl: [{"il": nl, "max": [u, u]}])
    forge(base, os.path.join(out, "corner_levelnf_d3_param_imax1.ndjson"),
          lambda u, nl: [{"il": nl, "succ": 0}, {"il": nl + 1, "imax": [nl, u]}])


if __name__ == "__main__":
    main()
