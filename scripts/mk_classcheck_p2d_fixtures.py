#!/usr/bin/env python3
"""CLASSCHECK / P2D: two forged twins, each one hash-consed node of an
exported good twin rewritten (every occurrence, the recursors included).

  corner_classcheck_alias_cyc_bad   `corner_classcheck_alias_cyc.ndjson`
      with the class `P (RL T) (RL T)` spelled `P (RL T) (RL (Id' T))`.
      Official 1 (its auxiliary types are compared structurally, so it
      makes `RL (Id' T)` and `List (RL (Id' T))` auxiliary types the
      stream has no recursors for).  Ours: `RL (Id' X)` in the class's
      constructor could be identified with the class `RL T` only by
      defeq, and `RL T` is a cyclic inner class of the key (a hole the
      class fact keeps free) — the class check refuses that
      identification, and the field is then no class occurrence: 1.

  corner_classcheck_mates_bad   `corner_classcheck_mates.ndjson` with
      the class `B T` spelled `B (Id' T)` (in `T.mk`'s field too).
      Official 1 (auxiliary types `A T`, `B T`, `B (Id' T)`,
      `A (Id' T)`).  Ours: `A T`'s block mate `B` at `A T`'s
      instantiation is no class — 1 (every block mate of a container
      class at its instantiation must be a class).

Usage: scripts/mk_classcheck_p2d_fixtures.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def load(base):
    src = os.path.join(ROOT, "tests/e2e/%s.ndjson" % base)
    recs = [json.loads(l) for l in open(src).read().splitlines()]
    names = {0: ""}
    for r in recs:
        if "in" in r:
            k = "str" if "str" in r else "num"
            pre = names[r[k]["pre"]]
            names[r["in"]] = (pre + "." if pre else "") + str(r[k].get(k, r[k].get("i")))
    exprs = {r["ie"]: r for r in recs if "ie" in r}
    return recs, names, exprs


def write(base, out):
    dst = os.path.join(ROOT, "tests/e2e/%s_bad.ndjson" % base)
    with open(dst, "w") as f:
        for r in out:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s_bad.ndjson: %d lines" % (base, len(out)))


def const_of(exprs, names, n):
    hits = [i for i, e in exprs.items() if "const" in e and names[e["const"]["name"]] == n
            and e["const"]["us"] == []]
    assert len(hits) == 1, (n, hits)
    return hits[0]


def name_of(names, n):
    hits = [i for i, s in names.items() if s == n]
    assert len(hits) == 1, (n, hits)
    return hits[0]


def app_of(exprs, f, a):
    hits = [i for i, e in exprs.items() if "app" in e and e["app"]["fn"] == f and e["app"]["arg"] == a]
    assert len(hits) == 1, (f, a, hits)
    return hits[0]


def rewrite(recs, target, new, repl):
    """Insert the `new` nodes before `target`'s line and redefine `target` as `repl`."""
    out = []
    for r in recs:
        if r.get("ie") == target:
            out += new
            r = dict(repl, ie=target)
        out.append(r)
    return out


def alias_cyc():
    base = "corner_classcheck_alias_cyc"
    recs, names, exprs = load(base)
    P, RL, T = (const_of(exprs, names, n) for n in ("P", "RL", "T"))
    rlt = app_of(exprs, RL, T)
    prl = app_of(exprs, P, rlt)
    key = app_of(exprs, prl, rlt)  # `P (RL T) (RL T)`
    nxt = max(exprs) + 1
    new = [
        {"const": {"name": name_of(names, "Id'"), "us": []}, "ie": nxt},
        {"app": {"arg": T, "fn": nxt}, "ie": nxt + 1},
        {"app": {"arg": nxt + 1, "fn": RL}, "ie": nxt + 2},
    ]
    write(base, rewrite(recs, key, new, {"app": {"arg": nxt + 2, "fn": prl}}))


def mates():
    base = "corner_classcheck_mates"
    recs, names, exprs = load(base)
    B, T = (const_of(exprs, names, n) for n in ("B", "T"))
    key = app_of(exprs, B, T)  # `B T`
    nxt = max(exprs) + 1
    new = [
        {"const": {"name": name_of(names, "Id'"), "us": []}, "ie": nxt},
        {"app": {"arg": T, "fn": nxt}, "ie": nxt + 1},
    ]
    write(base, rewrite(recs, key, new, {"app": {"arg": nxt + 1, "fn": B}}))


def main():
    alias_cyc()
    mates()


if __name__ == "__main__":
    main()
