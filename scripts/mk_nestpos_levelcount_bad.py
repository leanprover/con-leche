#!/usr/bin/env python3
"""Forge `corner_nestpos_levelcount_bad` (lane NESTIND s21): a nested
occurrence whose container is applied at the WRONG NUMBER of universe
levels.  Derived from the committed GOOD twin `corner_nestind_d_free`
(source `tests/e2e/src/corner_nestind_d_free.lean`: `CD (α : Type)`,
`TD ::= node (c : CD TD)`) by giving the container constant `CD` (no
level parameters) ONE universe level, `CD.{0} TD`, inside the block of
`TD` — its constructor type and its recursor records (types and rule
right-hand sides), path-copying so `CD`'s own declaration and every other
use of the shared `const CD` node keep the constant they had.

Official rejects: `infer_constant` fails on any constant at the wrong
level count ("incorrect number of universe levels"), so the stream is
not exporter-producible.  Target 1.

Usage: scripts/mk_nestpos_levelcount_bad.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

CHILD_KEYS = {"forallE": ("type", "body"), "lam": ("type", "body"),
              "app": ("fn", "arg"), "letE": ("type", "value", "body"),
              "proj": ("struct",), "mdata": ("expr",)}


def load(name):
    p = os.path.join(ROOT, "tests/e2e", name)
    return [json.loads(l) for l in open(p).read().splitlines()]


def dump(name, recs):
    p = os.path.join(ROOT, "tests/e2e", name)
    with open(p, "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s: %d lines" % (name, len(recs)))


def names_of(recs):
    names = {}
    for r in recs:
        if "in" in r and "str" in r:
            names[r["in"]] = (r["str"]["pre"], r["str"]["str"])
        elif "in" in r and "num" in r:
            names[r["in"]] = (r["num"]["pre"], str(r["num"]["i"]))

    def full(i):
        if i == 0:
            return ""
        pre, s = names[i]
        p = full(pre)
        return s if p == "" else p + "." + s

    return {full(i): i for i in names}


def main(src, out, member_name, cont_name, extra_level=0):
    """Inside the block of `member`, replace every `const <cont>.{us}` by
    `const <cont>.{us ++ [extra_level]}` (level id 0 is `zero`)."""
    recs = load(src)
    names = names_of(recs)
    member, cont = names[member_name], names[cont_name]
    E = {r["ie"]: r for r in recs if "ie" in r}
    bi = next(i for i, r in enumerate(recs)
              if "inductive" in r and any(t["name"] == member for t in r["inductive"]["types"]))

    nxt = max(E) + 1
    ins = []
    memo = {}
    bad = {}  # original us tuple -> new const node

    def go(ie):
        nonlocal nxt
        if ie in memo:
            return memo[ie]
        r = E[ie]
        if "const" in r and r["const"]["name"] == cont:
            us = tuple(r["const"]["us"])
            if us not in bad:
                bad[us] = nxt
                nxt += 1
                ins.append({"ie": bad[us],
                            "const": {"name": cont, "us": list(us) + [extra_level]}})
            memo[ie] = bad[us]
            return bad[us]
        k = next((k for k in CHILD_KEYS if k in r), None)
        if k is None:
            memo[ie] = ie
            return ie
        node = dict(r[k])
        changed = False
        for ck in CHILD_KEYS[k]:
            if ck in node and isinstance(node[ck], int):
                c = go(node[ck])
                if c != node[ck]:
                    node[ck] = c
                    changed = True
        if not changed:
            memo[ie] = ie
            return ie
        new = nxt
        nxt += 1
        ins.append({"ie": new, k: node})
        memo[ie] = new
        return new

    blk = recs[bi]["inductive"]
    for c in blk["ctors"]:
        c["type"] = go(c["type"])
    for rc in blk["recs"]:
        rc["type"] = go(rc["type"])
        for ru in rc["rules"]:
            ru["rhs"] = go(ru["rhs"])
    assert bad, "the container does not occur in the block"
    dump(out, recs[:bi] + ins + recs[bi:])


main("corner_nestind_d_free.ndjson", "corner_nestpos_levelcount_bad.ndjson", "TD", "CD")
