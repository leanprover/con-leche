#!/usr/bin/env python3
"""Forge the U4-at-nested-fields corner (lane NESTW): each stream is
derived from a committed GOOD twin `corner_nestw_<class>_free` (source
`tests/e2e/src/`, an ordinary non-nested block whose would-be nested
occurrence names an unrelated pin type) in two steps inside the block's
records: every `@Prod.snd A B x` becomes the raw projection
`.proj Prod 1 x` (so the later field reads the earlier field's value
WITHOUT naming the member — Lean elaborates the projection FUNCTION,
whose type arguments would), then the pin is repointed to the block's
own member (`scripts/mk_nestpos_bad.py`'s `repin`).  Official rejects
both results ("(kernel) invalid projection": its auxiliary type
replaces `Prod T Nat`, so the projection names the wrong structure),
so neither is exporter-producible.

  corner_nestw_u4_bad       UT, `mk (a : Prod UT Nat) (b : Fin a.2)`
  corner_nestw_u4frame_bad  VT, `node (x : Sigma (fun p : Prod VT Nat => Fin p.2))`

The positivity walk accepts both (the later field's normal form reads
the nested field, and its U4 decline looks at `.recursive`/`.reflexive`
fields of member constructors only), so the wide operator of (W) is
not flat: DESIGN, lane NESTW, finding F-W1.

Usage: scripts/mk_nestw_bad.py   (reads and writes under tests/e2e/)
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


def rewrite_block(recs, member, f):
    """Rewrite every expression of `member`'s block bottom-up by `f`
    (`f(ie, rec, E) -> ie'` or None to recurse), path-copying new
    nodes in front of the block record."""
    E = {r["ie"]: r for r in recs if "ie" in r}
    bi = next(i for i, r in enumerate(recs)
              if "inductive" in r and any(t["name"] == member for t in r["inductive"]["types"]))
    state = {"nxt": max(E) + 1, "ins": []}
    memo = {}

    def fresh(node):
        new = state["nxt"]
        state["nxt"] += 1
        node = dict(node, ie=new)
        state["ins"].append(node)
        E[new] = node
        return new

    def go(ie):
        if ie in memo:
            return memo[ie]
        r = E[ie]
        out = f(ie, r, E, go, fresh)
        if out is not None:
            memo[ie] = out
            return out
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
        memo[ie] = fresh({k: node})
        return memo[ie]

    blk = recs[bi]["inductive"]
    for c in blk["ctors"]:
        c["type"] = go(c["type"])
    for rc in blk["recs"]:
        rc["type"] = go(rc["type"])
        for ru in rc["rules"]:
            ru["rhs"] = go(ru["rhs"])
    assert state["ins"], "nothing was rewritten"
    return recs[:bi] + state["ins"] + recs[bi:]


def spine(ie, E):
    args = []
    while "app" in E[ie]:
        args.append(E[ie]["app"]["arg"])
        ie = E[ie]["app"]["fn"]
    return ie, args[::-1]


def forge(src, out, member_name, pin_name):
    recs = load(src)
    names = names_of(recs)
    member, pin = names[member_name], names[pin_name]
    snd, prod = names["Prod.snd"], names["Prod"]

    # step 1: `@Prod.snd A B x` ↦ `.proj Prod 1 x`
    def to_proj(ie, r, E, go, fresh):
        if "app" not in r:
            return None
        h, args = spine(ie, E)
        if "const" in E[h] and E[h]["const"]["name"] == snd and len(args) == 3:
            return fresh({"proj": {"idx": 1, "struct": go(args[2]), "typeName": prod}})
        return None

    recs = rewrite_block(recs, member, to_proj)

    # step 2: the pin ↦ the member, at the pin's levels
    E = {r["ie"]: r for r in recs if "ie" in r}
    us = next(r["const"]["us"] for r in E.values() if "const" in r and r["const"]["name"] == pin)
    mem = next((r["ie"] for r in E.values()
                if "const" in r and r["const"]["name"] == member and r["const"]["us"] == us), None)

    def repin(ie, r, E, go, fresh):
        nonlocal mem
        if "const" in r and r["const"]["name"] == pin:
            if mem is None:
                mem = fresh({"const": {"name": member, "us": us}})
            return mem
        return None

    recs = rewrite_block(recs, member, repin)
    dump(out, recs)


for cls, member, pin in [("u4", "UT", "UPin"), ("u4frame", "VT", "VPin")]:
    forge("corner_nestw_%s_free.ndjson" % cls, "corner_nestw_%s_bad.ndjson" % cls, member, pin)
