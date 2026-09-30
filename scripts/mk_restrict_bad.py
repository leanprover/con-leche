#!/usr/bin/env python3
"""Forge the official-REJECTED examples of the restriction audit
(`_tmp/uniform-inds/RESTRICT-AUDIT.md`, lane RESTRICT-FIX): each stream
is derived from a committed GOOD twin `restrict_<ex>_free` (source
`tests/e2e/src/`, an ordinary block whose would-be occurrence names the
unrelated pin type `BPin`) by repointing `BPin` to the block's own
member inside the block's records, KEEPING the levels the pin is used at
(`scripts/mk_nestpos_bad.py`'s `repin`, with the levels read off the
block's own records).  Official rejects both (Lean v4.29.1; the kernel's
message is in each source's header), so neither is exporter-producible.

  restrict_b01_idx_only_bad       `mk : Vi Nat T → T`: the member only in
                                  a container's INDEX (non valid occurrence)
  restrict_b02_m2prime_direct_bad `mk : T.{0} → T.{u}`: the member at other
                                  levels as the field (non valid occurrence)

Usage: scripts/mk_restrict_bad.py   (reads and writes under tests/e2e/)
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


def repin(src, out, member_name, pin_name):
    """Repoint every `const <pin>.{us}` under the block of `member` to
    `const <member>.{us}` (the same levels), path-copying so the pin's
    own declaration and every other use of the shared nodes keep the
    constant they had."""
    recs = load(src)
    names = names_of(recs)
    member, pin = names[member_name], names[pin_name]
    E = {r["ie"]: r for r in recs if "ie" in r}
    bi = next(i for i, r in enumerate(recs)
              if "inductive" in r and any(t["name"] == member for t in r["inductive"]["types"]))

    nxt = max(E) + 1
    ins = []
    memo = {}
    consts = {}

    def mem_const(us):
        nonlocal nxt
        key = json.dumps(us)
        if key not in consts:
            for r in E.values():
                if "const" in r and r["const"]["name"] == member and r["const"]["us"] == us:
                    consts[key] = r["ie"]
                    break
            else:
                consts[key] = nxt
                nxt += 1
                ins.append({"ie": consts[key], "const": {"name": member, "us": us}})
        return consts[key]

    def go(ie):
        nonlocal nxt
        if ie in memo:
            return memo[ie]
        r = E[ie]
        if "const" in r and r["const"]["name"] == pin:
            memo[ie] = mem_const(r["const"]["us"])
            return memo[ie]
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
    assert ins, "nothing was repointed"
    dump(out, recs[:bi] + ins + recs[bi:])


for ex in ["b01_idx_only", "b02_m2prime_direct"]:
    repin("restrict_%s_free.ndjson" % ex, "restrict_%s_bad.ndjson" % ex, "T", "BPin")
