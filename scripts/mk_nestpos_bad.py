#!/usr/bin/env python3
"""Forge the REJECT classes of positivity through containers (lane
NESTPOS): each stream is derived from a committed GOOD twin
`corner_nestpos_<class>_free` (source `tests/e2e/src/`, an ordinary
non-nested block whose would-be nested occurrence names an unrelated
pin type) by repointing the pin to the block's own member inside the
block's records — `scripts/mk_basis_pin.py`'s `repin`, verbatim.
Official rejects every result (Lean v4.29.1 and v4.34.0, the block
written in Lean; the kernel's message is in each source's header), so
none is exporter-producible.

  corner_nestpos_neg_bad       NegC NegT, `NegC α | mk : (α → Nat) → …`: non positive
  corner_nestpos_negdeep_bad   NegD NegDT, `… : List (α → Nat) → …`: non positive, one deeper
  corner_nestpos_idxty_bad     IdxC IdxT 0, `IdxC α : Idx α → Type`: unknown constant (N2)
  corner_nestpos_idxval_bad    IdxV IdxVT (List.length [h]): non valid occurrence (index)
  corner_nestpos_sort_bad      Nonempty SortT at a Type block: one universe (N3)
  corner_nestpos_sortprop_bad  PLift SortP at a Prop block: one universe (N3)
  corner_nestpos_local_bad     Prod LocT (Fin n): parameters cannot contain local variables
  corner_nestpos_redex_bad     FL RedT, `FL α := List α`: non valid occurrence (no container)
  corner_nestpos_group_bad     GC1 GT, GC1's group member GC2 negative: non positive
  corner_nestpos_eqret_bad     @Eq Prop (PEq p) True (pinned Eq): invalid return type
  corner_nestpos_eqidx_bad     @Eq Prop PEqI PEqI: non valid occurrence (index)
  corner_nestpos_eqlocal_bad   @Eq PEqL h h: parameters cannot contain local variables

The block's recursor records are repointed with it; official never
reaches them.  None of the forged streams carries an auxiliary
recursor, so the RECOGNISER routes each block to the uniform route,
where today's verdict is a decline ("a nested occurrence of the
block"); the target is official's reject, except `redex` and `group`,
accepted supersets (charter item 8, D1/D2), whose target is 0.

Usage: scripts/mk_nestpos_bad.py   (reads and writes under tests/e2e/)
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
    """Repoint every `const <pin>` under the block of `member` to
    `const <member>`, path-copying so the pin's own declaration and
    every other use of the shared nodes keep the constant they had."""
    recs = load(src)
    names = names_of(recs)
    member, pin = names[member_name], names[pin_name]
    E = {r["ie"]: r for r in recs if "ie" in r}
    bi = next(i for i, r in enumerate(recs)
              if "inductive" in r and any(t["name"] == member for t in r["inductive"]["types"]))

    nxt = max(E) + 1
    ins = []
    memo = {}
    # the member's own constant, at the pin's levels
    us = None
    for r in E.values():
        if "const" in r and r["const"]["name"] == pin:
            us = r["const"]["us"]
    assert us is not None, "the pin does not occur as a constant"
    mem_const = None
    for r in E.values():
        if "const" in r and r["const"]["name"] == member and r["const"]["us"] == us:
            mem_const = r["ie"]
    if mem_const is None:
        mem_const = nxt
        nxt += 1
        ins.append({"ie": mem_const, "const": {"name": member, "us": us}})

    def go(ie):
        if ie in memo:
            return memo[ie]
        r = E[ie]
        if "const" in r and r["const"]["name"] == pin:
            memo[ie] = mem_const
            return mem_const
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
        nonlocal nxt
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


for cls, member, pin in [
        ("neg", "NegT", "NPin"), ("negdeep", "NegDT", "DPin"), ("idxty", "IdxT", "IPin"),
        ("idxval", "IdxVT", "VPin"), ("sort", "SortT", "SPin"), ("sortprop", "SortP", "PPin"),
        ("local", "LocT", "LPin"), ("redex", "RedT", "RPin"), ("group", "GT", "GPin"),
        ("eqret", "PEq", "EPin"), ("eqidx", "PEqI", "IPinE"), ("eqlocal", "PEqL", "LPinE")]:
    repin("corner_nestpos_%s_free.ndjson" % cls, "corner_nestpos_%s_bad.ndjson" % cls,
          member, pin)
