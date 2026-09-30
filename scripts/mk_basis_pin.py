#!/usr/bin/env python3
"""Forge the two streams that NEST A BLOCK THROUGH A BASIS TYPE
(maintainer's ruling, 2026-09-21: "we'd reject if the basis were
normal inductives" — open question 5 of DESIGN DOCUMENT 1; the
amendment "collapsing pins and basis containers" spells out why
nothing official accepts gets here).

Neither stream is exporter-producible: official rejects both blocks,
so each is derived from a committed GOOD twin by repointing one
constant — the container's parameter — to the block's own member.

  corner_pin_quot_bad <- corner_pin_quot_free
      `QFree | mk : Quot (fun (_ _ : Nat) => True) -> QFree`  becomes
      `QFree | mk : Quot (fun (_ _ : QFree) => True) -> QFree`.
      `Quot` is not an `inductive` in official's environment
      (`is_nested_inductive_app`, inductive.cpp:932, tests
      `is_inductive()`), so there is no nested occurrence to find: the
      field whnf's to a `Quot` application, which is not a member
      application, and `check_positivity` reports a "non valid
      occurrence".  REJECT (exit 1).
  corner_pin_eq_bad   <- corner_pin_eq_free
      `EFree : Prop | mk : @Eq Prop False False -> EFree`  becomes
      `EFree : Prop | mk : @Eq Prop EFree EFree -> EFree`.  `Eq`'s only
      PARAMETER is `α`; both sides are index arguments, so again there
      is no nested occurrence and the field is a "non valid
      occurrence".  REJECT (exit 1).

Both rewrites keep the levels right: `QFree : Type` where `Nat : Type`
was, `EFree : Prop` where `False : Prop` was.

Usage: scripts/mk_basis_pin.py   (reads and writes under tests/e2e/)
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


repin("corner_pin_quot_free.ndjson", "corner_pin_quot_bad.ndjson", "QFree", "Nat")
repin("corner_pin_eq_free.ndjson", "corner_pin_eq_bad.ndjson", "EFree", "False")
