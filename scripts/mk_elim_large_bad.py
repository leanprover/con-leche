#!/usr/bin/env python3
"""Forge LARGE eliminators for `Prop` blocks official gives SMALL ones
(the uniform route's elimination guard — DESIGN.md's amendments of
2026-09-21, "the recursor check knows no motives" and "the elimination
guard, declaratively").

Official's `elim_only_at_universe_zero` (inductive.cpp:479) evaluates
`m_ind_types.size() > 1` on the AUX block, so a `Prop` block that is
MUTUAL or NESTED eliminates into `Prop` only, however few constructors
and however subsingleton its fields.  These three streams are what a
stream that claims otherwise looks like; every one of them must be
REJECTED, and accepting one is a soundness hole: at `w = 0` the
block's elements are all the proof point, so two minor premises would
have to be equal.

  corner_nest_or_prop_large_bad  <- corner_nest_or_prop
      `NOr : Prop | mk : Or True NOr -> NOr`, one member, one
      constructor, all fields propositions — un-nested that is
      official's large-elimination case; nested it is not, and the
      DESIGN amendment's countermodel is this very block (`pt` is both
      `inl trivial` and `inr p`, so `rec_1 pt` would have to be two
      different minors; refuted at `motive_2 := fun _ => Bool`).
  corner_nest_and_prop_large_bad <- nested_p13
      the same at `P13 : Prop | mk : And P13 P13` (survey probe P13,
      the nested block official still eliminates small).
  corner_mutual_prop_large_bad   <- corner_prop_mutual_small
      a two-member MUTUAL `Prop` block: official returns true at
      `m_ind_types.size() > 1` before it looks at the constructors.
      The base's two theorems are dropped — they instantiate the
      motives at a `Prop` and would reject for their own reason.

The patch is the same in all three: every motive binder of every
recursor of the block (in the recursor's TYPE and in each rule's
lambda prefix, which share the binder's domain node) has its codomain
`Sort 0` replaced by `Sort 1`, i.e. a monomorphic eliminator into
`Type`.  Official's own large eliminators prepend a fresh level
parameter instead; `Type` is enough to be large, and it keeps the
record's `levelParams` — and so the stream's level bookkeeping —
exactly as exported.

Usage: scripts/mk_elim_large_bad.py   (reads and writes under tests/e2e/)
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


def exprs(recs):
    return {r["ie"]: r for r in recs if "ie" in r}


def block_of(recs, member):
    for r in recs:
        if "inductive" in r and any(t["name"] == member for t in r["inductive"]["types"]):
            return r
    raise SystemExit("no inductive block for name index %d" % member)


def make_large(src, out, member_name, drop_theorems=False):
    recs = load(src)
    names = names_of(recs)
    member = names[member_name]
    block = block_of(recs, member)
    E = exprs(recs)
    nxt_ie = max(E) + 1
    nxt_il = max([r["il"] for r in recs if "il" in r] + [0]) + 1

    # `Sort 1`.  Every record this script creates is emitted
    # immediately in FRONT of the first record that mentions it: the
    # stream defines an index before it is used, and the checker's
    # decoder enforces that.
    one = None
    for r in recs:
        if "il" in r and r.get("succ") == 0:
            one = r["il"]
    pending = []
    if one is None:
        one = nxt_il
        nxt_il += 1
        pending.append({"il": one, "succ": 0})
    sort1 = nxt_ie
    nxt_ie += 1
    pending.append({"ie": sort1, "sort": one})

    # the motive binders' NAME indices: the `numMotives` binders after
    # the `numParams` ones, in every recursor of this block
    motive_names = set()
    for rc in block["inductive"]["recs"]:
        e = rc["type"]
        for i in range(rc["numParams"] + rc["numMotives"]):
            r = E[e]
            assert "forallE" in r, "recursor prefix is not a telescope"
            if i >= rc["numParams"]:
                motive_names.add(r["forallE"]["name"])
            e = r["forallE"]["body"]
    assert motive_names, "no motives"

    # `D = Pi indices, Pi (t : T ...), Sort 0`  ->  `... Sort 1`, path-copied
    patched = {}

    def relevel(ie):
        if ie in patched:
            return patched[ie]
        r = E[ie]
        if "sort" in r:
            assert r["sort"] == 0, "motive codomain is not Prop"
            patched[ie] = sort1
            return sort1
        assert "forallE" in r, "motive domain is not a telescope"
        body = relevel(r["forallE"]["body"])
        nonlocal nxt_ie
        new = nxt_ie
        nxt_ie += 1
        pending.append({"ie": new, "forallE": dict(r["forallE"], body=body)})
        patched[ie] = new
        return new

    out_recs = []
    hits = 0
    for r in recs:
        if drop_theorems and "theorem" in r:
            continue
        if "ie" in r:
            for k in ("forallE", "lam"):
                if k in r and r[k]["name"] in motive_names:
                    r[k] = dict(r[k], type=relevel(r[k]["type"]))
                    hits += 1
        out_recs.extend(pending)
        pending.clear()
        out_recs.append(r)
    assert hits, "no motive binder found"
    assert not pending
    dump(out, out_recs)


make_large("corner_nest_or_prop.ndjson", "corner_nest_or_prop_large_bad.ndjson", "NOr")
make_large("nested_p13.ndjson", "corner_nest_and_prop_large_bad.ndjson", "P13")
make_large("corner_prop_mutual_small.ndjson", "corner_mutual_prop_large_bad.ndjson",
           "MA", drop_theorems=True)
