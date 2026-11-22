#!/usr/bin/env python3
"""Derive the `ind_flags_*` install fixtures of task #630 from existing e2e fixtures.

lean4export 3.2.0 (lean4 PR #16595) writes five booleans on every inductive
type record — `isImpredicative`, `isK`, `hasProjections`, `hasEta`,
`hasLargeElim` — and the block's check validates them instead of computing
the features from the declaration's shape.  The toolchain that writes them is
not released, so these fixtures are today's exports with the flags patched in.

`allowed` gives each type record the flags the official kernel allows and its
elaborator would write: `hasLargeElim` as the recursor records eliminate
(a fresh level parameter in front); `isImpredicative` at a proposition
without a large eliminator; `isK` as the recursor's `k`; `hasProjections` at
one constructor, no index, not impredicative; `hasEta` with projections at a
block that is not recursive.  At a block without a large eliminator the
recursors carry no rules (`rules: []`), as the new exporter writes them.
Each fixture is that, then the patch its line below names.

Usage: scripts/mk_ind_flags_install.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
KEYS = ["isImpredicative", "isK", "hasProjections", "hasEta", "hasLargeElim"]


def load(base):
    lines = open(os.path.join(ROOT, "tests/e2e", base + ".ndjson")).read().splitlines()
    return lines, [json.loads(l) for l in lines]


def tables(recs):
    names, exprs = {}, {}
    for r in recs:
        if "in" in r:
            v = r.get("str") or r.get("num")
            names[r["in"]] = (v["pre"], v.get("str", v.get("i")))
        if "ie" in r:
            exprs[r["ie"]] = r
    return names, exprs


def name_of(names, i):
    pre, s = names[i]
    return str(s) if pre == 0 else name_of(names, pre) + "." + str(s)


def result_level(exprs, e, n):
    """The level of the sort the type `e` ends in after `n` binders (None: not syntactic)."""
    for _ in range(n):
        r = exprs[e]
        if "forallE" not in r:
            return None
        e = r["forallE"]["body"]
    r = exprs[e]
    return r["sort"] if "sort" in r else None


def allowed(names, exprs, ind):
    """The flags the official kernel allows for every type of the block `ind`, by name."""
    types, recs = ind["types"], ind["recs"]
    rec0 = recs[0]
    large = len(rec0["levelParams"]) > len(types[0]["levelParams"])
    out = {}
    for t in types:
        lvl = result_level(exprs, t["type"], t["numParams"] + t["numIndices"])
        is_prop = lvl == 0
        impred = is_prop and not large
        proj = len(t["ctors"]) == 1 and t["numIndices"] == 0 and not impred
        k = any(r["k"] for r in recs) and t is types[0]
        out[name_of(names, t["name"])] = {
            "isImpredicative": impred, "isK": k, "hasProjections": proj,
            "hasEta": proj and not t["isRec"], "hasLargeElim": large}
    return out


def emit(base, out, patch=None, keep_rules=(), bare=()):
    """Write `out` from `base`: every block at its allowed flags, then `patch(name, flags)` per
    type; the rules of small blocks dropped except those of the recursors in `keep_rules`; the
    types in `bare` left without flags."""
    lines, recs = load(base)
    names, exprs = tables(recs)
    res = []
    for line, r in zip(lines, recs):
        if "inductive" in r:
            r = json.loads(json.dumps(r))
            ind = r["inductive"]
            fl = allowed(names, exprs, ind)
            for t in ind["types"]:
                f = fl[name_of(names, t["name"])]
                if patch:
                    patch(name_of(names, t["name"]), f)
                if name_of(names, t["name"]) not in bare:
                    for k in KEYS:
                        t[k] = f[k]
            for rc in ind["recs"]:
                if not fl[name_of(names, ind["types"][0]["name"])]["hasLargeElim"] and \
                        name_of(names, rc["name"]) not in keep_rules:
                    rc["rules"] = []
            line = json.dumps(r, separators=(",", ":"), sort_keys=True, ensure_ascii=False)
        res.append(line)
    open(os.path.join(ROOT, "tests/e2e", out + ".ndjson"), "w").write("\n".join(res) + "\n")


def at(n, **kw):
    """A patch setting flags `kw` on type `n`."""
    def p(name, f):
        if name == n:
            f.update(kw)
    return p


# accepted at their allowed flags
emit("direct_sum_or", "ind_flags_or")
emit("unitlike_fieldless", "ind_flags_unitlike")
emit("ind_rec_struct_proj", "ind_flags_rec_struct")
emit("prop_proj", "ind_flags_prop_struct")
emit("inmodel_mutual", "ind_flags_mutual")
emit("inmodel_nested", "ind_flags_nested")
emit("direct_fix_nat", "ind_flags_nat")
emit("indexed_vec", "ind_flags_vec")
emit("ind_flags_nest_prop", "ind_flags_nest", at("FlagNestTree", isImpredicative=False))

# rejected: the flags do not fit the block, or withdraw what the stream uses
emit("direct_sum_or", "ind_flags_or_rules_bad", keep_rules=("Or'.rec",))
emit("direct_sum_or", "ind_flags_or_large_bad", at("Or'", hasLargeElim=True))
emit("direct_sum_or", "ind_flags_or_k_bad", at("Or'", isK=True))
emit("direct_sum_or", "ind_flags_impred_type_bad", at("Nil", isImpredicative=True))
emit("unitlike_fieldless", "ind_flags_unitlike_eta_off_bad", at("E", hasEta=False))
emit("ind_rec_struct_proj", "ind_flags_rec_struct_eta_bad", at("Chain", hasEta=True))
emit("ind_rec_struct_proj", "ind_flags_rec_struct_proj_off_bad",
     at("Chain", hasProjections=False))
emit("prop_proj", "ind_flags_prop_struct_eta_off_bad", at("PropPair", hasEta=False))
emit("prop_proj_raw", "ind_flags_prop_data_struct_bad")
emit("prop_proj_raw", "ind_flags_prop_data_bound_bad", at("PropStructure", isImpredicative=False))
emit("direct_fix_acc", "ind_flags_acc_large_bad")
emit("inmodel_mutual", "ind_flags_mutual_disagree_bad",
     lambda n, f: f.update(hasLargeElim=not f["hasLargeElim"]) if n == "InModelMutual.B" else None)
emit("direct_fix_nat", "ind_flags_eq_k_off_bad", at("Eq", isK=False))
emit("inmodel_mutual", "ind_flags_mixed_block_bad", bare=("InModelMutual.B",))
# nested through a proposition with projections, impredicative: the auxiliary type would be
# impredicative with projections
emit("ind_flags_nest_prop", "ind_flags_nest_impred_proj_bad")
# nested through an impredicative proposition with a field in `Type`, not impredicative: the
# auxiliary type's constructor would have a field outside `Prop`
emit("ind_flags_nest_prop", "ind_flags_nest_bound_bad",
     lambda n, f: f.update(isImpredicative=False) if n in ("FlagNestTree", "FlagNestExTree")
     else None)
