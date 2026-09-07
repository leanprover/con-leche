#!/usr/bin/env python3
"""Derive the `ind_stub_*` twins of tests/e2e/direct_fix_nat.ndjson (task #220).

Each twin carries a BROKEN RECURSOR RECORD beside a block whose type or
constructors the checker must reject on their own — the arena's finding
F1 shape, where the stub recursor used to make the recogniser refuse the
block and the semantic reject was never reached:

  ind_stub_rec      — `Nat'.rec`'s record blanked (`numMotives = 0`,
                      `numMinors = 0`, `rules = []`): the block itself is
                      fine, so the reject is the recursor pin's ("recursor
                      rules are not the generated ones").
  ind_stub_pos      — the same stub, plus `Nat'.succ`'s field patched to
                      `Nat' → Nat'`: a NON-POSITIVE occurrence, which must
                      reject BEFORE the recursor is looked at.
  ind_stub_resid    — the same stub, plus `Nat'.zero`'s type patched to
                      `Nat' → Nat'` with `numFields = 0`: an invalid
                      constructor return type (official's
                      `is_valid_ind_app`).
  ind_stub_univ     — the same stub, plus `Nat'.succ`'s field patched to
                      `Type`: a field universe too large for a `Type 0`
                      block.
  ind_stub_recname  — the block intact, its recursor record named
                      `Nat'.not_rec`: official generates only `Nat'.rec`
                      and its replay rejects ("No such recursor").
  ind_stub_reclps   — the block intact, its recursor record's level
                      parameters `[u, u]`: neither the block's own (the
                      small eliminator) nor a fresh one in front (the
                      large one).

Usage: scripts/mk_ind_stub_bad.py [tests/e2e/direct_fix_nat.ndjson]
"""
import json
import sys

src = sys.argv[1] if len(sys.argv) > 1 else "tests/e2e/direct_fix_nat.ndjson"
recs = [json.loads(l) for l in open(src).read().splitlines()]

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

def name_idx(s):
    for i in names:
        if full(i) == s:
            return i
    raise SystemExit(f"name {s} not in the stream")

exprs = {r["ie"]: r for r in recs if "ie" in r}
max_ie = max(exprs)
max_in = max(names)

def fresh_ie():
    global max_ie
    max_ie += 1
    return max_ie

def fresh_in():
    global max_in
    max_in += 1
    return max_in

nat_n = name_idx("Nat'")
zero_n = name_idx("Nat'.zero")
succ_n = name_idx("Nat'.succ")
rec_n = name_idx("Nat'.rec")
n_n = name_idx("n")
u_n = name_idx("u")

def find_const(name):
    for e in exprs.values():
        if "const" in e and e["const"]["name"] == name and e["const"]["us"] == []:
            return e["ie"]
    raise SystemExit(f"no constant {full(name)} in the stream")

nat_const = find_const(nat_n)

def block_of(name):
    for k, r in enumerate(recs):
        if "inductive" in r and any(t["name"] == name for t in r["inductive"]["types"]):
            return k, r
    raise SystemExit(f"no inductive block {full(name)}")

bk, block = block_of(nat_n)
nat_ty = [t for t in block["inductive"]["types"] if t["name"] == nat_n][0]["type"]

def emit(path, extra, patch):
    """Write a twin: `extra` records spliced before the block, `patch`
    applied to a deep copy of the block record."""
    b = json.loads(json.dumps(block))
    patch(b)
    out = ([json.dumps(r) for r in recs[:bk]] + [json.dumps(r) for r in extra] +
           [json.dumps(b)] + [json.dumps(r) for r in recs[bk + 1:]])
    open(path, "w").write("\n".join(out) + "\n")

def blank_rec(b):
    for r in b["inductive"]["recs"]:
        if r["name"] == rec_n:
            r["numParams"] = 0
            r["numMotives"] = 0
            r["numMinors"] = 0
            r["numIndices"] = 0
            r["rules"] = []

# --- the stub recursor alone -------------------------------------------
emit("tests/e2e/ind_stub_rec.ndjson", [], blank_rec)

# --- the stub recursor beside a non-positive field ----------------------
arrow = fresh_ie()
arrow_rec = {"ie": arrow, "forallE": {"binderInfo": "default", "body": nat_const,
                                      "name": n_n, "type": nat_const}}
succ_neg = fresh_ie()
succ_neg_rec = {"ie": succ_neg, "forallE": {"binderInfo": "default", "body": nat_const,
                                            "name": n_n, "type": arrow}}

def patch_pos(b):
    blank_rec(b)
    for c in b["inductive"]["ctors"]:
        if c["name"] == succ_n:
            c["type"] = succ_neg
emit("tests/e2e/ind_stub_pos.ndjson", [arrow_rec, succ_neg_rec], patch_pos)

# --- the stub recursor beside an invalid constructor return type --------
def patch_resid(b):
    blank_rec(b)
    for c in b["inductive"]["ctors"]:
        if c["name"] == zero_n:
            c["type"] = arrow
emit("tests/e2e/ind_stub_resid.ndjson", [arrow_rec], patch_resid)

# --- the stub recursor beside a field universe that is too large --------
succ_big = fresh_ie()
succ_big_rec = {"ie": succ_big, "forallE": {"binderInfo": "default", "body": nat_const,
                                            "name": n_n, "type": nat_ty}}

def patch_univ(b):
    blank_rec(b)
    for c in b["inductive"]["ctors"]:
        if c["name"] == succ_n:
            c["type"] = succ_big
emit("tests/e2e/ind_stub_univ.ndjson", [succ_big_rec], patch_univ)

# --- the recursor's own occurrence inside its rules ---------------------
# Both remaining twins change the recursor CONSTANT the rules recurse
# through, so that the rule bodies stay the generated ones for the
# record as patched and the reject is the pin being tested rather than
# the rule comparison.
CHILD_KEYS = {"forallE": ("type", "body"), "lam": ("type", "body"),
              "app": ("fn", "arg"), "letE": ("type", "value", "body"),
              "proj": ("struct",), "mdata": ("expr",)}

def kind_of(e):
    for k in CHILD_KEYS:
        if k in e:
            return k
    return None

def rebuild(ie, target, repl, new_recs, memo):
    """Copy the DAG below `ie` along every path to `target`, which is
    replaced by `repl`; returns the (possibly new) expression index."""
    if ie in memo:
        return memo[ie]
    if ie == target:
        memo[ie] = repl
        return repl
    e = exprs[ie]
    k = kind_of(e)
    if k is None:
        memo[ie] = ie
        return ie
    node = dict(e[k])
    changed = False
    for ck in CHILD_KEYS[k]:
        if ck in node and isinstance(node[ck], int):
            c = rebuild(node[ck], target, repl, new_recs, memo)
            if c != node[ck]:
                node[ck] = c
                changed = True
    if not changed:
        memo[ie] = ie
        return ie
    n = fresh_ie()
    new_recs.append({"ie": n, k: node})
    memo[ie] = n
    return n

# the recursor's own level parameters, as the level indices spelling
# them: the occurrence the RULES recurse through is the one at exactly
# those (the definitions below the block instantiate it at others)
lvl_param = {r["il"]: r["param"] for r in recs if "il" in r and "param" in r}
rec_lps = [r for r in block["inductive"]["recs"] if r["name"] == rec_n][0]["levelParams"]
rec_us = [i for q in rec_lps for i in lvl_param if lvl_param[i] == q]
rec_occ = [e["ie"] for e in exprs.values()
           if "const" in e and e["const"]["name"] == rec_n and e["const"]["us"] == rec_us]
if len(rec_occ) != 1:
    raise SystemExit("expected exactly one `Nat'.rec` occurrence at its own levels")
rec_occ = rec_occ[0]

# --- a recursor record under a name official never generates ------------
notrec_n = fresh_in()
extra_name = [{"in": notrec_n, "str": {"pre": nat_n, "str": "not_rec"}}]
notrec_const = fresh_ie()
extra_name.append({"ie": notrec_const, "const": {"name": notrec_n, "us": rec_us}})
memo_name = {}
rules_name = {}
for r in block["inductive"]["recs"]:
    if r["name"] == rec_n:
        for j, rule in enumerate(r["rules"]):
            rules_name[j] = rebuild(rule["rhs"], rec_occ, notrec_const,
                                    extra_name, memo_name)

def patch_recname(b):
    for r in b["inductive"]["recs"]:
        if r["name"] == rec_n:
            r["name"] = notrec_n
            for j, rule in enumerate(r["rules"]):
                rule["rhs"] = rules_name[j]
emit("tests/e2e/ind_stub_recname.ndjson", extra_name, patch_recname)

# --- a recursor record whose level parameters are neither shape ---------
extra_lps = []
duprec_const = fresh_ie()
extra_lps.append({"ie": duprec_const, "const": {"name": rec_n, "us": rec_us + rec_us}})
memo_lps = {}
rules_lps = {}
for r in block["inductive"]["recs"]:
    if r["name"] == rec_n:
        for j, rule in enumerate(r["rules"]):
            rules_lps[j] = rebuild(rule["rhs"], rec_occ, duprec_const,
                                   extra_lps, memo_lps)

def patch_reclps(b):
    for r in b["inductive"]["recs"]:
        if r["name"] == rec_n:
            r["levelParams"] = [u_n, u_n]
            for j, rule in enumerate(r["rules"]):
                rule["rhs"] = rules_lps[j]
emit("tests/e2e/ind_stub_reclps.ndjson", extra_lps, patch_reclps)

print("wrote tests/e2e/ind_stub_{rec,pos,resid,univ,recname,reclps}.ndjson")
