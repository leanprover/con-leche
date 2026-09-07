#!/usr/bin/env python3
"""Derive the two BAD twins of task #218's mutual fixtures (audit #206-A4).

  ind_mutual_param_bad.ndjson — ind_mutual_param_defeq with the second
      member's parameter domain `id Type` replaced IN PLACE by `Type 1`
      (the expression node is shared by `MB2`, `MB2.mk` and `MB2.nil`, so
      all three change together).  Official's `check_inductive_types`
      rejects the block ("parameters of all inductive datatypes must
      match", exit 1).  con-leche's modeller builds the auxiliary family
      over the FIRST member's telescope and emits `MB2._model := λ (α :
      Type 1), aux α (tag.1 α)`; the fold rejects that record's type check
      (`Type 1` against `aux`'s `Type`), exit 1 — the intended behaviour
      (the user's ruling: the modeller may be "yolo-like", invalid input
      is caught in the checked code).
  ind_mutual_sort_bad.ndjson  — ind_mutual_sort_defeq with the second
      member's sort `Sort (max v u)` replaced by `Sort (max u 1)`.
      Official: "mutually inductive types must live in the same
      universe", exit 1.  con-leche: `MD._model : Sort (max u 1) := aux
      tag.1` (of sort `Sort (max u v)`) rejects at the definition's
      type check, exit 1.

Usage: scripts/mk_mutual_bad.py   (reads and writes under tests/e2e/)
"""
import json
import re


def load(path):
    return [json.loads(l) for l in open(path).read().splitlines()]


def dump(path, recs):
    with open(path, "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")


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


def level_index(recs, pred):
    for r in recs:
        if "il" in r and pred(r):
            return r["il"]
    return None


def max_il(recs):
    return max([r["il"] for r in recs if "il" in r] + [0])


# --- the parameter twin ----------------------------------------------------
src = "tests/e2e/ind_mutual_param_defeq.ndjson"
recs = load(src)
names = names_of(recs)
id_n = names["id"]
# the node `id.{?} Type`: an app whose fn is `const id` and arg a `sort`
sort1 = None
for r in recs:
    if "ie" in r and "sort" in r:
        il = r["sort"]
        if any(x.get("il") == il and x.get("succ") == 0 for x in recs):
            sort1 = r["ie"]
consts = {r["ie"]: r["const"]["name"] for r in recs if "ie" in r and "const" in r}
apps = {r["ie"]: r["app"] for r in recs if "ie" in r and "app" in r}
# `@id.{3} (Type 1) Type`: an app whose arg is `Type` and whose fn is
# `id` applied to its implicit type argument
target = None
for i, r in enumerate(recs):
    if "ie" in r and "app" in r and r["app"]["arg"] == sort1:
        inner = apps.get(r["app"]["fn"])
        if inner is not None and consts.get(inner["fn"]) == id_n:
            target = i
assert target is not None, "no `id Type` node"
# the level 2 = succ (succ zero)
one = level_index(recs, lambda r: r.get("succ") == 0)
two = level_index(recs, lambda r: r.get("succ") == one)
ie = recs[target]["ie"]
if two is None:
    two = max_il(recs) + 1
    recs.insert(target, {"il": two, "succ": one})
    target += 1
recs[target] = {"ie": ie, "sort": two}
dump("tests/e2e/ind_mutual_param_bad.ndjson", recs)
print("ind_mutual_param_bad.ndjson: `id Type` (ie %d) -> Type 1" % ie)

# --- the sort twin ---------------------------------------------------------
src = "tests/e2e/ind_mutual_sort_defeq.ndjson"
recs = load(src)
names = names_of(recs)
md = names["MD"]
# MD's inductive record: its type is `sort L` with `L = max v u`
md_ty = None
for r in recs:
    if "inductive" in r:
        for t in r["inductive"]["types"]:
            if t["name"] == md:
                md_ty = t["type"]
assert md_ty is not None
idx = next(i for i, r in enumerate(recs) if r.get("ie") == md_ty)
assert "sort" in recs[idx], "MD's type is not a sort"
u_n = names["u"]
u_il = level_index(recs, lambda r: r.get("param") == u_n)
one = level_index(recs, lambda r: r.get("succ") == 0)
ins = []
nxt = max_il(recs) + 1
if one is None:
    one = nxt
    nxt += 1
    ins.append({"il": one, "succ": 0})
new = nxt
ins.append({"il": new, "max": [u_il, one]})
recs[idx:idx] = ins
recs[idx + len(ins)] = {"ie": md_ty, "sort": new}
dump("tests/e2e/ind_mutual_sort_bad.ndjson", recs)
print("ind_mutual_sort_bad.ndjson: MD : Sort (max v u) -> Sort (max u 1)")
