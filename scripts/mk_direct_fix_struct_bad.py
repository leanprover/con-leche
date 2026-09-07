#!/usr/bin/env python3
"""Derive the bad twins of the task #210 Part A structure-like fixtures.

  direct_fix_struct_proj_idx_bad.ndjson  — `Chain.h := fun self => self.2`
                                  (the projection index patched from 0 to
                                  2 at a two-field structure): official's
                                  `infer_proj` rejects an index past the
                                  fields; con-leche must REJECT at the
                                  table lookup ("projection index out of
                                  range").
  direct_fix_struct_proj_iota_bad.ndjson — `Chain.t_mk`'s statement patched
                                  from `(Chain.mk 3 t).t = t` to
                                  `(Chain.mk 3 t).t = Chain.mk 3 t`, the
                                  proof left `Eq.refl _`: the projection
                                  iota reduces the left side to `t`, which
                                  is not `Chain.mk 3 t`; REJECT.
  direct_fix_struct_eta_bad.ndjson — `Chain.eta`'s statement patched from
                                  `c = Chain.mk c.1 c.2` to
                                  `c = Chain.mk c.1 c` (well-typed): the
                                  η law identifies `c` with the
                                  constructor at its OWN projections only;
                                  REJECT.

Usage: scripts/mk_direct_fix_struct_bad.py
  (reads tests/e2e/direct_fix_struct_proj.ndjson and
   tests/e2e/direct_fix_struct_eta.ndjson)
"""
import json


def load(path):
    recs = [json.loads(l) for l in open(path).read().splitlines()]
    names = {}
    exprs = {}
    for r in recs:
        if "in" in r and "str" in r:
            names[r["in"]] = (r["str"]["pre"], r["str"]["str"])
        elif "in" in r and "num" in r:
            names[r["in"]] = (r["num"]["pre"], str(r["num"]["i"]))
        if "ie" in r:
            exprs[r["ie"]] = r

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

    return recs, exprs, full, name_idx


def write(path, recs):
    open(path, "w").write("\n".join(json.dumps(r) for r in recs) + "\n")


def decl_of(recs, kind, name):
    for k, r in enumerate(recs):
        if kind in r and r[kind]["name"] == name:
            return k, r
    raise SystemExit(f"no {kind} named index {name}")


# --- twins 1 and 2: off the projection fixture -----------------------------
recs, exprs, full, name_idx = load("tests/e2e/direct_fix_struct_proj.ndjson")
chain_n = name_idx("Chain")
h_n = name_idx("Chain.h")
tmk_n = name_idx("Chain.t_mk")
max_ie = max(exprs)

# twin 1: the projection index past the fields
k, d = decl_of(recs, "def", h_n)
lam = exprs[d["def"]["value"]]
proj = exprs[lam["lam"]["body"]]
if "proj" not in proj or proj["proj"]["idx"] != 0 or proj["proj"]["typeName"] != chain_n:
    raise SystemExit("Chain.h's value is not `fun self => self.0`")
out1 = []
for r in recs:
    if r.get("ie") == proj["ie"]:
        r = json.loads(json.dumps(r))
        r["proj"]["idx"] = 2
    out1.append(r)
write("tests/e2e/direct_fix_struct_proj_idx_bad.ndjson", out1)

# twin 2: the iota statement's right-hand side
k, d = decl_of(recs, "thm", tmk_n)
ty = exprs[d["thm"]["type"]]                       # ∀ t, Eq Chain (Chain.t (mk 3 t)) t
eq_app = exprs[ty["forallE"]["body"]]              # app (app (app Eq Chain) lhs) t
if "app" not in eq_app or exprs[eq_app["app"]["arg"]].get("bvar") != 0:
    raise SystemExit("Chain.t_mk's statement is not `… = t`")
lhs_app = exprs[eq_app["app"]["fn"]]               # app (app Eq Chain) (Chain.t (mk 3 t))
proj_app = exprs[lhs_app["app"]["arg"]]            # app Chain.t (mk 3 t)
mk3t = proj_app["app"]["arg"]                      # Chain.mk 3 t
new_eq = max_ie + 1
new_ty = max_ie + 2
new_recs = [{"app": {"arg": mk3t, "fn": eq_app["app"]["fn"]}, "ie": new_eq},
            {"forallE": dict(ty["forallE"], body=new_eq), "ie": new_ty}]
thm2 = json.loads(json.dumps(d))
thm2["thm"]["type"] = new_ty
out2 = recs[:k] + new_recs + [thm2] + recs[k + 1:]
write("tests/e2e/direct_fix_struct_proj_iota_bad.ndjson", out2)

# --- twin 3: off the η fixture ----------------------------------------------
recs, exprs, full, name_idx = load("tests/e2e/direct_fix_struct_eta.ndjson")
eta_n = name_idx("Chain.eta")
max_ie = max(exprs)
k, d = decl_of(recs, "thm", eta_n)
ty = exprs[d["thm"]["type"]]                       # ∀ c, Eq Chain c (Chain.mk c.0 c.1)
eq_app = exprs[ty["forallE"]["body"]]              # app (app (app Eq Chain) c) (mk c.0 c.1)
mk_app = exprs[eq_app["app"]["arg"]]               # app (app Chain.mk c.0) c.1
p1 = exprs[mk_app["app"]["arg"]]
if "proj" not in p1 or p1["proj"]["idx"] != 1:
    raise SystemExit("Chain.eta's statement is not `c = Chain.mk c.0 c.1`")
c_bvar = p1["proj"]["struct"]                      # bvar 0
new_mk = max_ie + 1
new_eq = max_ie + 2
new_ty = max_ie + 3
new_recs = [{"app": {"arg": c_bvar, "fn": mk_app["app"]["fn"]}, "ie": new_mk},
            {"app": {"arg": new_mk, "fn": eq_app["app"]["fn"]}, "ie": new_eq},
            {"forallE": dict(ty["forallE"], body=new_eq), "ie": new_ty}]
thm3 = json.loads(json.dumps(d))
thm3["thm"]["type"] = new_ty
out3 = recs[:k] + new_recs + [thm3] + recs[k + 1:]
write("tests/e2e/direct_fix_struct_eta_bad.ndjson", out3)
print("wrote direct_fix_struct_proj_idx_bad.ndjson, direct_fix_struct_proj_iota_bad.ndjson, "
      "direct_fix_struct_eta_bad.ndjson")
