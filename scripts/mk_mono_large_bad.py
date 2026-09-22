#!/usr/bin/env python3
"""Forge a MONOMORPHIC large eliminator for a `Prop` block official
gives a small one — the one-member, one-constructor case the counting
half of `elim_only_at_universe_zero` lets through.

`scripts/mk_elim_large_bad.py` forges the same patch (a motive's `Sort
0` codomain replaced by `Sort 1`, keeping the record's level
parameters) for blocks official refuses large elimination on for a
COUNTING reason: two members, or a container occurrence.  This one is
the case the counting half cannot see — ONE member, ONE constructor —
where official refuses because of the PER-FIELD subsingleton criterion
instead, and where the uniform route's two halves were keyed on
different things until lane SEC1 (2026-09-22):

  corner_rec_mono_large_bad  <- direct_idx_prop
      `Hidden : Nat -> Prop | mk (n m : Nat) : Hidden (Nat.succ n)`,
      whose two fields are DATA and neither an index argument, with
      `Hidden.rec`'s motive re-pointed at `Type`.  `Hidden.mk 0 0` and
      `Hidden.mk 0 1` are two proofs of `Hidden 1`, hence definitionally
      equal by proof irrelevance, while the eliminator tells them
      apart — so the stream goes on to prove `0 = 1`, and the four
      declarations appended here are that proof:

        def myget : forall n, Hidden n -> Nat :=
          fun n t => Hidden.rec (fun _ _ => Nat) (fun n m => m) n t
        theorem bad : myget 1 (Hidden.mk 0 0) = myget 1 (Hidden.mk 0 1)
          := Eq.refl _                            -- by proof irrelevance
        theorem lhs_is_zero : myget 1 (Hidden.mk 0 0) = 0 := rfl  -- by iota
        theorem rhs_is_one  : myget 1 (Hidden.mk 0 1) = 1 := rfl  -- by iota

      `direct_idx_prop_large_bad` is the SAME block with the motive
      patched to `Sort u` instead: that gains the fresh elimination
      level parameter, so `BlockShape.large` is `true` and the
      constructors' stage applies the criterion.  `Type` is one token's
      difference and used to slip past both halves; the guard is
      `blockLargeElimAllowed` (`Kernel/Inductives/BlockRec.lean`).

The motive binders are found through the BLOCK's own recursors (their
domain expression nodes), not by binder name: `direct_idx_prop`
declares four families and the exported stream interns the name
`motive` once for all of them.

Usage: scripts/mk_mono_large_bad.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SRC = "direct_idx_prop.ndjson"
OUT = "corner_rec_mono_large_bad.ndjson"
MEMBER = "Hidden"


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


recs = load(SRC)
names = names_of(recs)
E = {r["ie"]: r for r in recs if "ie" in r}
member = names[MEMBER]
block = None
for r in recs:
    if "inductive" in r and any(t["name"] == member for t in r["inductive"]["types"]):
        block = r
if block is None:
    raise SystemExit("no inductive block for %s" % MEMBER)

nxt_in = max(r["in"] for r in recs if "in" in r) + 1
nxt_ie = max(E) + 1
nxt_il = max([r["il"] for r in recs if "il" in r] + [0]) + 1
pending = []


def emit(**rec):
    """A new expression record, queued in FRONT of the record being
    written: the stream defines an index before it is used."""
    global nxt_ie
    i = nxt_ie
    nxt_ie += 1
    pending.append(dict(rec, ie=i))
    return i


def name(s, pre=0):
    global nxt_in
    i = nxt_in
    nxt_in += 1
    pending.append({"in": i, "str": {"pre": pre, "str": s}})
    return i


# ---- the patch: the block's motive domains, `... -> Sort 0` -> `Sort 1`

# `1`, at a FRESH level index: the stream may well define `succ 0`
# already, but not before the first record this script rewrites, and a
# level index must be defined before it is used.  Level index 0 is the
# decoder's built-in `0`, so this record needs nothing of the stream.
one_lvl = nxt_il
nxt_il += 1
pending.append({"il": one_lvl, "succ": 0})
sort1 = emit(sort=one_lvl)

motive_doms = set()
for rc in block["inductive"]["recs"]:
    e = rc["type"]
    for i in range(rc["numParams"] + rc["numMotives"]):
        r = E[e]
        assert "forallE" in r, "recursor prefix is not a telescope"
        if i >= rc["numParams"]:
            motive_doms.add(r["forallE"]["type"])
        e = r["forallE"]["body"]
assert motive_doms, "no motives"

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
    new = emit(forallE=dict(r["forallE"], body=body))
    patched[ie] = new
    return new


# the declarations the base stream builds ON the small eliminator
# (`Hidden.small`, `Hidden.elim`) instantiate the motive at a `Prop`
# and stop typing the moment it is re-pointed at `Type`; they are
# dropped, the way `mk_elim_large_bad.py` drops its base's theorems.
# Found by reachability, not by name: any expression mentioning the
# block's recursor.
uses = set()
for r in recs:
    if "ie" not in r:
        continue
    k = [x for x in r if x != "ie"][0]
    v = r[k]
    if k == "const":
        hit = v["name"] in {rc["name"] for rc in block["inductive"]["recs"]}
    elif k == "app":
        hit = v["fn"] in uses or v["arg"] in uses
    elif k in ("lam", "forallE"):
        hit = v["type"] in uses or v["body"] in uses
    elif k == "letE":
        hit = any(v[f] in uses for f in ("type", "value", "body"))
    elif k == "proj":
        hit = v["struct"] in uses
    else:
        hit = False
    if hit:
        uses.add(r["ie"])

out = []
hits = 0
for r in recs:
    dk = next((k for k in ("def", "thm", "opaq") if k in r), None)
    if dk is not None and (r[dk]["type"] in uses or r[dk].get("value") in uses):
        continue
    if "ie" in r:
        for k in ("forallE", "lam"):
            if k in r and r[k]["type"] in motive_doms:
                r[k] = dict(r[k], type=relevel(r[k]["type"]))
                hits += 1
    out.extend(pending)
    pending.clear()
    out.append(r)
assert hits, "no motive binder found"
assert not pending

# ---- the four declarations the patched block now proves


def app(fn, *args):
    for a in args:
        fn = emit(app={"fn": fn, "arg": a})
    return fn


def lam(nm, ty, body):
    return emit(lam={"binderInfo": "default", "name": nm, "type": ty, "body": body})


def pi(nm, ty, body):
    return emit(forallE={"binderInfo": "default", "name": nm, "type": ty, "body": body})


n_nm = name("n")
t_nm = name("t")
m_nm = name("m")
nat = emit(const={"name": names["Nat"], "us": []})
zero = emit(const={"name": names["Nat.zero"], "us": []})
succ = emit(const={"name": names["Nat.succ"], "us": []})
hid = emit(const={"name": names[MEMBER], "us": []})
mk = emit(const={"name": names[MEMBER + ".mk"], "us": []})
rec = emit(const={"name": names[MEMBER + ".rec"], "us": []})
eq = emit(const={"name": names["Eq"], "us": [one_lvl]})
refl = emit(const={"name": names["Eq.refl"], "us": [one_lvl]})
bv0 = emit(bvar=0)
bv1 = emit(bvar=1)
one = app(succ, zero)

# def myget : forall (n : Nat), Hidden n -> Nat :=
#   fun n t => Hidden.rec (fun _ _ => Nat) (fun n m => m) n t
myget_ty = pi(n_nm, nat, pi(t_nm, app(hid, bv0), nat))
motive_v = lam(n_nm, nat, lam(t_nm, app(hid, bv0), nat))
minor_v = lam(n_nm, nat, lam(m_nm, nat, bv0))
myget_val = lam(n_nm, nat, lam(t_nm, app(hid, bv0), app(rec, motive_v, minor_v, bv1, bv0)))
myget = name("myget")
out.extend(pending)
pending.clear()
out.append({"def": {"all": [myget], "hints": {"regular": 1}, "levelParams": [],
                    "name": myget, "safety": "safe", "type": myget_ty, "value": myget_val}})

mygetC = emit(const={"name": myget, "us": []})
lhs = app(mygetC, one, app(mk, zero, zero))
rhs = app(mygetC, one, app(mk, zero, one))


def thm(nm, ty, val):
    i = name(nm)
    out.extend(pending)
    pending.clear()
    out.append({"thm": {"all": [i], "levelParams": [], "name": i, "type": ty, "value": val}})


# theorem bad : myget 1 (mk 0 0) = myget 1 (mk 0 1) := Eq.refl _
thm("bad", app(eq, nat, lhs, rhs), app(refl, nat, lhs))
# theorem lhs_is_zero : myget 1 (mk 0 0) = 0 := rfl
thm("lhs_is_zero", app(eq, nat, lhs, zero), app(refl, nat, zero))
# theorem rhs_is_one : myget 1 (mk 0 1) = 1 := rfl
thm("rhs_is_one", app(eq, nat, rhs, one), app(refl, nat, one))
assert not pending

dump(OUT, out)
