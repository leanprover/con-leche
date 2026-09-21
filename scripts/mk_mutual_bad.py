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


# ---------------------------------------------------------------------------
# The RECURSOR-STAGE twins (milestone M5: the recursor stage as CHECKING).
#
# All five are surgery on `inmodel_mutual`'s third mutual block
#
#     A | mk : B -> A        B | mk : A -> B
#
# whose recursors carry no parameters, no indices, two motives and two
# minor premises, so `A.rec`'s rule for `A.mk` is exactly
#
#     lam mA mB minorA minorB f. minorA f (B.rec mA mB minorA minorB f)
#
# and a single repointed field of one record makes each of the four BAD
# shapes the primitive-recursion abstraction (`abstractIh`,
# `ConLeche/Kernel/Inductives/BlockRec.lean`) is there to refuse.  The
# fifth is GOOD and documents the ACCEPT-SUPERSET: its body is typed but
# is not `minor f ih`.
#
# NOTE (the gate): the uniform route is gated at one member
# (`blockRouteK1Only`) and the recursor CHECK at `blockRecCheckOn`, so
# none of these five is reachable by the shipped checker yet.  Their
# rows in `tests/e2e-expected.txt` are commented `# pending flip` with
# the verdict measured in a scratch build with both gates lifted.
# ---------------------------------------------------------------------------

BASE = "tests/e2e/inmodel_mutual.ndjson"


def exprs(recs):
    """index -> (kind, payload) for every expression record."""
    out = {}
    for r in recs:
        if "ie" in r:
            k = next(x for x in r if x != "ie")
            out[r["ie"]] = (k, r[k])
    return out


def find_ab_block(recs, names):
    """The index of the `A`/`B` inductive record, and its two rec records."""
    a, b = names["InModelMutual.A"], names["InModelMutual.B"]
    for i, r in enumerate(recs):
        if "inductive" in r:
            ts = [t["name"] for t in r["inductive"]["types"]]
            if ts == [a, b]:
                recsd = {rc["name"]: rc for rc in r["inductive"]["recs"]}
                return i, recsd
    raise AssertionError("no A/B block")


def spine(E, e):
    """An application spine as (head index, [arg indices], [node indices])."""
    args, nodes = [], []
    while E[e][0] == "app":
        nodes.append(e)
        args.append(E[e][1]["arg"])
        e = E[e][1]["fn"]
    return e, list(reversed(args)), list(reversed(nodes))


def rule_parts(recs, names):
    """`A.rec`'s rule for `A.mk`, decomposed.

    Returns the rule record, the body's outer application nodes (the
    minor applied to the field and to the recursive call) and the
    recursive call's own spine.
    """
    _, recsd = find_ab_block(recs, names)
    E = exprs(recs)
    arec = recsd[names["InModelMutual.A.rec"]]
    rule = next(ru for ru in arec["rules"] if ru["ctor"] == names["InModelMutual.A.mk"])
    e = rule["rhs"]
    lams = []
    while E[e][0] == "lam":
        lams.append(e)
        e = E[e][1]["body"]
    assert len(lams) == 5, "A.mk's rule does not bind 5 variables"
    head, args, nodes = spine(E, e)          # minorA f call
    assert E[head][0] == "bvar" and len(args) == 2
    chead, cargs, cnodes = spine(E, args[1])  # B.rec mA mB minorA minorB f
    assert E[chead][0] == "const" and len(cargs) == 5
    return rule, (head, args, nodes), (chead, cargs, cnodes), E, lams


def bvar_node(recs, E, n, ins):
    """An expression index holding `bvar n` (created if absent)."""
    for i, (k, v) in E.items():
        if k == "bvar" and v == n:
            return i
    idx = max(list(E) + [r["ie"] for r in ins if "ie" in r]) + 1
    ins.append({"ie": idx, "bvar": n})
    return idx


def twin(out, mutate, note):
    recs = load(BASE)
    names = names_of(recs)
    mutate(recs, names)
    dump(out, recs)
    print("%s: %s" % (out, note))


# 1. the recursive call names the WRONG member's recursor
def _wrong_member(recs, names):
    rule, outer, call, E, _ = rule_parts(recs, names)
    chead = call[0]
    idx = next(i for i, r in enumerate(recs) if r.get("ie") == chead)
    recs[idx] = {"ie": chead, "const": {"name": names["InModelMutual.A.rec"], "us": []}}


twin("tests/e2e/mutual_rec_wrong_member.ndjson", _wrong_member,
     "A.mk's rule recurses through A.rec on a field of type B")


# 2. the recursive call's major is NOT a field of this constructor
def _nonfield(recs, names):
    rule, outer, call, E, _ = rule_parts(recs, names)
    last = call[2][-1]                     # the outermost app of the call
    idx = next(i for i, r in enumerate(recs) if r.get("ie") == last)
    ins = []
    recs[idx]["app"] = dict(recs[idx]["app"], arg=bvar_node(recs, E, 1, ins))
    recs[idx:idx] = ins


twin("tests/e2e/mutual_rec_nonfield.ndjson", _nonfield,
     "A.mk's rule recurses on the minor premise instead of the field")


# 3. an UNGUARDED recursor occurrence: the call is one argument short,
#    so the recursor is passed as an argument rather than applied
def _unguarded(recs, names):
    rule, outer, call, E, _ = rule_parts(recs, names)
    partial = call[2][-2]                  # the spine without its major
    node = outer[2][-1]                    # minorA f <call>
    idx = next(i for i, r in enumerate(recs) if r.get("ie") == node)
    recs[idx]["app"] = dict(recs[idx]["app"], arg=partial)


twin("tests/e2e/mutual_rec_unguarded.ndjson", _unguarded,
     "A.mk's rule passes B.rec partially applied, as an argument")


# 4. the two members' RULES are swapped, so each recursor fires its
#    constructor with the other member's body (the minors permuted
#    across members)
def _swap(recs, names):
    i, recsd = find_ab_block(recs, names)
    arec = recsd[names["InModelMutual.A.rec"]]
    brec = recsd[names["InModelMutual.B.rec"]]
    ar = next(ru for ru in arec["rules"] if ru["ctor"] == names["InModelMutual.A.mk"])
    br = next(ru for ru in brec["rules"] if ru["ctor"] == names["InModelMutual.B.mk"])
    ar["rhs"], br["rhs"] = br["rhs"], ar["rhs"]


twin("tests/e2e/mutual_rec_rules_swapped.ndjson", _swap,
     "A.rec and B.rec exchange their rule bodies")


# 5. GOOD: a body that is TYPED but is not `minor f ih` — the canonical
#    body under an identity redex.  Documents the accept-superset: the
#    check types the rule's body, it does not compare it with a
#    generated term.
def _redex(recs, names):
    rule, outer, call, E, lams = rule_parts(recs, names)
    body = outer[2][-1]                    # minorA f (B.rec … f)
    ins = []
    b0 = bvar_node(recs, E, 0, ins)
    b4 = bvar_node(recs, E, 4, ins)
    nxt = max(list(E) + [r["ie"] for r in ins]) + 1
    amk = None
    for i, (k, v) in E.items():
        if k == "const" and v["name"] == names["InModelMutual.A.mk"] and v["us"] == []:
            amk = i
    if amk is None:
        amk = nxt
        ins.append({"ie": amk, "const": {"name": names["InModelMutual.A.mk"], "us": []}})
        nxt += 1
    mk_f = nxt                              # A.mk f
    ins.append({"ie": mk_f, "app": {"fn": amk, "arg": b0}})
    nxt += 1
    dom = nxt                               # motiveA (A.mk f)
    ins.append({"ie": dom, "app": {"fn": b4, "arg": mk_f}})
    nxt += 1
    idf = nxt                               # fun (x : motiveA (A.mk f)) => x
    ins.append({"ie": idf, "lam": {"binderInfo": "default",
                                   "name": names["InModelMutual.A"], "type": dom,
                                   "body": b0}})
    nxt += 1
    red = nxt                               # (fun x => x) (minorA f ih)
    ins.append({"ie": red, "app": {"fn": idf, "arg": body}})
    # the new nodes carry indices above every index the file defines
    # (nothing clashes) and go in FRONT of the record that will use
    # them — the innermost `λ` of the rule, whose body they replace;
    # the export's records are not in index order, so the insertion
    # point is that record's own line
    idx = next(j for j, r in enumerate(recs) if r.get("ie") == lams[-1])
    recs[idx]["lam"] = dict(recs[idx]["lam"], body=red)
    recs[idx:idx] = ins


twin("tests/e2e/mutual_rec_body_redex.ndjson", _redex,
     "A.mk's rule body is the canonical one under an identity redex (GOOD)")


# 6. a recursor with a MISSING rule.  Completeness is a soundness
#    requirement — `Nat.rec` with a rule for `zero` only would prove
#    `∀ n, M n` from `M 0` — and the uniform route already enforces it
#    twice: the recursor records' structural pin
#    (`blockRecPinOk`: `rules.length == ms.ctors.length`, one rule per
#    constructor of the member IN ORDER, each naming its constructor
#    with its field count) and the rule loop itself
#    (`checkBlockRules`, whose two lists must run out together).  The
#    twin drops `Even.zero`'s rule from `Even.rec`.
def _missing_rule(recs, names):
    a, b = names["InModelMutual.Even"], names["InModelMutual.Odd"]
    blk = None
    for r in recs:
        if "inductive" in r and [t["name"] for t in r["inductive"]["types"]] == [a, b]:
            blk = r
    assert blk is not None, "no Even/Odd block"
    erec = next(rc for rc in blk["inductive"]["recs"]
                if rc["name"] == names["InModelMutual.Even.rec"])
    assert len(erec["rules"]) == 2
    erec["rules"] = [ru for ru in erec["rules"]
                     if ru["ctor"] != names["InModelMutual.Even.zero"]]


twin("tests/e2e/mutual_rec_missing_rule.ndjson", _missing_rule,
     "Even.rec loses its rule for Even.zero")


# 7. a mutual `Prop` block whose recursor's CONCLUSION is not a
#    proposition.  `InModelMutual.A`/`B` are `Sort 0` with two members,
#    so official's `elim_only_at_universe_zero` — `blockLargeElimAllowed`
#    (`ConLeche/Kernel/Inductives/BlockRec.lean`) — allows no large
#    eliminator and the uniform route requires the conclusion's sort to
#    be `Sort 0`.  The twin retypes `A.rec`'s FIRST motive binder from
#    `A -> Prop` to `A -> Type`, which is the whole edit: the rules
#    still type-check, only the elimination restriction refuses it.
def _prop_concl(recs, names):
    i, recsd = find_ab_block(recs, names)
    arec = recsd[names["InModelMutual.A.rec"]]
    E = exprs(recs)
    top = arec["type"]
    assert E[top][0] == "forallE", "A.rec's type is not a telescope"
    mty = E[top][1]["type"]
    assert E[mty][0] == "forallE", "A.rec's motive is not a telescope"
    assert E[E[mty][1]["body"]][0] == "sort", "the motive's codomain is not a sort"
    # the level `1` (succ zero), created if the file has none
    ins, lvls = [], {}
    for r in recs:
        if "il" in r:
            k = next(x for x in r if x != "il")
            lvls[r["il"]] = (k, r[k])
    one = next((i for i, (k, v) in lvls.items() if k == "succ" and v == 0), None)
    nxtl = max(list(lvls) + [0]) + 1
    if one is None:
        one = nxtl
        ins.append({"il": one, "succ": 0})
    nxt = max(E) + 1
    s1 = nxt
    ins.append({"ie": s1, "sort": one})
    mty2 = nxt + 1
    ins.append({"ie": mty2, "forallE": dict(E[mty][1], body=s1)})
    top2 = nxt + 2
    ins.append({"ie": top2, "forallE": dict(E[top][1], type=mty2)})
    arec["type"] = top2
    recs[i:i] = ins


twin("tests/e2e/mutual_rec_prop_concl.ndjson", _prop_concl,
     "A.rec's motive is A -> Type on a mutual Prop block")
