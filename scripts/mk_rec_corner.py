#!/usr/bin/env python3
"""The RECURSOR corner cases at k = 1, for the uniform route's
motive-free recursor CHECK (DESIGN.md, amendment 2026-09-21 "the
recursor check knows no motives" and the ruling of the same day: the
check reads `rulePrefix = majorIdx` off the recursor RECORD, types the
rule's residue, and accepts any primitively recursive shape — it does
not compare the rule with a generated term).

Each twin is one edit of a committed good stream.  Where the edit
changes a recursor's TYPE, the base's definitions and theorems are
dropped from the twin: they apply the recursor at its old type and
would reject for their own reason, at their own record, instead of at
the block.  Where it changes only a rule (or adds one), they stay, so
the stream still fires iota.

Bases: `direct_fix_nat` (`Nat'` — one nullary and one recursive
constructor, no parameters, no indices; `List' (α)` — one parameter)
and `direct_fix_refl` (`Iter f n` — a REFLEXIVE field
`h : forall k, Nat.le k n -> Iter f k`, so the rule's recursive call is
`Iter.rec ... k (h k a)` under two lambdas).

  corner_rec_extra_binder   an EXTRA minor premise `(junk : Nat')`
      between `Nat'.rec`'s minors and its major, `numMinors` bumped to
      match and every rule's lambda prefix extended by one.  The
      record stays self-consistent (`majorIdx = rulePrefix = 4`), and
      the eliminator is merely WEAKER than the generated one — the
      accept-superset: TARGET 0.
  corner_rec_no_ih          `Nat'.rec` shaped like `casesOn`: the
      `succ` minor loses its `n_ih : motive n` premise and the `succ`
      rule loses its recursive call, so the rule's body IGNORES the
      inductive hypothesis it no longer has.  That is a legitimate
      primitive recursion (it is `Nat'.casesOn`): TARGET 0.
  corner_rec_call_redex     `Iter.step`'s rule recurses on
      `h ((fun x : Nat => x) k) a` — the reflexive field at an argument
      vector that is DEFEQ to, but not syntactically, the bound
      variable.  The guard DOES abstract the argument vector; what it
      demands syntactically is the call's INDEX arguments, which must
      be the field's stored index expressions at that vector, and `k`
      is the index-carrying argument here: TARGET 1.  Its two
      accept-side twins are `corner_rec_wtype_redex` and
      `corner_rec_redex_nonindex` below.
  corner_rec_call_const_bad the same call at `h Nat.zero a`: a constant
      where the bound variable belongs.  `a : Nat.le k n` is not a
      `Nat.le 0 n`, so the residue is ill-typed however the guard reads
      it — the "different `a⃗`" case is only ever accepted when it
      still types.  TARGET 1.
  corner_rec_closed_major   `Nat'.rec`'s `succ` rule recurses on
      `Nat'.zero` — a closed term of the type, not a field of the
      constructor.  `motive Nat'.zero` is not the `motive n` the minor
      asks for, and the recursion is not structural: TARGET 1.
  corner_rec_alien_rule     `Nat'.rec` carries a THIRD rule, for
      `List'.nil` — a constructor of another type.  A rule per
      constructor of the major's type is what completeness means:
      TARGET 1.
  corner_rec_major_params   `List'.rec`'s major is `t : List' Nat'`
      where `t : List' α` belongs — the major at the wrong parameters,
      so the recursor is not this block's: TARGET 1.
  corner_rec_reserved_name  `Nat'`'s recursor is named `List.cons` — a
      name the `String`-literal guard looks up.  A recursor under a
      guarded name could flip the guard across its own cons, so the
      recursor stage refuses it: TARGET 1.

Usage: scripts/mk_rec_corner.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

CHILD_KEYS = {"forallE": ("type", "body"), "lam": ("type", "body"),
              "app": ("fn", "arg"), "letE": ("type", "value", "body"),
              "proj": ("struct",), "mdata": ("expr",)}
# the child positions that are UNDER the node's own binder
UNDER = {"forallE": ("body",), "lam": ("body",), "letE": ("body",)}


def dump(name, recs):
    p = os.path.join(ROOT, "tests/e2e", name)
    with open(p, "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s: %d lines" % (name, len(recs)))


class Twin:
    """One committed stream, opened for surgery.

    New expression and name records are collected in `self.ins` and
    written out in FRONT of the declaration record that uses them (the
    stream defines an index before it is used).
    """

    def __init__(self, src):
        p = os.path.join(ROOT, "tests/e2e", src + ".ndjson")
        self.recs = [json.loads(l) for l in open(p).read().splitlines()]
        self.E = {r["ie"]: r for r in self.recs if "ie" in r}
        self.nxt_ie = max(self.E) + 1
        self.nxt_in = max([r["in"] for r in self.recs if "in" in r] + [0]) + 1
        self.ins = []
        raw = {}
        for r in self.recs:
            if "in" in r and "str" in r:
                raw[r["in"]] = (r["str"]["pre"], r["str"]["str"])
            elif "in" in r and "num" in r:
                raw[r["in"]] = (r["num"]["pre"], str(r["num"]["i"]))

        def full(i):
            if i == 0:
                return ""
            pre, s = raw[i]
            p = full(pre)
            return s if p == "" else p + "." + s

        self.names = {full(i): i for i in raw}

    # --- emitting ---------------------------------------------------
    def ex(self, node):
        i = self.nxt_ie
        self.nxt_ie += 1
        r = dict(node, ie=i)
        self.ins.append(r)
        self.E[i] = r
        return i

    def name(self, s):
        if s in self.names:
            return self.names[s]
        i = self.nxt_in
        self.nxt_in += 1
        self.ins.append({"in": i, "str": {"pre": 0, "str": s}})
        self.names[s] = i
        return i

    def fresh_name(self, parts):
        """A NEW name record for `parts`, emitted in front of the block
        under surgery.  `name` reuses the stream's index, which is no
        good when the stream declares that name only LATER (the alien
        rule below names a constructor of a block that follows)."""
        pre = 0
        for part in parts:
            i = self.nxt_in
            self.nxt_in += 1
            self.ins.append({"in": i, "str": {"pre": pre, "str": part}})
            pre = i
        return pre

    def const(self, s, us=None):
        n = self.names[s]
        for r in self.E.values():
            if "const" in r and r["const"]["name"] == n \
                    and (us is None or r["const"]["us"] == us):
                return r["ie"]
        return self.ex({"const": {"name": n, "us": us or []}})

    # --- generic rewrites -------------------------------------------
    def map(self, ie, f, depth=0, memo=None):
        """Rebuild `ie`, replacing each node by `f(ie, depth)` when that
        is not None; shared nodes are copied along the path only."""
        if memo is None:
            memo = {}
        key = (ie, depth)
        if key in memo:
            return memo[key]
        got = f(ie, depth)
        if got is not None:
            memo[key] = got
            return got
        r = self.E[ie]
        k = next((k for k in CHILD_KEYS if k in r), None)
        if k is None:
            memo[key] = ie
            return ie
        node = dict(r[k])
        changed = False
        for ck in CHILD_KEYS[k]:
            if ck in node and isinstance(node[ck], int):
                d = depth + 1 if ck in UNDER.get(k, ()) else depth
                c = self.map(node[ck], f, d, memo)
                if c != node[ck]:
                    node[ck] = c
                    changed = True
        out = self.ex({k: node}) if changed else ie
        memo[key] = out
        return out

    def lift(self, ie, d, cutoff=0):
        """de Bruijn lift: free variables at or above `cutoff` move by `d`."""
        def f(i, depth):
            r = self.E[i]
            if "bvar" in r and r["bvar"] >= cutoff + depth:
                return self.ex({"bvar": r["bvar"] + d})
            return None
        return self.map(ie, f)

    def replace(self, ie, old, new):
        """Replace every occurrence of the node `old` by `new`."""
        return self.map(ie, lambda i, _d: new if i == old else None)

    # --- locating ---------------------------------------------------
    def block(self, member):
        n = self.names[member]
        for i, r in enumerate(self.recs):
            if "inductive" in r and any(t["name"] == n for t in r["inductive"]["types"]):
                return i, r["inductive"]
        raise SystemExit("no block for " + member)

    def rec(self, member, recname):
        _, blk = self.block(member)
        n = self.names[recname]
        return next(rc for rc in blk["recs"] if rc["name"] == n)

    def rule(self, member, recname, ctor):
        n = self.names[ctor]
        return next(ru for ru in self.rec(member, recname)["rules"] if ru["ctor"] == n)

    def binders(self, ie, n):
        """The first `n` binder records of a telescope, outermost first."""
        out = []
        for _ in range(n):
            r = self.E[ie]
            k = "forallE" if "forallE" in r else "lam"
            out.append(r)
            ie = r[k]["body"]
        return out

    # --- writing ----------------------------------------------------
    def write(self, out, member, drop_defs=False):
        bi, _ = self.block(member)
        recs = self.recs[:bi] + self.ins + self.recs[bi:]
        if drop_defs:
            recs = [r for r in recs
                    if not ("definition" in r or "theorem" in r)]
        dump(out + ".ndjson", recs)


def rebuild_prefix(t, ie, n, rebuild_rest):
    """Re-thread the first `n` binders of the telescope at `ie` around a
    new tail, returning the new root."""
    chain = []
    e = ie
    for _ in range(n):
        r = t.E[e]
        k = "forallE" if "forallE" in r else "lam"
        chain.append((r, k))
        e = r[k]["body"]
    new = rebuild_rest(e)
    for r, k in reversed(chain):
        new = t.ex({k: dict(r[k], body=new)})
    return new


# --- corner_rec_extra_binder ----------------------------------------
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
junk = t.name("junk")
nat = t.const("Nat'")
rec_const = t.const("Nat'.rec")
pre = rc["numParams"] + rc["numMotives"] + rc["numMinors"]   # 0 + 1 + 2


def _spine(ie):
    args = []
    while "app" in t.E[ie]:
        args.append(t.E[ie]["app"]["arg"])
        ie = t.E[ie]["app"]["fn"]
    return ie, list(reversed(args))


def _pass_junk(i, depth):
    """`Nat'.rec m z s major`  ->  `Nat'.rec m z s junk major`.  `depth`
    counts the binders between the recursor's new minor and this node,
    which is exactly the new argument's de Bruijn index."""
    if "app" not in t.E[i]:
        return None
    head, args = _spine(i)
    if head != rec_const or len(args) != pre + 1:
        return None
    e = head
    for a in args[:pre] + [t.ex({"bvar": depth})] + args[pre:]:
        e = t.ex({"app": {"fn": e, "arg": a}})
    return e


def _ins_forall(rest):
    return t.ex({"forallE": {"binderInfo": "default", "name": junk,
                             "type": nat, "body": t.lift(rest, 1)}})


def _ins_lam(rest):
    return t.ex({"lam": {"binderInfo": "default", "name": junk, "type": nat,
                         "body": t.map(t.lift(rest, 1), _pass_junk)}})


rc["type"] = rebuild_prefix(t, rc["type"], pre, _ins_forall)
for ru in rc["rules"]:
    ru["rhs"] = rebuild_prefix(t, ru["rhs"], pre, _ins_lam)
rc["numMinors"] += 1
t.write("corner_rec_extra_binder", "Nat'", drop_defs=True)

# --- corner_rec_no_ih -----------------------------------------------
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
succ_minor = t.binders(rc["type"], 3)[2]["forallE"]["type"]     # the `succ` premise
inner = t.E[succ_minor]["forallE"]                              # `(n : Nat') -> ...`
ih = t.E[inner["body"]]["forallE"]                              # `(n_ih : motive n) -> ...`
no_ih = t.ex({"forallE": dict(inner, body=t.lift(ih["body"], -1))})
rc["type"] = t.replace(rc["type"], succ_minor, no_ih)
for ru in rc["rules"]:
    ru["rhs"] = t.replace(ru["rhs"], succ_minor, no_ih)
sr = t.rule("Nat'", "Nat'.rec", "Nat'.succ")
body = t.binders(sr["rhs"], 4)[3]["lam"]["body"]                # `succ n (Nat'.rec ... n)`
sr["rhs"] = t.replace(sr["rhs"], body, t.E[body]["app"]["fn"])  # drop the call
t.write("corner_rec_no_ih", "Nat'", drop_defs=True)

# --- corner_rec_call_redex / corner_rec_call_const_bad ---------------
# `Iter.step`'s rule body is `step n h (fun k a => Iter.rec f m b s k (h k a))`;
# the `k` INSIDE `h k a` is what moves.  The rewrite replaces the whole
# `Iter.rec` SPINE, not the `h k` node: the exporter shares that node
# with the `step n` application one binder level up.
def _iter_call(out, new_k):
    t = Twin("direct_fix_refl")
    ru = t.rule("Iter", "Iter.rec", "Iter.step")
    inner = t.binders(ru["rhs"], 6)[5]["lam"]["body"]           # `step n h (fun k a => ...)`
    lam_k = t.E[inner]["app"]["arg"]
    spine = t.E[t.E[lam_k]["lam"]["body"]]["lam"]["body"]       # `Iter.rec ... (h k a)`
    major = t.E[spine]["app"]["arg"]                            # `h k a`
    hk = t.E[major]["app"]["fn"]                                # `h k`
    assert t.E[t.E[hk]["app"]["arg"]].get("bvar") == 1, "not the bound `k`"
    new_hk = t.ex({"app": {"fn": t.E[hk]["app"]["fn"], "arg": new_k(t)}})
    new_major = t.ex({"app": dict(t.E[major]["app"], fn=new_hk)})
    ru["rhs"] = t.replace(ru["rhs"], spine,
                          t.ex({"app": dict(t.E[spine]["app"], arg=new_major)}))
    t.write(out, "Iter")


def _redex(t):
    """`(fun x : Nat => x) k` — defeq to `k`, syntactically not `k`."""
    idf = t.ex({"lam": {"binderInfo": "default", "name": t.name("x"),
                        "type": t.const("Nat"), "body": t.ex({"bvar": 0})}})
    return t.ex({"app": {"fn": idf, "arg": t.ex({"bvar": 1})}})


def _const(t):
    return t.const("Nat.zero")


_iter_call("corner_rec_call_redex", _redex)
_iter_call("corner_rec_call_const_bad", _const)

# --- corner_rec_closed_major ----------------------------------------
t = Twin("direct_fix_nat")
sr = t.rule("Nat'", "Nat'.rec", "Nat'.succ")
body = t.binders(sr["rhs"], 4)[3]["lam"]["body"]                # `succ n (Nat'.rec ... n)`
call = t.E[body]["app"]["arg"]                                  # `Nat'.rec motive zero succ n`
sr["rhs"] = t.map(sr["rhs"],
                  lambda i, _d: (t.ex({"app": dict(t.E[call]["app"],
                                                   arg=t.const("Nat'.zero"))})
                                 if i == call else None))
t.write("corner_rec_closed_major", "Nat'")

# --- corner_rec_alien_rule ------------------------------------------
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
zero_rule = t.rule("Nat'", "Nat'.rec", "Nat'.zero")
rc["rules"] = rc["rules"] + [{"ctor": t.fresh_name(["List'", "nil"]), "nfields": 0,
                              "rhs": zero_rule["rhs"]}]
t.write("corner_rec_alien_rule", "Nat'")

# --- corner_rec_major_params ----------------------------------------
t = Twin("direct_fix_nat")
rc = t.rec("List'", "List'.rec")
pre = rc["numParams"] + rc["numMotives"] + rc["numMinors"]      # 1 + 1 + 2
major = t.binders(rc["type"], pre + 1)[pre]["forallE"]          # `(t : List' α)`
alpha = t.E[major["type"]]["app"]["arg"]
assert t.E[alpha].get("bvar") == 3, "the major's parameter is not the block's"
bad = t.ex({"app": dict(t.E[major["type"]]["app"], arg=t.const("Nat'"))})
# ONLY the major moves: `List' α` at this depth is the node the `cons`
# minor's `tail` binder uses too, so the telescope is re-threaded around
# a fresh major binder instead of the node being replaced everywhere.
rc["type"] = rebuild_prefix(t, rc["type"], pre,
                            lambda rest: t.ex({"forallE": dict(major, type=bad)}))
t.write("corner_rec_major_params", "List'", drop_defs=True)

# =====================================================================
# THE NAMING RULING AND D-d (2026-09-21)
#
# The maintainer's two further rulings: recursor NAMES are the stream's
# business (a member may carry any number of recursors, and a recursor
# is assigned to its member by its MAJOR premise), and D-d — one
# elimination level for the whole family.  Four twins.
# =====================================================================

# --- corner_rec_two_recursors ---------------------------------------
# `Nat'` with a SECOND recursor `Nat'.rec2`, shaped like `casesOn` (the
# `succ` minor has no `n_ih` premise and its rule makes no recursive
# call).  Two recursors on ONE member, both legitimate eliminators:
# TARGET 0.  `Nat'.rec` is untouched, so the stream's definitions still
# fire iota through it.
t = Twin("direct_fix_nat")
_, blk = t.block("Nat'")
rc = t.rec("Nat'", "Nat'.rec")
succ_minor = t.binders(rc["type"], 3)[2]["forallE"]["type"]
inner = t.E[succ_minor]["forallE"]
ih = t.E[inner["body"]]["forallE"]
no_ih = t.ex({"forallE": dict(inner, body=t.lift(ih["body"], -1))})
rules2 = []
for ru in rc["rules"]:
    rules2.append({"ctor": ru["ctor"], "nfields": ru["nfields"],
                   "rhs": t.replace(ru["rhs"], succ_minor, no_ih)})
sr2 = next(ru for ru in rules2 if ru["ctor"] == t.names["Nat'.succ"])
body = t.binders(sr2["rhs"], 4)[3]["lam"]["body"]               # `succ n (Nat'.rec ... n)`
sr2["rhs"] = t.replace(sr2["rhs"], body, t.E[body]["app"]["fn"])
blk["recs"] = blk["recs"] + [dict(rc, name=t.fresh_name(["Nat'", "rec2"]),
                                  type=t.replace(rc["type"], succ_minor, no_ih),
                                  rules=rules2)]
t.write("corner_rec_two_recursors", "Nat'")

# --- corner_rec_hoolahoop -------------------------------------------
# `Nat'`'s recursor is called `Nat'.hoolahoop`.  Nothing else changes —
# its type, its rules and its major are the generated ones — so the
# motive-free check accepts it: TARGET 0.  The definitions are dropped
# (they apply `Nat'.rec`, a name the twin no longer declares).
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
hoola = t.fresh_name(["Nat'", "hoolahoop"])
_recn = t.names["Nat'.rec"]
# the constant is renamed EVERYWHERE — in the rules and in the stream's
# own definitions, which then fire iota through `Nat'.hoolahoop`
for r in t.E.values():
    if "const" in r and r["const"]["name"] == _recn:
        r["const"]["name"] = hoola
rc["name"] = hoola
# the NAME record goes to the front: the `Nat'.rec` const nodes it
# renames are emitted long before the block
t.recs = t.recs[:1] + t.ins + t.recs[1:]
t.ins = []
t.write("corner_rec_hoolahoop", "Nat'")

# --- corner_rec_reserved_name ---------------------------------------
# `Nat'`'s recursor is called `List.cons` — a name one of the
# environment's own GUARDS looks up (`strLitSupported`'s
# `listConsTyOk` slot).  Recursor names are the stream's business, but
# not THIS free: consing a recursor under a guarded name could flip a
# literal guard, and a string literal would read as one thing below
# the block's recursors and as another above them.  The recursor
# stage refuses the name outright (`blockRecNamesUnreserved`):
# TARGET 1.  (The name-set conformance check would refuse it too; the
# reservation check runs first, so the twin exercises it.)
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
guarded = t.fresh_name(["List", "cons"])
_recn = t.names["Nat'.rec"]
for r in t.E.values():
    if "const" in r and r["const"]["name"] == _recn:
        r["const"]["name"] = guarded
rc["name"] = guarded
t.recs = t.recs[:1] + t.ins + t.recs[1:]
t.ins = []
t.write("corner_rec_reserved_name", "Nat'")

# --- corner_rec_rule_missing ----------------------------------------
# `Nat'.rec` without its `Nat'.zero` rule.  Rule COMPLETENESS is a
# soundness requirement and stays in the record's pin whatever the
# recursor is called: TARGET 1.
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
rc["rules"] = [ru for ru in rc["rules"] if ru["ctor"] != t.names["Nat'.zero"]]
t.write("corner_rec_rule_missing", "Nat'", drop_defs=True)

# --- mutual_rec_elim_levels -----------------------------------------
# D-d: the mutual block `MutA`/`MutB` (both `Type`) with `MutB.rec`'s
# OWN motive retyped `MutB -> Type` while `MutA.rec`'s stays
# `MutA -> Sort u`.  Each recursor is a well-typed eliminator on its
# own; the FAMILY eliminates at two different levels, which official
# never produces — one elimination level parameter is shared:
# TARGET 1.
t = Twin("tower_mutual")
rc = t.rec("MutB", "MutB.rec")
assert rc["numParams"] == 0 and rc["numMotives"] == 2
_one = next((r["il"] for r in t.recs if "il" in r and r.get("succ") == 0), None)
assert _one is not None, "the stream has no level 1"
_top = t.E[rc["type"]]["forallE"]                               # motive_MutA
_snd = t.E[_top["body"]]["forallE"]                             # motive_MutB
assert t.E[t.E[_snd["type"]]["forallE"]["body"]].get("sort") is not None
_mty = t.ex({"forallE": dict(t.E[_snd["type"]]["forallE"],
                             body=t.ex({"sort": _one}))})
rc["type"] = t.ex({"forallE": dict(_top,
                                   body=t.ex({"forallE": dict(_snd, type=_mty)}))})
t.write("mutual_rec_elim_levels", "MutB")

# --- corner_rec_two_callees -----------------------------------------
# `Nat'` with a second recursor `Nat'.rec2` whose TYPE is `Nat'.rec`'s
# own, and whose `succ` rule recurses on the field `n` through BOTH
# recursors — itself and the first:
#
#   λ m z s n. s n ((fun _ : m n => Nat'.rec2 m z s n) (Nat'.rec m z s n))
#
# Two guarded calls on ONE field with two different callees, so the
# rule's frame carries TWO `ih` openers keyed by (field, callee), each
# typed from ITS callee's own type at the spine's arguments (the
# maintainer's ruling: the family is primitively MUTUALLY recursive).
# TARGET 0.
t = Twin("direct_fix_nat")
_, blk = t.block("Nat'")
rc = t.rec("Nat'", "Nat'.rec")
rec2n = t.fresh_name(["Nat'", "rec2"])
sr = t.rule("Nat'", "Nat'.rec", "Nat'.succ")
body = t.binders(sr["rhs"], 4)[3]["lam"]["body"]                # `s n (Nat'.rec m z s n)`
call_rec = t.E[body]["app"]["arg"]                              # `Nat'.rec m z s n`
_head = call_rec
while "app" in t.E[_head]:
    _head = t.E[_head]["app"]["fn"]
assert "const" in t.E[_head], "the call's head is not a constant"
call_rec2 = t.replace(t.lift(call_rec, 1), _head,
                      t.ex({"const": dict(t.E[_head]["const"], name=rec2n)}))
motive_n = t.ex({"app": {"fn": t.ex({"bvar": 3}), "arg": t.ex({"bvar": 0})}})
dead = t.ex({"lam": {"binderInfo": "default", "name": t.name("ih2"),
                     "type": motive_n, "body": call_rec2}})
new_body = t.ex({"app": {"fn": t.E[body]["app"]["fn"],
                         "arg": t.ex({"app": {"fn": dead, "arg": call_rec}})}})
rules2 = [({"ctor": ru["ctor"], "nfields": ru["nfields"],
            "rhs": rebuild_prefix(t, ru["rhs"], 4, lambda _e: new_body)}
           if ru["ctor"] == t.names["Nat'.succ"] else dict(ru))
          for ru in rc["rules"]]
blk["recs"] = blk["recs"] + [dict(rc, name=rec2n, rules=rules2)]
t.write("corner_rec_two_callees", "Nat'")

# --- corner_rec_dom_recursor ----------------------------------------
# `Nat'.rec`'s `succ` rule binds its FIELD at a domain that mentions
# the recursor CONSTANT:
#
#   λ m z s (n : (fun _ : T_rec => Nat') Nat'.rec). s n (Nat'.rec m z s n)
#
# The domain β-reduces to `Nat'`, so the rule's own typing (at the
# RULE-LESS recursor environment, which HOLDS `Nat'.rec`) and the
# binder-by-binder defeq against the openers' stored types (at the
# CONSTRUCTORS' environment, where a β-redex never looks the head up)
# both pass, and `stripLams` puts the domain out of the residue's
# reach.  Nothing else of the stage constrains a rule's λ-domains, so
# before the domains' own resolution guard the stream was ACCEPTED
# while its domain does not READ at the constructors' environment —
# the model's tower fit needs `ConstsBound envC` there and no check
# made it available.  TARGET 1.
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
sr = t.rule("Nat'", "Nat'.rec", "Nat'.succ")
_lps = rc["levelParams"]
_us = next(r["const"]["us"] for r in t.E.values()
           if "const" in r and r["const"]["name"] == t.names["Nat'.rec"])
_dom = t.ex({"app": {
    "fn": t.ex({"lam": {"binderInfo": "default", "name": t.name("_"),
                        "type": rc["type"], "body": t.const("Nat'")}}),
    "arg": t.const("Nat'.rec", _us)}})
_chain = t.binders(sr["rhs"], 4)
assert all("lam" in r for r in _chain), "the rule is not a λ-telescope"
_new = t.ex({"lam": dict(_chain[3]["lam"], type=_dom)})
for _r in reversed(_chain[:3]):
    _new = t.ex({"lam": dict(_r["lam"], body=_new)})
sr["rhs"] = _new
t.write("corner_rec_dom_recursor", "Nat'")

# --- corner_rec_redex_nonindex / corner_rec_wtype_redex --------------
# Where the primitive-recursion guard's SYNTACTIC demand really is.
# The guard does NOT demand a syntactic argument vector: it abstracts
# the spine, and what it demands syntactically is the call's INDEX
# arguments, which must be the recursive field's stored index
# expressions AT that vector.  These two pin the accept side of that
# reading, so that nobody "fixes" the guard into accepting less.
#
#   corner_rec_wtype_redex      `W'` is reflexive and NOT indexed, so
#       no argument of the call carries an index; the same
#       `(fun x : β a => x) b` redex in the recursive call's argument
#       vector is accepted.  TARGET 0.
#   corner_rec_redex_nonindex   the very block `corner_rec_call_redex`
#       edits, with the redex moved from the index-carrying telescope
#       argument `k` to the other one, `a : Nat.le k n`, which carries
#       none.  TARGET 0, where the committed twin is TARGET 1.
t = Twin("direct_fix_wtype")
ru = t.rule("W'", "W'.rec", "W'.sup")
body = t.binders(ru["rhs"], 6)[5]["lam"]["body"]   # `minor a f (fun b => rec … (f b))`
lam_b = t.E[body]["app"]["arg"]
ty_ba = t.E[lam_b]["lam"]["type"]                  # `β a`, outside the `b` binder
spine = t.E[lam_b]["lam"]["body"]                  # `W'.rec α β motive sup (f b)`
major = t.E[spine]["app"]["arg"]                   # `f b`
assert t.E[t.E[major]["app"]["arg"]].get("bvar") == 0, "not the bound `b`"
idf = t.ex({"lam": {"binderInfo": "default", "name": t.name("x"),
                    "type": t.lift(ty_ba, 1), "body": t.ex({"bvar": 0})}})
redex = t.ex({"app": {"fn": idf, "arg": t.ex({"bvar": 0})}})
new_major = t.ex({"app": dict(t.E[major]["app"], arg=redex)})
ru["rhs"] = t.replace(ru["rhs"], spine,
                      t.ex({"app": dict(t.E[spine]["app"], arg=new_major)}))
t.write("corner_rec_wtype_redex", "W'")

t = Twin("direct_fix_refl")
ru = t.rule("Iter", "Iter.rec", "Iter.step")
inner = t.binders(ru["rhs"], 6)[5]["lam"]["body"]  # `step n h (fun k a => …)`
lam_k = t.E[inner]["app"]["arg"]
lam_a = t.E[lam_k]["lam"]["body"]
ty_a = t.E[lam_a]["lam"]["type"]                   # `Nat.le k n`
spine = t.E[lam_a]["lam"]["body"]                  # `Iter.rec f m b s k (h k a)`
major = t.E[spine]["app"]["arg"]                   # `h k a`
assert t.E[t.E[major]["app"]["arg"]].get("bvar") == 0, "not the bound `a`"
idf = t.ex({"lam": {"binderInfo": "default", "name": t.name("x"),
                    "type": t.lift(ty_a, 1), "body": t.ex({"bvar": 0})}})
redex = t.ex({"app": {"fn": idf, "arg": t.ex({"bvar": 0})}})
new_major = t.ex({"app": dict(t.E[major]["app"], arg=redex)})
ru["rhs"] = t.replace(ru["rhs"], spine,
                      t.ex({"app": dict(t.E[spine]["app"], arg=new_major)}))
t.write("corner_rec_redex_nonindex", "Iter")

# --- corner_rec_body_redex (lane CONF1, 2026-09-23) -------------------
# `Nat'.rec`'s `succ` rule is the generated body under an identity
# redex:
#
#   λ m z s n. (fun x : m (Nat'.succ n) => x) (s n (Nat'.rec m z s n))
#
# A valid primitive recursion — the rule's residue types, the guarded
# call is the generated one — but not the rule official generates, so
# official rejects it.  The k = 1 twin of `mutual_rec_body_redex`: at
# one member the recursor CONFORMANCE check (the generate-and-compare
# kept after the primitive-recursion check, `checkBlockRecConform`)
# brings the verdict back to official's; at two members no generator
# exists and the twin stays the accept-superset.  The definitions stay
# (only a rule changes), so iota still fires through the rule.
# TARGET 1 (conformance).
t = Twin("direct_fix_nat")
sr = t.rule("Nat'", "Nat'.rec", "Nat'.succ")
body = t.binders(sr["rhs"], 4)[3]["lam"]["body"]                # `s n (Nat'.rec m z s n)`
_dom = t.ex({"app": {"fn": t.ex({"bvar": 3}),                   # `m (Nat'.succ n)`
                     "arg": t.ex({"app": {"fn": t.const("Nat'.succ"),
                                          "arg": t.ex({"bvar": 0})}})}})
_idf = t.ex({"lam": {"binderInfo": "default", "name": t.name("x"),
                     "type": _dom, "body": t.ex({"bvar": 0})}})
sr["rhs"] = rebuild_prefix(t, sr["rhs"], 4,
                           lambda _e: t.ex({"app": {"fn": _idf, "arg": body}}))
t.write("corner_rec_body_redex", "Nat'")

# --- corner_rec_empty_prefix (lane CONF1, 2026-09-23; lane RM49's witness)
# `inductive T : Prop | c` closed by a recursor with an EMPTY rule
# prefix: `T.rec : (t : T) → True` — no motive, no minor, so
# `numParams + numMotives + numMinors = 0` — and the rule
# `T.rec T.c ↦ True.intro`, which binds no variable at all.  The
# equation is true and the kernel's recursor CHECK accepts it (lane
# FLOOR removed the `nP + k ≤ rP` floor: a motive is a parameter like
# any other; the model reads a rule binding no variable through the ι
# law).  From a STREAM the record is refused by the frontend's field
# validation ("declares 0 motives"), which is what the fixture pins,
# and the one-member conformance check would refuse it behind that.
# TARGET 1.
t = Twin("and_rec_opaque")
_T = t.fresh_name(["T"])
_Tc = t.nxt_in; t.nxt_in += 1; t.ins.append({"in": _Tc, "str": {"pre": _T, "str": "c"}})
_Tr = t.nxt_in; t.nxt_in += 1; t.ins.append({"in": _Tr, "str": {"pre": _T, "str": "rec"}})
_tn = t.name("t")
_prop = next(r["ie"] for r in t.recs if r.get("sort") == 0 and "ie" in r)
_constT = t.ex({"const": {"name": _T, "us": []}})
_recTy = t.ex({"forallE": {"binderInfo": "default", "name": _tn, "type": _constT,
                           "body": t.const("True", [])}})
_intro = t.const("True.intro", [])
_blk = {"inductive": {
    "ctors": [{"cidx": 0, "induct": _T, "isUnsafe": False, "levelParams": [], "name": _Tc,
               "numFields": 0, "numParams": 0, "type": _constT}],
    "recs": [{"all": [_T], "isUnsafe": False, "k": True, "levelParams": [], "name": _Tr,
              "numIndices": 0, "numMinors": 0, "numMotives": 0, "numParams": 0,
              "rules": [{"ctor": _Tc, "nfields": 0, "rhs": _intro}], "type": _recTy}],
    "types": [{"all": [_T], "ctors": [_Tc], "isRec": False, "isReflexive": False,
               "isUnsafe": False, "levelParams": [], "name": _T, "numIndices": 0,
               "numNested": 0, "numParams": 0, "type": _prop}]}}
dump("corner_rec_empty_prefix.ndjson", t.recs + t.ins + [_blk])
