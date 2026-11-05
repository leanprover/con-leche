#!/usr/bin/env python3
"""Forge the fixtures of a pinned block at the stream's own constants (task #480).

A pinned block is installed at the record's level-parameter names, and its
comparison with the pin (up to those names) is the block's check, a job of
the checking phase.  No exporter writes these streams, so each is derived from
a committed twin.

  basis_eq_other_names            <- corner_pin_eq_free
      `Eq.{w}`, `Eq.refl.{w}`, `Eq.rec.{u, w}`: the pin up to its names, the
      recursor's as official generates them.
  basis_eq_rec_motive_name        <- corner_pin_eq_free
      `Eq.rec.{m, w}`: the same with the motive's parameter at another name.
  basis_eq_rec_swapped_names_bad  <- corner_pin_eq_free
      `Eq.rec.{w, m}`, the pin's positions at swapped names: the motive at the
      former's name, `Eq` at another, so a rule reading `Eq.refl`'s parameter
      by name (`pinLinkOk`) reads the motive's level.
  basis_eq_refl_other_name_bad    <- corner_pin_eq_free
      `Eq.refl.{v}` under `Eq.{w}`: a constructor at another block's names.
  basis_nat_rule_bad              <- corner_pin_quot_free
      `Nat.rec`'s rule for `Nat.zero` returns the other minor premise: not the
      pin; nothing follows the block.
  basis_nat_rule_used_bad         <- corner_pin_quot_free
      the same, with every later declaration of the stream reading `Nat`: the
      names are installed and used before the block's job has reported.
  basis_quot_other_names          <- corner_pin_quot_free
      `Quot.{w}`: official's kernel makes the quotient package itself, at
      fixed names; a record at others is not the pin.

Usage: scripts/mk_basis_names_fixtures.py   (reads and writes under tests/e2e/)
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


class Stream:
    def __init__(self, recs):
        self.recs = recs
        self.E = {r["ie"]: r for r in recs if "ie" in r}
        self.L = {r["il"]: r for r in recs if "il" in r}
        self.N = {}
        for r in recs:
            if "in" in r and "str" in r:
                self.N[r["in"]] = (r["str"]["pre"], r["str"]["str"])
            elif "in" in r and "num" in r:
                self.N[r["in"]] = (r["num"]["pre"], str(r["num"]["i"]))
        self.nn = max(self.N) + 1
        self.nl = max(self.L) + 1
        self.ne = max(self.E) + 1
        self.new = []

    def full(self, i):
        if i == 0:
            return ""
        pre, s = self.N[i]
        p = self.full(pre)
        return s if p == "" else p + "." + s

    def name_id(self, s):
        for i in self.N:
            if self.full(i) == s:
                return i
        i = self.nn
        self.nn += 1
        self.N[i] = (0, s)
        self.new.append({"in": i, "str": {"pre": 0, "str": s}})
        return i

    def level_map(self, sub):
        """A level rewriter: parameter name id -> parameter name id."""
        memo = {}

        def go(il):
            if il == 0:
                return 0
            if il in memo:
                return memo[il]
            r = self.L[il]
            nr = dict(r)
            changed = False
            for k in ("succ", "param", "max", "imax"):
                if k not in r:
                    continue
                if k == "param":
                    if r[k] in sub:
                        nr[k] = sub[r[k]]
                        changed = True
                elif k == "succ":
                    c = go(r[k])
                    if c != r[k]:
                        nr[k] = c
                        changed = True
                else:
                    a = [go(x) for x in r[k]]
                    if a != r[k]:
                        nr[k] = a
                        changed = True
            if not changed:
                memo[il] = il
                return il
            i = self.nl
            self.nl += 1
            nr["il"] = i
            self.L[i] = nr
            self.new.append(nr)
            memo[il] = i
            return i

        return go

    def expr_map(self, lv):
        memo = {}

        def go(ie):
            if ie in memo:
                return memo[ie]
            r = self.E[ie]
            nr = None
            if "sort" in r:
                u = lv(r["sort"])
                if u != r["sort"]:
                    nr = {"sort": u}
            elif "const" in r:
                us = [lv(u) for u in r["const"]["us"]]
                if us != r["const"]["us"]:
                    nr = {"const": {"name": r["const"]["name"], "us": us}}
            else:
                k = next((k for k in CHILD_KEYS if k in r), None)
                if k is not None:
                    node = dict(r[k])
                    changed = False
                    for ck in CHILD_KEYS[k]:
                        if ck in node:
                            c = go(node[ck])
                            if c != node[ck]:
                                node[ck] = c
                                changed = True
                    if changed:
                        nr = {k: node}
            if nr is None:
                memo[ie] = ie
                return ie
            i = self.ne
            self.ne += 1
            nr["ie"] = i
            self.E[i] = nr
            self.new.append(nr)
            memo[ie] = i
            return i

        return go

    def block_of(self, member):
        m = self.name_id(member)
        return next(i for i, r in enumerate(self.recs)
                    if "inductive" in r and any(t["name"] == m for t in r["inductive"]["types"]))

    def finish(self, bi):
        """The stream with the new nodes before record `bi`."""
        return self.recs[:bi] + self.new + self.recs[bi:]


def rename_eq(out, type_ps, refl_ps, rec_ps):
    """`Eq`'s block with its parameters renamed, record by record."""
    s = Stream(load("corner_pin_eq_free.ndjson"))
    bi = s.block_of("Eq")
    blk = s.recs[bi]["inductive"]
    u = s.name_id("u_1")
    m = blk["recs"][0]["levelParams"][0]
    assert blk["recs"][0]["levelParams"] == [m, u]

    def ids(xs):
        return [s.name_id(x) for x in xs]

    def renamer(ps, olds):
        return s.expr_map(s.level_map(dict(zip(olds, ids(ps)))))

    ty = renamer(type_ps, [u])
    t0 = blk["types"][0]
    t0["type"] = ty(t0["type"])
    t0["levelParams"] = ids(type_ps)
    c0 = blk["ctors"][0]
    tc = renamer(refl_ps, [u])
    c0["type"] = tc(c0["type"])
    c0["levelParams"] = ids(refl_ps)
    r0 = blk["recs"][0]
    tr = renamer(rec_ps, [m, u])
    r0["type"] = tr(r0["type"])
    r0["levelParams"] = ids(rec_ps)
    for ru in r0["rules"]:
        ru["rhs"] = tr(ru["rhs"])
    dump(out, s.finish(bi))


def nat_rule(out, keep_rest):
    """`Nat.rec`'s rule for `Nat.zero` at the wrong right-hand side."""
    s = Stream(load("corner_pin_quot_free.ndjson"))
    bi = s.block_of("Nat")
    blk = s.recs[bi]["inductive"]
    rec = blk["recs"][0]
    zero = s.name_id("Nat.zero")
    ru = next(r for r in rec["rules"] if r["ctor"] == zero)
    # `fun motive zero succ => zero` becomes `… => succ`: same binders, the
    # other minor premise
    r = s.E[ru["rhs"]]
    path = []
    while "lam" in r:
        path.append(r)
        r = s.E[r["lam"]["body"]]
    assert r.get("bvar") == 1, r
    b = s.ne
    s.ne += 1
    s.new.append({"bvar": 0, "ie": b})
    s.E[b] = s.new[-1]
    for node in reversed(path):
        i = s.ne
        s.ne += 1
        lam = dict(node["lam"])
        lam["body"] = b
        s.new.append({"ie": i, "lam": lam})
        s.E[i] = s.new[-1]
        b = i
    ru["rhs"] = b
    recs = s.finish(bi)
    if not keep_rest:
        k = next(i for i, x in enumerate(recs)
                 if "inductive" in x and any(t["name"] == s.name_id("Nat") for t in x["inductive"]["types"]))
        recs = recs[:k + 1]
    dump(out, recs)


def quot_names(out):
    s = Stream(load("corner_pin_quot_free.ndjson"))
    i = next(i for i, r in enumerate(s.recs) if "quot" in r and r["quot"].get("kind") == "type")
    q = s.recs[i]["quot"]
    u = q["levelParams"][0]
    w = s.name_id("w")
    q["type"] = s.expr_map(s.level_map({u: w}))(q["type"])
    q["levelParams"] = [w]
    dump(out, s.finish(i))


rename_eq("basis_eq_other_names.ndjson", ["w"], ["w"], ["u", "w"])
rename_eq("basis_eq_rec_motive_name.ndjson", ["w"], ["w"], ["m", "w"])
rename_eq("basis_eq_rec_swapped_names_bad.ndjson", ["w"], ["w"], ["w", "m"])
rename_eq("basis_eq_refl_other_name_bad.ndjson", ["w"], ["v"], ["u", "w"])
nat_rule("basis_nat_rule_bad.ndjson", False)
nat_rule("basis_nat_rule_used_bad.ndjson", True)
quot_names("basis_quot_other_names.ndjson")
