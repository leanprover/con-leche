#!/usr/bin/env python3
"""BAD fixtures for the recursor check's kernel additions K4, K6 and K7
(`ConLeche/Kernel/Inductives/RecCheck.lean`; `REVIEW-CHECKS` §1, question
Q-H: "forge bad fixtures for K1, K3, K4, K6 and K7").  Each stream is
the smallest edit of a committed good stream that lands in the check's
corner case.  Only K7 can be the check that FIRES: the others are
implied by an earlier check, and the fixture pins which one (DESIGN.md,
lane SMALLFIX).  All three: official 1, TARGET 1.

  corner_rec_k7_let_major_bad  <- direct_sum_enum (cut after `Color`)
      `Color` gets a second recursor `Color.rec_1` — `Color.rec`'s type
      with the major's domain written `let x : Type := Color; x`.  The
      recogniser reads the DECLARED major head (a `let`, no member), so
      the record is an auxiliary one (tgt = k) and its name is the
      generated auxiliary name; the checked type is the ANNOTATED one,
      which unfolds the `let` to the member `Color`.  K7
      ("the recursor record's member is not its major's") fires.
      Official: a non-nested block gets exactly one recursor per member
      (`mk_rec_infos`/`declare_recursors`, inductive.cpp:1191 names the
      auxiliaries only for nested auxiliary types), so no `Color.rec_1`
      exists to match the record.
  corner_rec_k6_param_dom_bad  <- ind_mutual_param_defeq
      `MB2.rec`'s parameter binder `(α : id Type)` becomes `(α : Prop)`.
      K6 compares it with the MAJOR's former (`MB2`'s), but the major
      `(t : MB2 α)` already forces it: the recursor's type does not
      type-check (application of `MB2` to a `Prop`), and that rejects
      first.  K6 is implied whenever the major applies the member to
      the recursor's parameter variables — which the major check
      (`targetMajorOf`) demands syntactically.  Official: the recursor
      is generated (`mk_rec_infos`, one `m_params`), the record differs.
  corner_rec_k4_foreign_level_bad <- direct_sum_enum (cut after `Color`)
      `Color.green` gets a field `(x : Sort v)` with `v` declared by no
      one.  K4 asks that the fields' normal forms name only the
      recursor's level parameters; a field inherits its levels from the
      constructor, which is checked at the block's parameters (⊆ the
      recursor's) BEFORE the recursor stage, and δ/ι never introduce a
      parameter, so K4 cannot be the first check to fire: the
      constructor's type check rejects ("undeclared universe").
      Official: `check_constructors` type-checks the constructor with
      the block's level parameters (inductive.cpp:469) — rejects.

K1 and K3 get no stream here.  K1 (the call λ is inferred at the frame)
is implied by R9 + the `want` inference + the `fty ≡ want` defeq that
precede it; K3 compares the call's inferred type with `targetIhTy`, which
the check builds from the same pieces — neither side is read off the
stream.  Their nearest bad streams are the R22/K5 fixtures
(`corner_rec_call_const_bad`, `corner_rec_call_redex`).

Usage: scripts/mk_rec_kbad.py   (reads and writes under tests/e2e/)
"""
import copy
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def dump(name, recs):
    p = os.path.join(ROOT, "tests/e2e", name)
    with open(p, "w") as f:
        for r in recs:
            f.write(json.dumps(r, separators=(",", ":"), ensure_ascii=False) + "\n")
    print("%s: %d lines" % (name, len(recs)))


class Stream:
    def __init__(self, src):
        p = os.path.join(ROOT, "tests/e2e", src + ".ndjson")
        self.recs = [json.loads(l) for l in open(p).read().splitlines()]
        self.E = {r["ie"]: r for r in self.recs if "ie" in r}
        self.nxt_ie = max(self.E) + 1
        self.nxt_in = max([r["in"] for r in self.recs if "in" in r] + [0]) + 1
        self.nxt_il = max([r["il"] for r in self.recs if "il" in r] + [0]) + 1
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
            q = full(pre)
            return s if q == "" else q + "." + s

        self.names = {full(i): i for i in raw}
        self.ins = []

    def ex(self, node):
        i = self.nxt_ie
        self.nxt_ie += 1
        r = dict(node, ie=i)
        self.ins.append(r)
        self.E[i] = r
        return i

    def name(self, s, pre=0):
        i = self.nxt_in
        self.nxt_in += 1
        self.ins.append({"in": i, "str": {"pre": pre, "str": s}})
        return i

    def lvl(self, **k):
        i = self.nxt_il
        self.nxt_il += 1
        self.ins.append(dict({"il": i}, **k))
        return i

    def block_index(self, member):
        n = self.names[member]
        return next(i for i, r in enumerate(self.recs) if "inductive" in r
                    and any(t["name"] == n for t in r["inductive"]["types"]))

    def emit(self, upto):
        """The stream through record `upto`, the new records in front of it."""
        return self.recs[:upto] + self.ins + [self.recs[upto]]


def pi_parts(s, ie, n):
    """The first `n` forallE nodes of the telescope at `ie`, and the rest."""
    nodes = []
    for _ in range(n):
        r = s.E[ie]
        nodes.append(r["forallE"])
        ie = r["forallE"]["body"]
    return nodes, ie


def rebuild(s, nodes, body):
    for nd in reversed(nodes):
        body = s.ex({"forallE": dict(nd, body=body)})
    return body


def k7():
    s = Stream("direct_sum_enum")
    bi = s.block_index("Color")
    blk = s.recs[bi]["inductive"]
    rc = blk["recs"][0]
    mI = rc["numParams"] + rc["numMotives"] + rc["numMinors"] + rc["numIndices"]
    outer, major = pi_parts(s, rc["type"], mI)
    maj = s.E[major]["forallE"]
    color = maj["type"]                                   # const Color
    typ = next(r["ie"] for r in s.recs if "sort" in r and "ie" in r
               and any(x.get("il") == r["sort"] and x.get("succ") == 0 for x in s.recs))
    b0 = s.ex({"bvar": 0})
    let = s.ex({"letE": {"name": s.name("x"), "type": typ, "value": color, "body": b0,
                         "nondep": False}})
    newmaj = s.ex({"forallE": dict(maj, type=let)})
    ty = rebuild(s, outer, newmaj)
    aux = copy.deepcopy(rc)
    aux["name"] = s.name("rec_1", s.names["Color"])
    aux["type"] = ty
    blk["recs"].append(aux)
    dump("corner_rec_k7_let_major_bad.ndjson", s.emit(bi))


def k6():
    s = Stream("ind_mutual_param_defeq")
    bi = s.block_index("MB2")
    blk = s.recs[bi]["inductive"]
    rc = next(r for r in blk["recs"] if r["name"] == s.names["MB2.rec"])
    assert rc["numParams"] == 1
    outer, rest = pi_parts(s, rc["type"], 1)
    prop = next(r["ie"] for r in s.recs if r.get("sort") == 0 and "ie" in r)
    rc["type"] = rebuild(s, [dict(outer[0], type=prop)], rest)
    # the rules' λ prefix binds the parameter at the same domain
    for rule in rc["rules"]:
        lam = s.E[rule["rhs"]]["lam"]
        rule["rhs"] = s.ex({"lam": dict(lam, type=prop)})
    dump("corner_rec_k6_param_dom_bad.ndjson", s.emit(bi))


def k4():
    s = Stream("direct_sum_enum")
    bi = s.block_index("Color")
    blk = s.recs[bi]["inductive"]
    green = blk["ctors"][1]
    lv = s.lvl(param=s.name("v"))
    sv = s.ex({"sort": lv})
    ty = s.ex({"forallE": {"binderInfo": "default", "name": s.name("x"), "type": sv,
                           "body": green["type"]}})
    green["type"] = ty
    green["numFields"] = 1
    rc = blk["recs"][0]
    for rule in rc["rules"]:
        if rule["ctor"] == green["name"]:
            rule["nfields"] = 1
    dump("corner_rec_k4_foreign_level_bad.ndjson", s.emit(bi))


if __name__ == "__main__":
    k7()
    k6()
    k4()
