#!/usr/bin/env python3
"""GENREC fixtures (the recursor family GENERATED, charter item 5 as amended
2026-09-29).  Each twin is one edit of a committed good stream, forged with
`scripts/mk_rec_corner.py`'s `Twin`.

  genrec_k2_caseson / genrec_k3_caseson   a k = 2 (k = 3) mutual block whose
      recursor family is casesOn-SHAPED: every minor premise loses its
      inductive hypotheses and every rule its recursive calls.  A legitimate
      primitive recursion, but not official's recursor: official 1 ("invalid
      recursor"); the generated stage compares the stream's TYPES with the
      generated ones and rejects: 1.  (Before GENREC the primitive-recursion
      check accepted it: 0.)  The bases' definitions are dropped (they apply
      the recursors at their old types).
  genrec_rules_garbage   `Nat'.rec`'s rules replaced by the constant
      `Nat'.zero` — ill-typed, not a recursion at all — its TYPE untouched,
      the base's definitions and theorems kept (they reduce through the
      recursor's rules).  Official 1 (replay compares the rules).  The
      generated stage never reads the stream's rules: it installs its own,
      so the stream is accepted and every theorem that reduces through
      `Nat'.rec` checks against the GENERATED rules: 0.
  genrec_rules_garbage_nested   the same at a NESTED block: every rule of
      `NT.rec` and `NT.rec_1` (`ind_rec_struct_proj_raw`, `NT` nested through
      `List`) replaced by `Nat.zero`, the definition `NT.lbl` and the theorem
      `NT.lbl_proj` (by reduction) kept: 0 (official 1).

Usage: scripts/mk_genrec_fixtures.py   (reads and writes under tests/e2e/)
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, "mk_rec_corner.py")).read()
exec(_src[:_src.index("\n# --- corner_rec_extra_binder")])


def spine(t, ie):
    args = []
    while "app" in t.E[ie]:
        args.append(t.E[ie]["app"]["arg"])
        ie = t.E[ie]["app"]["fn"]
    return ie, list(reversed(args))


def casesonify(base, member, out):
    t = Twin(base)
    _, blk = t.block(member)
    nf = {c["name"]: c["numFields"] for c in blk["ctors"]}
    ctors = [c["name"] for c in blk["ctors"]]
    for rc in blk["recs"]:
        nP, nMot, nMin = rc["numParams"], rc["numMotives"], rc["numMinors"]
        bs = t.binders(rc["type"], nP + nMot + nMin)
        mins = [b["forallE"]["type"] for b in bs[nP + nMot:]]
        assert len(mins) == len(ctors)
        repl = {}
        for mi, c in zip(mins, ctors):
            n = nf[c]
            # the minor's telescope: n fields, then the ihs, then the conclusion
            tot = 0
            e = mi
            while "forallE" in t.E[e]:
                tot += 1
                e = t.E[e]["forallE"]["body"]
            nih = tot - n
            if nih == 0:
                continue
            fb = t.binders(mi, n)
            new = t.lift(e, -nih)
            for r in reversed(fb):
                new = t.ex({"forallE": dict(r["forallE"], body=new)})
            repl[mi] = new
        f = lambda i, _d: repl.get(i)
        rc["type"] = t.map(rc["type"], f)
        for ru, c in zip(rc["rules"],
                         [c for c in ctors if any(r["ctor"] == c for r in rc["rules"])]):
            n = ru["nfields"]
            lb = t.binders(ru["rhs"], nP + nMot + nMin + n)
            body = lb[-1]["lam"]["body"]
            head, args = spine(t, body)
            if len(args) > n:
                nb = head
                for a in args[:n]:
                    nb = t.ex({"app": {"fn": nb, "arg": a}})
                ru["rhs"] = t.replace(ru["rhs"], body, nb)
            ru["rhs"] = t.map(ru["rhs"], f)
    t.write(out, member, drop_defs=True)


def garbage_rules(base, member, const_name, out):
    t = Twin(base)
    _, blk = t.block(member)
    junk = t.const(const_name)
    for rc in blk["recs"]:
        for ru in rc["rules"]:
            ru["rhs"] = junk
    t.write(out, member)


casesonify("ind_defhead_mutual", "MA", "genrec_k2_caseson")
casesonify("ind_mutual_three", "TA", "genrec_k3_caseson")
garbage_rules("direct_fix_nat", "Nat'", "Nat'.zero", "genrec_rules_garbage")
garbage_rules("ind_rec_struct_proj_raw", "NT", "Nat.zero", "genrec_rules_garbage_nested")
