#!/usr/bin/env python3
"""Stored-recursor fixtures (task #431): the installer installs the
STORED recursor — its type and its rules' right-hand sides — once they
agree with the generated ones up to definitional equality (binder by
binder for the type).  Each twin is one edit of `direct_fix_nat`
(`Nat'`), forged with `scripts/mk_rec_corner.py`'s `Twin`.

  stored_rule_dom_redex   `Nat'.rec`'s rule for `Nat'.succ`: the domain of
      its field binder `(n : Nat')` written as the β-redex
      `(fun T : Type => T) Nat'`.  Definitionally the generated rule:
      accepted, and the STORED rule is what is installed.  (Official, which
      compares syntactically: 1.)
  stored_type_dom_redex   `Nat'.rec`'s TYPE: in the `succ` minor premise,
      the field's domain written as the same β-redex.  Definitionally the
      generated type, binder by binder: accepted, the stored type
      installed.  (Official: 1.)
  stored_type_dom_bad   the same field's domain written as `Nat' → Nat'`:
      a type, not the generated one's: 1 (official 1).

Usage: scripts/mk_stored_rec_fixtures.py   (reads and writes under tests/e2e/)
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, "mk_rec_corner.py")).read()
exec(_src[:_src.index("\n# --- corner_rec_extra_binder")])


def redex(t, ty_ie):
    """`(fun T : Type => T) ty`, at the type of the stream's `Nat'`."""
    _, blk = t.block("Nat'")
    sort_ie = blk["types"][0]["type"]          # `Nat' : Type`
    junk = t.name("T")
    idf = t.ex({"lam": {"binderInfo": "default", "name": junk, "type": sort_ie,
                        "body": t.ex({"bvar": 0})}})
    return t.ex({"app": {"fn": idf, "arg": ty_ie}})


# --- stored_rule_dom_redex -------------------------------------------
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
pre = rc["numParams"] + rc["numMotives"] + rc["numMinors"]
sr = t.rule("Nat'", "Nat'.rec", "Nat'.succ")
field = t.binders(sr["rhs"], pre + 1)[pre]["lam"]
nat_ie = field["type"]
assert t.E[nat_ie].get("const", {}).get("name") == t.names["Nat'"], "not the field `n : Nat'`"
sr["rhs"] = rebuild_prefix(t, sr["rhs"], pre,
    lambda rest: t.ex({"lam": dict(t.E[rest]["lam"], type=redex(t, nat_ie))}))
t.write("stored_rule_dom_redex", "Nat'")

# --- stored_type_dom_redex -------------------------------------------
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
nP, nMot = rc["numParams"], rc["numMotives"]
succ_minor_b = t.binders(rc["type"], nP + nMot + 2)[nP + nMot + 1]["forallE"]   # `succ` premise
fld = t.E[succ_minor_b["type"]]["forallE"]                                      # `(n : Nat') -> ...`
assert t.E[fld["type"]].get("const", {}).get("name") == t.names["Nat'"], "not the field `n : Nat'`"
new_minor = t.ex({"forallE": dict(fld, type=redex(t, fld["type"]))})
rc["type"] = rebuild_prefix(t, rc["type"], nP + nMot + 1,
    lambda rest: t.ex({"forallE": dict(t.E[rest]["forallE"], type=new_minor)}))
t.write("stored_type_dom_redex", "Nat'")

# --- stored_type_dom_bad ---------------------------------------------
# the same field's domain written as `Nat' → Nat'`: a type, but not the
# generated one's — rejected (exit 1), as official rejects it.
t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
nP, nMot = rc["numParams"], rc["numMotives"]
succ_minor_b = t.binders(rc["type"], nP + nMot + 2)[nP + nMot + 1]["forallE"]
fld = t.E[succ_minor_b["type"]]["forallE"]
arrow = t.ex({"forallE": {"binderInfo": "default", "name": t.name("x"), "type": fld["type"],
                          "body": fld["type"]}})
new_minor = t.ex({"forallE": dict(fld, type=arrow)})
rc["type"] = rebuild_prefix(t, rc["type"], nP + nMot + 1,
    lambda rest: t.ex({"forallE": dict(t.E[rest]["forallE"], type=new_minor)}))
t.write("stored_type_dom_bad", "Nat'", drop_defs=True)
