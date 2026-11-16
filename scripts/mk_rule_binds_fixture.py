#!/usr/bin/env python3
"""The ι step's peel needs the stated λs (task #585): a stored rule's
right-hand side must be a function of the recursor's rule prefix and the
constructor's fields, syntactically (`ruleBinds`).  One edit of
`direct_fix_nat` (`Nat'`), forged with `scripts/mk_rec_corner.py`'s `Twin`.

  stored_rule_lams_short   `Nat'.rec`'s rule for `Nat'.zero`,
      `fun motive zero succ => zero`, written with two manifest λs,
      `fun motive zero => (fun (x : motive Nat'.zero) succ => x) zero`:
      definitionally the generated rule (accepted before task #585),
      rejected by the λ count since.  (Official, which compares
      syntactically: 1.)

Usage: scripts/mk_rule_binds_fixture.py   (reads and writes under tests/e2e/)
"""
import os

HERE = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(HERE, "mk_rec_corner.py")).read()
exec(_src[:_src.index("\n# --- corner_rec_extra_binder")])

t = Twin("direct_fix_nat")
rc = t.rec("Nat'", "Nat'.rec")
pre = rc["numParams"] + rc["numMotives"] + rc["numMinors"]
assert pre == 3, "Nat'.rec: motive, zero, succ"
zr = t.rule("Nat'", "Nat'.rec", "Nat'.zero")
bs = t.binders(zr["rhs"], pre)
lz, ls = bs[1]["lam"], bs[2]["lam"]
assert t.E[ls["body"]] .get("bvar") == 1, "the zero rule's body is `zero`"
# under `motive zero`: `(fun (x : motive Nat'.zero) succ => x) zero`
inner = t.ex({"lam": dict(lz, name=t.name("x"), type=t.lift(lz["type"], 1),
    body=t.ex({"lam": dict(ls, type=t.lift(ls["type"], 1), body=t.ex({"bvar": 1}))}))})
redex = t.ex({"app": {"fn": inner, "arg": t.ex({"bvar": 0})}})
zr["rhs"] = rebuild_prefix(t, zr["rhs"], 2, lambda rest: redex)
t.write("stored_rule_lams_short", "Nat'")
