#!/usr/bin/env python3
"""Forge the two unit-eta reject twins of lane UNITCAPS (found by lane
WHNFSWAP).  Each is its `_free` twin with ONE expression reference
re-pointed from `P U a` to `P U b` (`a`, `b : U`, `U` a fieldless
one-constructor member of a block official calls recursive):

  corner_unitcaps_mutual_bad  <- corner_unitcaps_mutual_free
      `T.mk`'s field `Const Nat (∀ a b (x : P U a), R (P U a) (@id (P U a) x))`
      becomes `... (@id (P U b) x)`: typing the constructor needs
      `a =?= b : U`.  The block is recursive in official's RAW sense
      (the domain mentions `U`, though it reduces to `Nat`), so
      official's `is_def_eq_unit_like` does not fire: 1 ("application
      type mismatch").
  corner_unitcaps_post_bad    <- corner_unitcaps_post_free
      `theorem f (a b : U) (x : P U a) : P U a := x` becomes
      `... : P U b := x`, after the block `U | mk`, `T | mk : U → T`.
      Official 1 ("declaration type mismatch").

Lean cannot elaborate either, hence the forge.

Usage: scripts/mk_unitcaps_bad.py   (reads and writes under tests/e2e/)
"""
import json
import os

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
D = os.path.join(ROOT, "tests/e2e")


def forge(src, out, ie, field, old, new, head):
    lines = open(os.path.join(D, src)).read().splitlines()
    recs = [json.loads(l) for l in lines]
    E = {r["ie"]: r for r in recs if "ie" in r}
    assert p_u(E, old, head) and p_u(E, new, head), src
    k = next(k for k, r in enumerate(recs) if r.get("ie") == ie)
    kind = next(key for key in recs[k] if key != "ie")
    assert recs[k][kind][field] == old, (src, recs[k])
    recs[k][kind][field] = new
    lines[k] = json.dumps(recs[k], separators=(",", ":"), ensure_ascii=False)
    open(os.path.join(D, out), "w").write("\n".join(lines) + "\n")


def p_u(E, i, fn):
    # `P U #j`: an application of the shared head `P U`
    return "app" in E[i] and E[i]["app"]["fn"] == fn


# mutual: 162 = `@id.{1} (P U a)`; 159 = `P U a`, 158 = `P U b` (both `157 · bvar`)
forge("corner_unitcaps_mutual_free.ndjson", "corner_unitcaps_mutual_bad.ndjson",
      162, "arg", 159, 158,
      157)
# post: 158 = `∀ x : P U a, P U a`; its body 157 becomes 156 (`P U b`)
forge("corner_unitcaps_post_free.ndjson", "corner_unitcaps_post_bad.ndjson",
      158, "body", 157, 156,
      155)
