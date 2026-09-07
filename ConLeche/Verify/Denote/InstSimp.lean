import ConLeche.Kernel.ExprOps

/-!
# `inst_simp`: computing `Expr.instantiate1` at a concrete telescope

One tactic, built because the same fight recurs in every remaining
clause of `CheckStepTT`: unfolding `Expr.instantiate1` on a *concrete*
pinned type (a basis constant's stored telescope) to see what the
opened body is.

## The fight, and why it is uniform

`Expr.instantiate1` (`ConLeche/Kernel/ExprOps.lean`) has exactly **one**
clause that branches:

```
| .bvar i => if i = d then v else if i > d then .bvar (i - 1) else .bvar i
```

Everything else is structural.  So the difficulty is uniform across
clauses — it is always these two `ite`s and nothing else — which is
what makes one tactic the right answer rather than per-clause
fiddling.

Three things have to happen, and missing any one leaves the term
stuck:

1. **unfold** `Expr.instantiate1`;
2. **normalise the depth arithmetic** — the depth arrives as
   `0 + 1 + 1`, not `2`, because each binder adds `+ 1` syntactically,
   and `reduceIte` cannot decide `1 = 0 + 1 + 1`;
3. **decide the comparisons** — `Nat.reduceLT` for `>` (after
   `gt_iff_lt`), `Nat.reduceEqDiff` for `=`, then `reduceIte`.

`simp only [Expr.instantiate1]` does (1) alone and leaves the `ite`s;
bare `simp` does all three but also normalises everything else in
sight, which is how it over-reduces a goal that still has work to do.
`inst_simp` is exactly the three, and nothing more.

## Customers

Every clause that opens a stored telescope: the `.proj` clause's
`PSigma'.mk` premises, the iota clause's recursor and constructor
telescopes, and the basis reductions.  Built when the second of those
needed it, not speculatively.
-/

namespace ConLeche.Verify

/-- Compute `Expr.instantiate1` through a concrete telescope: unfold,
normalise the depth arithmetic, decide the comparisons.  See the module
docstring for why bare `simp` and `simp only [Expr.instantiate1]` both
fail, in opposite directions. -/
syntax (name := instSimp) "inst_simp" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| inst_simp $[$loc]?) =>
    `(tactic| simp only [Expr.instantiate1, Nat.reduceAdd, Nat.reduceSub,
        gt_iff_lt, Nat.reduceLT, Nat.reduceEqDiff, reduceIte] $[$loc]?)

end ConLeche.Verify
