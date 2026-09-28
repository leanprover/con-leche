module

public import ConLeche.SetModel.Ops
public import ConLeche.SetModel.Value
public import ConLeche.SetModel.TupleTower
public import ConLeche.SetModel.UnionRec
public import ConLeche.SetModel.GraphRec
public import ConLeche.SetTheory.Derive.LfpTuple
public import ConLeche.SetModel.TaggedSum
public import ConLeche.SetModel.HoleClose
public import ConLeche.SetModel.NestRec
public import ConLeche.SetModel.NestRecCls
public import ConLeche.SetModel.Access
public import ConLeche.SetModel.ClassFacts
public import ConLeche.SetModel.ClassKit

@[expose] public section

/-!
# `ConLeche.SetModel` — the pure set constructions

Set constructions over an abstract `SetTheory V` that mention neither
`Expr` nor the annotated syntax `AnnotTerm`.

* `Ops` — `piR`/`lamR`/`app`, the two-regime dependent product and
  abstraction (the `R` is *regime*);
* `Value` — the built-in constants' value towers (`natRecV`,
  `quotLiftV`, `psigmaV`, …) over `piR`/`lamR`;
* `TupleTower` — the uniform tuple model for directly-installed
  structures: `sigmaSet`-built, unit-terminated pair towers, the
  tupler `mkTower` and the projection family (namespace
  `ConLeche.SetTheory.Tower`);
* `UnionRec` — the disjoint union of a block's values (`unionSet`,
  `tagged`), the index set of the recursor's graph;
* `GraphRec` — the recursor family's GRAPH as a least fixed point,
  functional by the majors' induction alone (`GraphRecKit.exu`): one
  mechanism at every sort;
* `HoleClose` — closing the holes: the least tuple below
  a bound on a group of its components (the container case of
  "positivity ⇒ monotone"), operators compared through their fibre laws;
* `NestRec` — the nested recursor's graph kit: majors over several classes (the members and the
  container instantiations, each the lfp of its own operator at its own
  frame), `ind` by the strengthened predicate ("in the TRUE class ∧ the
  property") with no container parameter-monotonicity and no Bekić,
  `exu` under `huniq` in both regimes;
* `NestRecCls` — the kit's induction, decoded (`NestNodeInd`,
  `NestKit.toNodeInd`), transported to the
  RECURSOR's classes: a class visited at one or several
  nodes, and the graph kit's `ind` over the recursors' tagged majors
  follows (`NestNodeInd.ind_recNodesOn`);
* `Access` — the closure witness (W) from ACCESSIBILITY:
  `closed_of_acc` (a uniformly
  bounded, accessible operator mapping the tuple space into itself has a
  closed tuple — ordinal-free, along Brouwer trees coded by their
  paths), `AccTuple.monoTuple`, the closure lemmas over readings, and
  `lfpP_acc` (the least tuple of an accessible joint operator is
  accessible in its parameter — the nested case, no key, no wide
  operator); (W) at EVERY block, flat or nested, and
  `closedTuple_zero` for the `Prop` regime.

A nested block's clause is the narrow one: the container is read
ordinarily at the hole, never as a copy in a wider tuple.

`Ops` and `Value` carry the namespace `ConLeche.SetModel`.  The tier
imports only `ConLeche/SetTheory/*` and `ConLeche/Term/*`; the Expr-facing
denotation and claims stand above it in `ConLeche/Semantics/*`.
-/
