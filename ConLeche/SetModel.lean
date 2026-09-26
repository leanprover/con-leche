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

@[expose] public section

/-!
# `ConLeche.SetModel` — the pure set constructions

The Expr-free half of the former `ConLeche/SetBase/*` (split 2026-09-06,
cleanup pass A): set constructions over an abstract `SetTheory V` that
mention neither `Expr` nor the annotated syntax `AnnotTerm`.

* `Ops` — `piR`/`lamR`/`app`, the two-regime dependent product and
  abstraction (the `R` is *regime*, not the retired R lane);
* `Value` — the built-in constants' value towers (`natRecV`,
  `quotLiftV`, `psigmaV`, …) over `piR`/`lamR`;
* `TupleTower` — the uniform tuple model for directly-installed
  structures: `sigmaSet`-built, unit-terminated pair towers, the
  tupler `mkTower` and the projection family (namespace
  `ConLeche.SetTheory.Tower`, unchanged);
* `UnionRec` — the disjoint union of a block's values (`unionSet`,
  `tagged`), the index set of the recursor's graph;
* `GraphRec` — the recursor family's GRAPH as a least fixed point,
  functional by the majors' induction alone (`GraphRecKit.exu`): one
  mechanism at every sort, the recursor model's (DESIGN, ruling of
  2026-09-23);
* `HoleOp` — the HOLE operator (design lane HOLEOP): a block's
  operator as `Σ ctor, Π fields, ⟦field⟧[members := X]` over a syntax
  of POSITIVE TYPES with no field kinds, monotonicity by induction on
  the positivity derivation, the fibre law, and parameter-monotonicity
  of any block by leastness (the nested case's only need);
* `HoleClose` — closing the holes (lane POSPROOF): the least tuple is
  monotone in its operator (`lfpTuple_le_of_opLe`, the container case of
  "positivity ⇒ monotone"), operators compared through their fibre laws,
  and D2 (an unreached member does not change the reached component);
* `NestRec` — the nested recursor's graph kit (lane
  NESTIND-KIT): majors over several classes (the members and the
  container instantiations, each the lfp of its own operator at its own
  frame), `ind` by the strengthened predicate ("in the TRUE class ∧ the
  property") with no container parameter-monotonicity and no Bekić,
  `exu` under `huniq` in both regimes;
* `NestRecCls` — the kit's induction, decoded (`NestNodeInd`,
  `NestKit.toNodeInd`), transported to the
  RECURSOR's classes (lane NESTIND): a class visited at one or several
  nodes, and the graph kit's `ind` over the recursors' tagged majors
  follows (`NestNodeInd.ind_recNodesOn`);
* `Access` — the closure witness (W) from ACCESSIBILITY (maintainer
  ruling 2026-09-24, lane ACCMODEL): `closed_of_acc` (a uniformly
  bounded, accessible operator mapping the tuple space into itself has a
  closed tuple — ordinal-free, along Brouwer trees coded by their
  paths), `AccTuple.monoTuple`, the closure lemmas over readings, and
  `lfpP_acc` (the least tuple of an accessible joint operator is
  accessible in its parameter — the nested case, no key, no wide
  operator); (W) at EVERY block, flat or nested (lane FLATACC), and
  `closedTuple_zero` for the `Prop` regime.

The WIDE-tuple falsifiers that stood here — `EnvClauseTreeList`,
`EnvClauseP3`, `EnvClauseP4`, `EnvClauseIndexed` and
`UnionRecIndexed`, which modelled a nested block as its members plus a
COPY of each container and identified the copy's component with the
container's recorded reading — are retired (DESIGN 2026-09-21): a
nested block's clause is the narrow one (the container read ordinarily
at the hole).

`Ops` and `Value` carry the namespace `ConLeche.SetModel`.  The tier
imports only `ConLeche/SetTheory/*` and `ConLeche/Term/*`; the Expr-facing
denotation and claims stand above it in `ConLeche/Semantics/*`.
-/
