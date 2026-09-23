module

public import ConLeche.SetModel.Ops
public import ConLeche.SetModel.Value
public import ConLeche.SetModel.TupleTower
public import ConLeche.SetModel.UnionRec
public import ConLeche.SetModel.TupleContainer
public import ConLeche.SetModel.WfRec
public import ConLeche.SetModel.NarrowTreeList
public import ConLeche.SetModel.HoleOp

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
* `UnionRec` — the simultaneous recursor of a block over the disjoint
  union of its values, on `RecGraph`'s recursion theorem and
  `SetTheory/Derive/LfpTuple`'s tuple lfp; `TupleContainer` — the
  closed tuple of a block presented as a member container ((W) at
  tuples, the `Prop` regime, the nested slot);
* `WfRec`, `NarrowTreeList` — the NARROW falsifier: a nested block's
  meaning as the one-component least fixed point reading the container
  ordinarily at the hole, with the recursion run by ∈-recursion on the
  global subterm relation (`SetTheory/Derive/TransClosure.lean`) over
  the two majors' ordinary carriers — no wide tuple, no identification,
  no per-block accessibility;
* `HoleOp` — the HOLE operator (design lane HOLEOP): a block's
  operator as `Σ ctor, Π fields, ⟦field⟧[members := X]` over a syntax
  of POSITIVE TYPES with no field kinds, monotonicity by induction on
  the positivity derivation, the fibre law, and parameter-monotonicity
  of any block by leastness (the nested case's only need).

The WIDE-tuple falsifiers that stood here — `EnvClauseTreeList`,
`EnvClauseP3`, `EnvClauseP4`, `EnvClauseIndexed` and
`UnionRecIndexed`, which modelled a nested block as its members plus a
COPY of each container and identified the copy's component with the
container's recorded reading — are retired (DESIGN 2026-09-21): the
narrow clause replaces the wide tuple, so `NarrowTreeList` is the
falsifier the route is read against, and it carries its own clause,
minors and standard model.

`Ops` and `Value` carry the namespace `ConLeche.SetModel`.  The tier
imports only `ConLeche/SetTheory/*` and `ConLeche/Term/*`; the Expr-facing
denotation and claims stand above it in `ConLeche/Semantics/*`.
-/
