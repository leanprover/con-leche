module

public import ConLeche.SetModel.Ops
public import ConLeche.SetModel.Value
public import ConLeche.SetModel.TupleTower
public import ConLeche.SetModel.UnionRec
public import ConLeche.SetModel.TupleContainer
public import ConLeche.SetModel.WfRec
public import ConLeche.SetModel.GraphRec
public import ConLeche.SetModel.HoleOp
public import ConLeche.SetModel.HoleClose
public import ConLeche.SetModel.NestRec
public import ConLeche.SetModel.NestRecEx
public import ConLeche.SetModel.WideFlat
public import ConLeche.SetModel.NestWide
public import ConLeche.SetModel.NestWideEx

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
* `WfRec` — recursion by ∈-recursion on the global subterm relation
  (`SetTheory/Derive/TransClosure.lean`) at arbitrary classes, off
  regularity — the recursion half of the retired narrow falsifier
  (its Tree/List instance was superseded by the NESTW-KIT witness below);
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
* `NestRec`, `NestRecEx` — the nested recursor's graph kit (lane
  NESTIND-KIT): majors over several classes (the members and the
  container instantiations, each the lfp of its own operator at its own
  frame), `ind` by the strengthened predicate ("in the TRUE class ∧ the
  property") with no container parameter-monotonicity and no Bekić,
  `exu` under `huniq` in both regimes; instances `Tree`/`List`,
  `Rose`/`List`, and the two-level `T`/`Rose T`/`List (Rose T)`;
* `WideFlat`, `NestWide`, `NestWideEx` — the closure witness (W) of a
  NESTED block (lane NESTW-KIT): the closed tuple of a FLAT hole-operator
  block (`UBlock.closed_of_flat`, R3's caveat as the named premise
  `HoleUnread`), and the transient wide operator (members + one
  component per container key) with all keys composed away at once
  (`closed_of_wide_groups`), asking of each container only its lfp
  clause at the instantiation; instances `Rose`/`List`, the two-level
  `T`/`Rose T`/`List (Rose T)`, a mutual container group reached by
  restart, and `Prop`.

The WIDE-tuple falsifiers that stood here — `EnvClauseTreeList`,
`EnvClauseP3`, `EnvClauseP4`, `EnvClauseIndexed` and
`UnionRecIndexed`, which modelled a nested block as its members plus a
COPY of each container and identified the copy's component with the
container's recorded reading — are retired (DESIGN 2026-09-21): a
nested block's clause is the narrow one (the container read ordinarily
at the hole), and a wide operator appears only transiently, inside the
closure witness (`NestWide`), where nothing is identified.

`Ops` and `Value` carry the namespace `ConLeche.SetModel`.  The tier
imports only `ConLeche/SetTheory/*` and `ConLeche/Term/*`; the Expr-facing
denotation and claims stand above it in `ConLeche/Semantics/*`.
-/
