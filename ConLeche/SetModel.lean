module

public import ConLeche.SetModel.Ops
public import ConLeche.SetModel.Value
public import ConLeche.SetModel.TupleTower
public import ConLeche.SetModel.UnionRec
public import ConLeche.SetModel.MutualPair
public import ConLeche.SetModel.NestedTreeList

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
  union of its values (task #315), on `RecGraph`'s recursion theorem
  and `SetTheory/Derive/LfpTuple`'s tuple lfp; the pure experiments
  `MutualPair` (a two-member mutual block) and `NestedTreeList`
  (`Tree ::= node (List Tree)` through a `Sat`-guarded container).

`Ops` and `Value` carry the namespace `ConLeche.SetModel`.  The tier
imports only `ConLeche/SetTheory/*` and `ConLeche/Term/*`; the Expr-facing
denotation and claims stand above it in `ConLeche/Semantics/*`.
-/
