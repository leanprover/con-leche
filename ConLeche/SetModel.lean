module

public import ConLeche.SetModel.Ops
public import ConLeche.SetModel.Value
public import ConLeche.SetModel.TupleTower
public import ConLeche.SetModel.UnionRec
public import ConLeche.SetModel.TupleContainer
public import ConLeche.SetModel.EnvClauseTreeList
public import ConLeche.SetModel.WfRec
public import ConLeche.SetModel.NarrowTreeList
public import ConLeche.SetModel.EnvClauseP3
public import ConLeche.SetModel.EnvClauseP4
public import ConLeche.SetModel.UnionRecIndexed
public import ConLeche.SetModel.EnvClauseIndexed

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
* `EnvClauseTreeList`, `EnvClauseP3`, `EnvClauseP4` — the falsifiers
  for the uniform nested route: `Tree ::= node (List Tree)` as a plain
  two-component block whose copy component is identified with the
  container's recorded reading through the container's env clause
  alone; `P3 ::= mk (Array (List P3))` at four components, where the
  container's own clause is WIDE and the identifications run in RANK
  order; `P4 ::= mk (Rose P4)` at three, where the group's whole
  segment is the nested container's wide table seeded at the pin.
  `UnionRecIndexed` — the falsifier for the recursion kit itself at an
  INDEXED, PARAMETRIC block with a REFLEXIVE field (`Acc`-shaped in
  `Type`, at one member and at two mutual ones), together with the
  `ℓ = 0` arm (`InductionKit`), where the motive fibre's inhabitation
  comes from the tuple lfp's induction alone; `EnvClauseIndexed` —
  `TV ::= node (n : ω) (v : Vec TV n)`, where the group's container is
  INDEXED, so the identification runs at a non-trivial index set and
  the fibre law selects its arms by the index.

`Ops` and `Value` carry the namespace `ConLeche.SetModel`.  The tier
imports only `ConLeche/SetTheory/*` and `ConLeche/Term/*`; the Expr-facing
denotation and claims stand above it in `ConLeche/Semantics/*`.
-/
