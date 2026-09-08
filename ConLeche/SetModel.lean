import ConLeche.SetModel.Ops
import ConLeche.SetModel.Value
import ConLeche.SetModel.TupleTower

/-!
# `ConLeche.SetModel` — the pure set constructions

The Expr-free half of the former `ConLeche/SetBase/*` (split 2026-09-06,
cleanup pass A): set constructions over an abstract `SetTheory V` that
mention neither `Expr` nor the annotated syntax `AnnotTerm`.

* `Ops` — `piR`/`lamR`/`app`, the two-regime dependent product and
  abstraction (the `R` is *regime*, not the retired R lane);
* `Value` — the built-in constants' value towers (`natRecV2`,
  `quotLiftV2`, `psigmaV2`, …) over `piR`/`lamR`;
* `TupleTower` — the uniform tuple model for directly-installed
  structures: `sigmaSet`-built, unit-terminated pair towers, the
  tupler `mkTower` and the projection family (namespace
  `ConLeche.SetTheory.Tower`, unchanged).

`Ops` and `Value` carry the namespace `ConLeche.SetModel`.  The tier
imports only `ConLeche/SetTheory/*` and `ConLeche/Term/*`; the Expr-facing
denotation and claims stand above it in `ConLeche/Semantics/*`.
-/
