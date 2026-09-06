import Setlec.SetModel.Ops
import Setlec.SetModel.Value
import Setlec.SetModel.TupleTower

/-!
# `Setlec.SetModel` — the pure set constructions

The Expr-free half of the former `Setlec/SetBase/*` (split 2026-09-06,
cleanup pass A): set constructions over an abstract `SetTheory V` that
mention neither `Expr` nor the annotated syntax `AVExpr`.

* `Ops` — `piR`/`lamR`/`app`, the two-regime dependent product and
  abstraction (the `R` is *regime*, not the retired R lane);
* `Value` — the built-in constants' value towers (`natRecV2`,
  `quotLiftV2`, `psigmaV2`, …) over `piR`/`lamR`;
* `TupleTower` — the uniform tuple model for directly-installed
  structures: `sigmaSet`-built, unit-terminated pair towers, the
  tupler `mkTower` and the projection family (namespace
  `Setlec.SetTheory.Tower`, unchanged).

`Ops` and `Value` carry the namespace `Setlec.SetModel`.  The tier
imports only `Setlec/SetTheory/*` and `Setlec/TT/*`; the Expr-facing
denotation and claims stand above it in `Setlec/Semantics/*`.
-/
