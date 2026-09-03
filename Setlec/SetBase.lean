import Setlec.SetBase.Ops
import Setlec.SetBase.Value
import Setlec.SetBase.Syntax
import Setlec.SetBase.Interp
import Setlec.SetBase.Kit
import Setlec.SetBase.Ok2
import Setlec.SetBase.DefEqList
import Setlec.SetBase.EqTower
import Setlec.SetBase.EraseInv
import Setlec.SetBase.ProjPhase
import Setlec.SetBase.DivModEval

/-!
# `Setlec.SetBase` — the lane-neutral semantic primitives (task #161, S1)

THE SEPARATION (task #161) splits the two model proofs into disjoint
subtrees: `Setlec.SetR.*` (the collapsed model — `EnvS`, `Sound/*`,
`Install/*`, the `R`/`R2` capstones) and the graded-model tree (the `P`
lane).  Six modules belonged to neither: they are the *semantic and
syntactic primitives both lanes stand on*, filed under `SetR/Interp2`
and `SetR/Annot` for historical reasons only (design census §2.3).
S1 re-based them here, below both lanes:

* `Ops` — `piR`, `lamC`, `app`, `piR_dom_unique` over the `SetTheory`
  interface;
* `Value` — the graded value tower (with `TT.Const`);
* `Syntax` — `AVExpr` and `AVExpr.erase`, the annotated syntax both
  lanes read (`erase` is the collapsed lane's own reading function);
* `Interp` — `interp`/`interp2`;
* `Kit` — the membership kit over `interp2`;
* `Ok2` — `AnnotOk2`, the annotation invariant.  `Install/Axiom.lean`
  states `AnnotOk2` conjuncts for the P consumer; that import was the
  *single* R→P edge in the whole tree, and this re-basing kills it.

**Only the file paths and module names moved.**  The Lean namespaces
(`Setlec.SetR.Interp2`, `Setlec.SetR`) are unchanged, so every frozen
statement keeps its name verbatim and no consumer outside the `import`
lines was touched — the statement-freeze discipline (task #161).
-/
