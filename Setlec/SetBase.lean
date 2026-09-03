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
import Setlec.SetBase.Frame
import Setlec.SetBase.LitParams
import Setlec.SetBase.Sat2
import Setlec.SetBase.WhnfCoreLeaf
import Setlec.SetBase.DefEqStep2
import Setlec.SetBase.Canon
import Setlec.SetBase.LitStep2

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

S2 (the 2U/R move) added, on the same terms:

* `Frame` — `frame_open2`, the opened binder's frame conditions (pure
  `Expr` scoping);
* `LitParams` — the two `*_levelParams_nil` reads off the literal
  support guards;
* `Sat2` — `Sat2` with its intro lemmas, and `interp2C_trans`;
* `WhnfCoreLeaf` — the six `whnfCoreR_*` `rfl` lemmas about the kernel's
  `whnfCore` (S1 deferred them here by name);
* `DefEqStep2` — the definitional-equality quarter's Tier A clauses,
  which are pure `interp2` algebra and which both lanes' `DefEq…P`
  quarters consume (whole-module move of `Interp2/Step2/DefEq`);
* `Canon` — `sortOfE`/`lamSortE`, the annotated literal spines
  (`natLitT2`, `charListT2`), the canonical annotation pass `denote2`
  and its erasure law (whole-module move of `Annot/Canon`).  `denote2`
  takes the annotated valuation as a *parameter*, so the pass carries
  no environment at all;
* `LitStep2` — `natLit_facts2`, the numeral induction over
  `natLitT2` (whole-module move of `Interp2/Step2/Lit`).

**Only the file paths and module names moved.**  The Lean namespaces
(`Setlec.SetR.Interp2`, `Setlec.SetR`) are unchanged, so every frozen
statement keeps its name verbatim and no consumer outside the `import`
lines was touched — the statement-freeze discipline (task #161).
-/
