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
import Setlec.SetBase.Denote2Closed
import Setlec.SetBase.Install2
import Setlec.SetBase.ConstsBound
import Setlec.SetBase.BasisType
import Setlec.SetBase.Univ
import Setlec.SetBase.BasisOk
import Setlec.SetBase.Skeleton
import Setlec.SetBase.Hoist
import Setlec.SetBase.Rel
import Setlec.SetBase.ProjPins
import Setlec.SetBase.Weaken
import Setlec.SetBase.CtxOkR
import Setlec.SetBase.Decl
import Setlec.SetBase.DeclEta
import Setlec.SetBase.DeclRun
import Setlec.SetBase.DeclIndRun
import Setlec.SetBase.IndBlockR
import Setlec.SetBase.IndBlockRun
import Setlec.SetBase.EnvR
import Setlec.SetBase.EnvRCons
import Setlec.SetBase.IndRecsCoreR
import Setlec.SetBase.BasisRules
import Setlec.SetBase.PSigmaTower
import Setlec.SetBase.ProjFnRR
import Setlec.SetBase.Bridge.Claims
import Setlec.SetBase.Bridge.WhnfCore
import Setlec.SetBase.Bridge.Infer
import Setlec.SetBase.Bridge.DefEq
import Setlec.SetBase.Bridge.ReduceNat
import Setlec.SetBase.Bridge.InferStruct
import Setlec.SetBase.Bridge.Spine
import Setlec.SetBase.Bridge.Irrel
import Setlec.SetBase.Bridge.Certs
import Setlec.SetBase.Bridge.StuckIrrel
import Setlec.SetBase.Bridge.Eta
import Setlec.SetBase.Bridge.StrLitR
import Setlec.SetBase.Bridge.Stuck
import Setlec.SetBase.Bridge.EtaCerts
import Setlec.SetBase.Bridge.DefEqClosed
import Setlec.SetBase.Bridge.Proj
import Setlec.SetBase.Bridge.ProjRed
import Setlec.SetBase.Bridge.Major
import Setlec.SetBase.Bridge.Iota
import Setlec.SetBase.Bridge.Main
import Setlec.SetBase.Bridge.Decl
import Setlec.SetBase.Bridge.DeclInd
import Setlec.SetBase.Bridge.DeclRun
import Setlec.SetBase.Bridge.DeclIndRun
import Setlec.SetBase.Bridge.Sound

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

S4 (the C3 artifact) added the **shared record family** — the design
census's spec point 1 ("the bridge records are shared; the derivations
are R's"), unblocked by S2's finding 2 (`Infer`/`DefEq` became base
names when `SetR/Rel` moved, so `DeclR`'s derivation conjuncts stopped
being a reason to keep the file in R):

* `Weaken` — the mutual weakening lemmas for the `Rel` relations
  (whole-module move of `SetR/Weaken`);
* `CtxOkR` — the context correspondence for the relation family
  (whole-module move of `SetR/CtxOkR`);
* `Decl` — **`DeclR` and the whole per-kind record family**
  (whole-module move of `SetR/Decl`); both lanes state over it, the R
  lane proves it (`Bridge/*`), the P lane consumes its run/guard
  conjuncts;
* `DeclEta` — `declEtaStep`, the fold's model-free η half (S3's C4;
  whole-module move of `SetR/DeclEta`, which sat in R only because
  `Decl` did);
* `IndBlockR` — the inductive block's relation-level residue and
  `declIndEtaClosed` (S5's ind unit: the C4 refutation's bill, paid —
  the `indMembersR_*`/`indRecsR_*`/`ExtEta` lemmas moved here verbatim
  from `SetR/Install/{IndMembersS,IndRecsS,DeclIndS}`, plus
  `indRecsR_keep`, which replaces `indRecsS`'s model-carrying
  `hnonrecUp`).

S6 (the residue) added:

* `EnvR` — **the bridge invariant** (whole-module move of
  `SetR/Bridge/Env`).  It never had a lane: every field is V-free by
  construction (the module docstring says so), its four imports are
  all base, and both lanes now build one — the R lane by projection
  from `EnvS` (`EnvS.toEnvR`), the P lane by projection from
  `EnvS2PM` (`EnvS2PM.toEnvR`), which is what lets the P fold call the
  bridge without a collapsed-model carrier.

S7 (the de-basing's last wall) added `IndRecsCoreR`, `ProjFnRR`,
`BasisRules` and `PSigmaTower` — the sixteen syntactic declarations
the P lane had been resolving *through* the four dying imports.

S8 (**THE ZERO-OPENER**) added `Bridge/*` — the whole
checker-to-derivation bridge, twenty-two modules, from `Claims` to
`Sound`:

* the inference chain (`Claims` … `Main`), which never mentioned a
  model at all — twenty of the twenty-three modules were already
  `EnvS`-free at S7;
* `Bridge/Decl` — the six per-kind declaration bridges and their front
  doors, model-free since S5 (`EnvR`-signed, zero proof edits);
* `Bridge/DeclInd` — the interleaved `indDecl` walk, model-free since
  S7 (`declIndRR`, off an `EnvR`; its `EnvS` instance `declIndRS` was
  consumer-free after that re-proof and is deleted);
* `Bridge/Sound` — `directParts?_none`, `checkDeclR_ofEnvR` and
  `checkDeclR_ofEnvRE`, the dispatch off an `EnvR`.

S11a added `Bridge/DeclRun` — the **run-only** bridges for the five
non-`ind` declaration kinds (`declDefnRunR_of`, `declThmRunR_of`,
`declOpaqueRunR_of`, `declAxiomRunR_of`, `declBasisR` verbatim) and
the dispatch `checkDeclRun_of`, whose only route into the derivation
tier is `DeclRunR`'s `Ind` parameter.  `Bridge/Sound` assembles it as
`checkDeclRun_ofEnvRE` (the `Ind` slot filled by `declIndRR` until
S11b), and that — not `checkDeclR_ofEnvRE` — is what the graded fold
now imports.  The measurement is `tests/proofdeps.sh`'s, not this
file's: the criterion is the proof term, and an import listing cannot
see it (S9's finding).

`checkDeclR_ofEnvRE` is the theorem the graded fold imports, and its
residence here rather than under `Setlec/SetR/` is what takes the
layering whitelist to **zero**: `tests/layering.sh` reads
`0 P->R edges (whitelist EMPTY)`.  What stayed in `Setlec/SetR/Bridge/`
is exactly the collapsed lane's own two instances — `EnvS.toEnvR`
(`Decl.lean`) and `checkDeclR_sound`/`foldlM_R` (`Sound.lean`).

**Only the file paths and module names moved.**  The Lean namespaces
(`Setlec.SetR.Interp2`, `Setlec.SetR`) are unchanged, so every frozen
statement keeps its name verbatim and no consumer outside the `import`
lines was touched — the statement-freeze discipline (task #161).
-/
