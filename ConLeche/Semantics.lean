module

public import ConLeche.Semantics.Syntax
public import ConLeche.Semantics.Interp
public import ConLeche.Semantics.Kit
public import ConLeche.Semantics.WellDenoted
public import ConLeche.Semantics.DefEqList
public import ConLeche.Semantics.EqTower
public import ConLeche.Semantics.EraseInv
public import ConLeche.Semantics.ProjPhase
public import ConLeche.Semantics.DivModEval
public import ConLeche.Semantics.Frame
public import ConLeche.Semantics.LitParams
public import ConLeche.Semantics.Sat
public import ConLeche.Semantics.WhnfCoreLeaf
public import ConLeche.Semantics.DefEqStep
public import ConLeche.Semantics.Canon
public import ConLeche.Semantics.LitStep
public import ConLeche.Semantics.DenoteClosed
public import ConLeche.Semantics.Install
public import ConLeche.Semantics.ConstsBound
public import ConLeche.Semantics.BasisType
public import ConLeche.Semantics.Univ
public import ConLeche.Semantics.BasisOk
public import ConLeche.Semantics.Skeleton
public import ConLeche.Semantics.Hoist
public import ConLeche.Semantics.Decl
public import ConLeche.Semantics.DeclEta
public import ConLeche.Semantics.DeclRun
public import ConLeche.Verify.Inductives.SumWF
public import ConLeche.Semantics.Inductives.DeclSumEta
public import ConLeche.Semantics.DeclIndRun
public import ConLeche.Semantics.IndBlockFacts
public import ConLeche.Semantics.IndBlockRun
public import ConLeche.Semantics.EnvFacts
public import ConLeche.Semantics.EnvFactsCons
public import ConLeche.Semantics.IndRecsCore
public import ConLeche.Semantics.BasisRules
public import ConLeche.Semantics.Tower.TowerIntro
public import ConLeche.Semantics.Tower.TowerLeaf
public import ConLeche.Semantics.Tower.TowerMk
public import ConLeche.Semantics.Tower.TowerRec
public import ConLeche.Semantics.Tower.TowerWire
public import ConLeche.Semantics.ProjFnFacts
public import ConLeche.Semantics.Bridge.Decl
public import ConLeche.Semantics.Bridge.DeclRun
public import ConLeche.Semantics.Bridge.DeclIndRun
public import ConLeche.Semantics.Bridge.Sound

@[expose] public section

/-!
# `ConLeche.Semantics` — the Expr-facing semantic tier

**Split from `ConLeche/SetBase/*` on 2026-09-06** (cleanup pass A, user
ruling: *"SetModel or Semantics/SetInterp are decent names"*), by
Expr-freeness.  What stayed pure — the two-regime product and
abstraction (`piR`/`lamR`), the built-in constants' value towers and
the unit-terminated tuple tower — is `ConLeche/SetModel/*`, the
namespace `ConLeche.SetModel`, and mentions neither `Expr` nor the
annotated syntax.  Everything that reads a term lives here: the
annotated syntax `AnnotTerm` and its two-regime interpretation `interp`,
the membership kit, `WellDenoted`, the canonical annotation pass, the
per-declaration run records and the run bridge (`Bridge/*`), the
direct-structure declaration records (`Direct/*`) and the tower
introduction machinery that reads annotated field domains
(`Tower/*`).  The namespace is `ConLeche.Semantics` (formerly
`ConLeche.SetR.Interp` and `ConLeche.SetR`, both retired with the
collapsed lane they were named for).  The layering rule is unchanged
in substance: `ConLeche/{Kernel,Cached,Frontend}/*` and `Main.lean`
never import this tier, `ConLeche/Model/*` stands on it.

The history below is the base tier's own record (task #161), kept as
written; its paths and namespaces are those of the time.
-/

/-!
# `ConLeche.SetBase` — the lane-neutral semantic primitives (task #161, S1)

THE SEPARATION (task #161) splits the two model proofs into disjoint
subtrees: `ConLeche.SetR.*` (the collapsed model — `EnvS`, `Sound/*`,
`Install/*`, the `R`/`R2` capstones) and the graded-model tree (the `P`
lane).  Six modules belonged to neither: they are the *semantic and
syntactic primitives both lanes stand on*, filed under `SetR/Interp`
and `SetR/Annot` for historical reasons only (design census §2.3).
S1 re-based them here, below both lanes:

* `Ops` — `piR`, `lamC`, `app`, `piR_dom_unique` over the `SetTheory`
  interface;
* `Value` — the graded value tower (with `Term.Const`);
* `Syntax` — `AnnotTerm` and `AnnotTerm.erase`, the annotated syntax both
  lanes read (`erase` is the collapsed lane's own reading function);
* `Interp` — `interp`/`interp`;
* `Kit` — the membership kit over `interp`;
* `WellDenoted` — `WellDenoted`, the annotation invariant.  `Install/Axiom.lean`
  states `WellDenoted` conjuncts for the P consumer; that import was the
  *single* R→P edge in the whole tree, and this re-basing kills it.

S2 (the 2U/R move) added, on the same terms:

* `Frame` — `frame_open2`, the opened binder's frame conditions (pure
  `Expr` scoping);
* `LitParams` — the two `*_levelParams_nil` reads off the literal
  support guards;
* `Sat` — `Sat` with its intro lemmas, and `interpC_trans`;
* `WhnfCoreLeaf` — the six `whnfCoreR_*` `rfl` lemmas about the kernel's
  `whnfCore` (S1 deferred them here by name);
* `DefEqStep` — the definitional-equality quarter's Tier A clauses,
  which are pure `interp` algebra and which both lanes' `DefEq…P`
  quarters consume (whole-module move of `Interp/Steps/DefEq`);
* `Canon` — `sortOfE`/`lamSortE`, the annotated literal spines
  (`natLitAV`, `charListAV`), the canonical annotation pass `denoteAnnot`
  and its erasure law (whole-module move of `Annot/Canon`).  `denoteAnnot`
  takes the annotated valuation as a *parameter*, so the pass carries
  no environment at all;
* `LitStep` — `natLit_factsAV`, the numeral induction over
  `natLitAV` (whole-module move of `Interp/Steps/Lit`).

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

* `EnvFacts` — **the bridge invariant** (whole-module move of
  `SetR/Bridge/Env`).  It never had a lane: every field is V-free by
  construction (the module docstring says so), its four imports are
  all base, and both lanes now build one — the R lane by projection
  from `EnvS` (`EnvS.toEnvFacts`), the P lane by projection from
  `EnvModelM` (`EnvModelM.toEnvFacts`), which is what lets the P fold call the
  bridge without a collapsed-model carrier.

S7 (the de-basing's last wall) added `IndRecsCoreR`, `ProjFnRR`,
`BasisRules` and `PSigmaTower` — the sixteen syntactic declarations
the P lane had been resolving *through* the four dying imports.
(`PSigmaTower` and `ProjPins` were deleted with the pinned `PSigma'`
block at task #175 W6.)

S8 (**THE ZERO-OPENER**) added `Bridge/*` — the whole
checker-to-derivation bridge, twenty-two modules, from `Claims` to
`Sound`:

* the inference chain (`Claims` … `Main`), which never mentioned a
  model at all — twenty of the twenty-three modules were already
  `EnvS`-free at S7;
* `Bridge/Decl` — the six per-kind declaration bridges and their front
  doors, model-free since S5 (`EnvFacts`-signed, zero proof edits);
* `Bridge/DeclInd` — the interleaved `indDecl` walk, model-free since
  S7 (`declIndRR`, off an `EnvFacts`; its `EnvS` instance `declIndRS` was
  consumer-free after that re-proof and is deleted);
* `Bridge/Sound` — `structParts?_none`, `checkDeclR_ofEnvR` and
  `checkDeclR_ofEnvRE`, the dispatch off an `EnvFacts`.

S11a added `Bridge/DeclRun` — the **run-only** bridges for the five
non-`ind` declaration kinds (`declDefnRun_of`, `declThmRun_of`,
`declOpaqueRun_of`, `declAxiomRun_of`, `declBasisRun` verbatim) and
the dispatch `checkDeclRun_of`, whose only route into the derivation
tier is `DeclRun`'s `Ind` parameter.  `Bridge/Sound` assembles it as
`checkDeclRun_ofEnvFactsE` (the `Ind` slot filled by `declIndRR` until
S11b), and that — not `checkDeclR_ofEnvRE` — is what the graded fold
now imports.  The measurement is `tests/proofdeps.sh`'s, not this
file's: the criterion is the proof term, and an import listing cannot
see it (S9's finding).

`checkDeclR_ofEnvRE` is the theorem the graded fold imports, and its
residence here rather than under `ConLeche/SetR/` is what takes the
layering whitelist to **zero**: `tests/layering.sh` reads
`0 P->R edges (whitelist EMPTY)`.  What stayed in `ConLeche/SetR/Bridge/`
is exactly the collapsed lane's own two instances — `EnvS.toEnvFacts`
(`Decl.lean`) and `checkDeclR_sound`/`foldlM_R` (`Sound.lean`).

**Only the file paths and module names moved.**  The Lean namespaces
(`ConLeche.SetR.Interp`, `ConLeche.SetR`) are unchanged, so every frozen
statement keeps its name verbatim and no consumer outside the `import`
lines was touched — the statement-freeze discipline (task #161).
-/
