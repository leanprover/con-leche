module

public import ConLeche.Model.Inductives.DeclBlock
import ConLeche.Model.Inductives.BlockAccRunCont
public section

/-!
# The uniform block step at NESTED blocks — the integration contract of `nested`

`declBlock_nested` (lane NESTKERN, NESTPLAN L4): the P carrier survives
the uniform install's run with the ROUTE SWITCH ON (`DeclBlockRun … true`,
`uniformNested`: containers accepted by the positivity function, the
auxiliary recursors checked at their outside majors and their rules
stored `.nested`, `consBlockRecsT`).  It is `declBlock_gen` — the block
step written once for both switch positions — at `nst = true`, and every
fact the switch-off step gets from a stage theorem that reads the flat
walk or member majors is an OWED premise here, named and tagged with the
lane that discharges it.  Everything else is read off the run
(`declBlock_gen`: the conses, the lfp clause's record, coverage, the
tables).

The flip (L9) needs this theorem premise-free; the nested proof lanes
land as CONSUMED checkpoints of it (a premise replaced by its proof).
Its premise-free form is `declBlock_nested_proved`
(`TargetNodeCalls.lean`, lane NESTIND session 28): the recursors' stage
from the proved calls, `nestedNodeCallsOwed`.

The owed premises, and who owes what:

* (W) — **PROVED** (lane ACCMODEL session 3, a consumed checkpoint):
  `nestedAccOwed` (`BlockAccRunCont.lean`), from the container case
  `contAcc` (`ContAcc.lean`: the cache invariant `CacheInvA`, the frame
  walk `frame_acc`, the leaf) and the run inversion `nestPos_acc`, the
  telescope's one bound, `blockCtorAcc_of_walk`, `LfpDatum.accTuple_holeOp`.
  `NestedAccOwed` (`BlockPosRunCont.lean`), for the record:
  the hole operator accessible at `w ≠ 0` with one bound of the level,
  at a block the install walked with the route switch on; the block step
  turns it into (W), the closed tuple, by `closed_of_acc` (maintainer
  ruling: (W) from accessibility; with the switch off the same, through
  `blockAccTuple_of_run_flat`).  Stated as a producer: the datum's records,
  the positivity run at the switch, its links to the datum, coverage at
  the walk's carrier and the formers.  It is the one part of the constructors' stage the
  nested run still owes: the rest of `BlockCtorStageAt … true` is
  PROVED (`blockCtorStageAt_nested`, lane NESTKERN session 2):
  - the positivity stage's reading facts at container kinds (L4):
    `StoredFieldShapes` at every kind (`holeApp` from the kernel's M3
    check on the walk's normal form, `Expr.holesApplied`; the flat
    presentation only with the switch off), the normal form member-free
    (M2′ on the normal form), `blockRunLink` and its consumers generic in
    the switch;
  - the operator's monotonicity at container kinds (L3/COVERB):
    `CtorPos` from `contSem` (`blockCtorPos_of_run_gen`), the walk's
    cache invariant threaded through the block's constructors
    (`checkBlockPositivity_inv_I`, `cacheInv_empty`,
    `nestMemberCtor_sem_cont`), `ContCover` at the walk's carrier from
    the input's coverage (`lfpCover_formers`, `contCover_of`).
* **`NestedRecStageOwed`** — **L5 (NESTIND) + L6 (NESTIND/AUXFIRE)**: the
  recursors' stage at outside majors, `BlockRecStagedT` (the four
  cons-monotonicities at `consBlockRecsT`) from the stage's own run
  (`checkBlockRec … true …`, the target check at `outside = true`), the
  block's POSITIVITY run at the formers' environment (route A, maintainer
  ruling of 2026-09-25: the recursor stage may read it; its consumers are
  to go through ONE declarative positivity derivation, lane POSDERIV) and
  the constructors' records, the carrier covered:
  - L5: the records at `outside` (`TargetMajorRun.outside`), the graph
    producer at clause classes (`graphRecPre_core` over `NestKit`: `ok`,
    `trans`, `calls`, `top`, `huniq`), and the rule typing at container
    constructors (O12: the field segment at the INSTANTIATED constructor,
    the index reading at the container's indices);
  - L6: `RecRuleLaw` for the `.nested` rules (`blockRecRuleLaw_gen`, the
    pins graded at the prefix — kernel F2, `targetMajorPins`).
  REDUCED (lane NESTIND, session 14, `NestedRecStage.lean`):
  `nestedRecStageOwed_of` from `NestedClassIndOwed` (the class induction,
  `TgtClassInd`) alone (lane RECREST discharged the rest).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **OWED by L5 (NESTIND) + L6 (NESTIND/AUXFIRE)** — see the module
docstring: the recursors' stage at outside majors, from its own run with
the switch on and the block's positivity run, at the constructors'
records and a covered carrier. -/
@[expose] def NestedRecStageOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)) (nodesR : ConLeche.NestNodes),
    ConLeche.checkBlockRec (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp true
      (true && ConLeche.blockNestedBit pp.toBlockShape kindsR)
      (ConLeche.nestKindsFlat kindsR) nodesR block cvTasR ctorsAsR
      (ConLeche.blockNormalCtors pp.toBlockShape ctorsAsR nfsR) = .ok out →
    -- the block's positivity run (route A, maintainer 2026-09-25), at the
    -- formers' environment `envI`, whose constructors' cons is `envC`
    ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pp cvTasR ctorsAsR true = .ok (kindsR, nfsR, nodesR) →
    envC = ConLeche.consBlockCtors pp.nP ctorsAsR envI →
    ctorsAsR.map (·.map (fun cA => (cA.1.name, cA.2)))
      = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) →
    pp.toBlockShape.memberNames.Nodup →
    BlockNamesOk (V := V) dR cvTasR →
    BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A envI
      pp.ctorNamesAt →
    BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k →
    (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) →
    (∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      dR = blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf) →
    dR.toLfp ∈ mpC.lfpBlocks →
    LfpCover mpC [] →
    FormersModelAt (V := V) envI pp.toBlockShape.memberNames mpC dR pp.lps cvTasR
      pp.toBlockShape isRecR →
    BlockOverEnv envC pp.toBlockShape.memberNames →
    BlockRecStagedT (V := V) μ envC pp.toBlockShape out mpC

/-- **THE UNIFORM BLOCK STEP AT NESTED BLOCKS** (lane NESTKERN, the
integration contract of `nested`): the install's run with the route
switch on, from a covered carrier, leaves a covered carrier — given (W)
for the nested hole operator and the recursors' stage (see the module
docstring for the lanes).  The shape is
`BlockCoverPB`'s ("coverage in ⇒ some covered carrier out"), the one the
fold's block step takes at the flip. -/
theorem declBlock_nested (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂ true)
    -- OWED: L5 (records, graph producer at clause classes, O12) + L6 (`.nested` rule law)
    (hrec : NestedRecStageOwed V μ F block) :
    LfpCover mp [] → ∃ mp' : EnvModelM V μ env₂, LfpCover mp' [] := by
  intro hcov
  obtain ⟨mp', h⟩ := declBlock_gen hμ mp hE hdp hrun
    (blockCtorStageAt_nested hμ mp (nestedAccOwed hμ F) hcov)
    fun envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hRec hPos henvC hnames
      hnd hN hS hcore hctorsAs hdR hlfp hcovC hmk hover =>
      hrec envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR nodesR hRec hPos henvC
        hnames hnd hN hS hcore hctorsAs hdR hlfp (hcovC hcov) (hmk hcov) hover
  exact ⟨mp', h hcov⟩

end ConLeche.Model
