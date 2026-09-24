module

public import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Model.Cover
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

The owed premises, and who owes what:

* **`NestedCtorStageOwed`** — the constructors' stage at the nested run
  (`BlockCtorStageAt … true`: what `blockTablesStage_of` and
  `blockCtorPos_of_run` produce with the switch off), under the input's
  coverage.  Its parts, by lane:
  - **L4 (NESTKERN), next checkpoint**: the positivity stage's reading
    facts at container kinds — `blockRunLink`'s conclusion WITHOUT the
    flat presentation (the normal form's reading as the hole telescope,
    `StoredFieldShapes`: `len`, `holeApp`, `override`), which today reads
    `storedWalk_fields`/`storedWalk_nestOcc` at flat kinds only; and the
    walk's cache invariant threaded through the block's constructors
    (`CacheInv`, from `cacheInv_empty`, per constructor by
    `nestMemberCtor_sem_cont`).
  - **L3/COVERB**: the operator's monotonicity at container kinds —
    `CtorPos` from `nestMemberCtor_sem_cont`, whose one input is
    `ContCover` at the walk's carrier (the formers' environment): COVERB's
    recipe, `lfpCover_append` at `consBlockInds_consts` from the input's
    `LfpCover mp []` (the premise's hypothesis).
  - **L7 (NESTW)**: the hole operator's closed tuple at `w ≠ 0`
    (`BlockCtorsStage.holeFun`'s second half; with the switch off
    `blockHoleClosed_of` from the flat presentation) —
    `closed_of_wide_groups` (`SetModel/NestWide.lean`) through the wide
    datum.
* **`NestedRecStageOwed`** — **L5 (NESTIND) + L6 (NESTIND/AUXFIRE)**: the
  recursors' stage at outside majors, `BlockRecStagedT` (the four
  cons-monotonicities at `consBlockRecsT`) from the stage's own run
  (`checkBlockRec … true …`, the target check at `outside = true`) and
  the constructors' records, the carrier covered:
  - L5: the records at `outside` (`TargetMajorRun.outside`), the graph
    producer at clause classes (`graphRecPre_core` over `NestKit`: `ok`,
    `trans`, `calls`, `top`, `huniq`), and the rule typing at container
    constructors (O12: the field segment at the INSTANTIATED constructor,
    the index reading at the container's indices);
  - L6: `RecRuleLaw` for the `.nested` rules (`blockRecRuleLaw_gen`, the
    pins graded at the prefix — kernel F2, `targetMajorPins`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockParts)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **OWED by L4 (NESTKERN: the reading facts at container kinds, the
cache invariant's threading) + L3/COVERB (`CtorPos` from `ContCover`) +
L7 (NESTW: the closed tuple at `w ≠ 0`)** — see the module docstring:
the constructors' stage at the nested run, at a covered input carrier. -/
@[expose] def NestedCtorStageOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    {env : Env} (mp : EnvModelM V μ env) : Prop :=
  LfpCover mp [] → BlockCtorStageAt V μ F mp true

/-- **OWED by L5 (NESTIND) + L6 (NESTIND/AUXFIRE)** — see the module
docstring: the recursors' stage at outside majors, from its own run with
the switch on, at the constructors' records and a covered carrier. -/
@[expose] def NestedRecStageOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)),
    ConLeche.checkBlockRec (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp true
      (true && ConLeche.blockNestedBit pp.toBlockShape kindsR)
      (ConLeche.nestKindsFlat kindsR) block cvTasR ctorsAsR
      (ConLeche.blockNormalCtors pp.toBlockShape ctorsAsR nfsR) = .ok out →
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
    BlockRecStagedT (V := V) μ envC pp.toBlockShape out mpC

/-- **THE UNIFORM BLOCK STEP AT NESTED BLOCKS** (lane NESTKERN, the
integration contract of `nested`): the install's run with the route
switch on, from a covered carrier, leaves a covered carrier — given the
two owed stages (see the module docstring for the lanes).  The shape is
`BlockCoverPB`'s ("coverage in ⇒ some covered carrier out"), the one the
fold's block step takes at the flip. -/
theorem declBlock_nested (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂ true)
    -- OWED: L4 (reading facts, cache threading) + L3/COVERB (`CtorPos`) + L7 (closed tuple)
    (hctor : NestedCtorStageOwed V μ F mp)
    -- OWED: L5 (records, graph producer at clause classes, O12) + L6 (`.nested` rule law)
    (hrec : NestedRecStageOwed V μ F block) :
    LfpCover mp [] → ∃ mp' : EnvModelM V μ env₂, LfpCover mp' [] := by
  intro hcov
  obtain ⟨mp', h⟩ := declBlock_gen hμ mp hE hdp hrun (hctor hcov)
    fun envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hRec hnames hnd hN hS
      hcore hctorsAs hdR hlfp hcovC =>
      hrec envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hRec hnames hnd hN hS
        hcore hctorsAs hdR hlfp (hcovC hcov)
  exact ⟨mp', h hcov⟩

end ConLeche.Model
