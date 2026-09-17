module

public import ConLeche.Model.Inductives.NestedCore
import ConLeche.Verify.Inductives.NestedAuxInv
import ConLeche.Verify.Inductives.NestedElimInv
public section

/-!
# `declNested_of` — the nested assembly's run-level consumer (task #315, M6 s3 / M7-2)

**THE run-level consumer of the nested half**: the model of the
pre-block environment survives the nested install's run
(`DeclNestedRun`, `Semantics/Inductives/DeclNested.lean`), given two
named facts that M6/M7 discharge — `declBlock`'s pattern (DESIGN §U.6)
at the nested block:

* `NestedCoreModeled` (M6): the run's stages through the restored
  constructors keep the model and leave THE BLOCK MODEL of the nested
  block at the constructors' environment — the composed block model
  `nestedBlockModel` (`NestedCore.lean`) CONCRETELY, together with the
  scratch install's formers' facts and the constructors' loop's outputs
  the recursors' stage reads (`NestedCoreOut`, task #315 M7-2, DESIGN
  §U.29: the block model "grows at its consumer" — the recursors' kit
  is stated at `nestedBlockModel` and its pins' constructors, so the
  tail sees the parameters, not an existential `d`);
* `NestedTailModeled` (M7): from there the restored recursors (at
  `k + nPins` motives), their rules, the projection tables and the
  two post-checks keep the model to the post-block environment.

The containers' block models are the pre-block CARRIER'S OWN
(`EnvModelB`, task #315 M7-3: `EnvModelM` with the field
`EnvBlockModels` — every stored inductive is a member of a block whose
block model holds at the model, with its injections the tagged towers
at the constructors' MEMBER-LOCAL positions; DESIGN §U.13 (f) 1's
field); at the pins it is read as `PinsModeled`.  Those definitions and
the run's record live in `NestedPremise.lean`, below `NestedCore.lean`;
the crossing kit that carries a container's block model over an
environment extension is `ContainerCross.lean`.  `nestedCoreModeled_of`
(the core's discharge modulo the restored constructors' loop) lives
here with its statement.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level CheckMode ConstantInfo ConstantVal RecFieldKind RecRule
  NestedParts MutualBlock AuxStored ElimState NestedPin ContainerInfo IndCaps fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The core's output: the block model, concretely -/

/-- **The nested core's output** — what the recursors' stage (M7) reads
of the constructors' stage, at the run's data: the scratch install's
formers' run and facts (`MutualFormersFacts` at the `auxRoute` grade),
the scratch constructors' run, the block's shape, the restored
constructors' stage's outputs at the model `mp₂` of the restored
environment (`NestedStageFacts`: the members' leaves, the restored
constructors' leaves and readings, the pin groups, the agreement off
the block), and the CONCRETE block model `nestedBlockModel` at every
member, with the members, constructors and pins typed and its record. -/
structure NestedCoreOut {env : Env} (F : Nat) (mp : EnvModelM V μ env) (p : NestedParts)
    (st : ElimState) (b : MutualBlock) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
    (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
    (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
    (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
    (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
    (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
    (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
    (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
    (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
    (pinsS : List PinSyn)
    (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
      (ConLeche.consMutualFormers (fms.take p.k) env))) : Prop where
  formers : ConLeche.mutualFormers (m := ConLeche.CheckM) (fueledOps μ F) b.nP b.formers env true
    = .ok (ConLeche.consMutualFormers fms env, fms)
  facts : MutualFormersFacts V F true mp b fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
    fvsPF xFvsF xrestF eissF tssF
  ctors : ConLeche.checkMutualCtors (m := ConLeche.CheckM) (fueledOps μ F)
    (ConLeche.consMutualFormers fms env) b fms (Level.isEquiv f₀.s .zero == some true) true b.ctors
    = .ok (ctorsA, sortss)
  kindsRun : ConLeche.classifyMutualKinds (m := ConLeche.CheckM) b.members3 b.lps b.nP ctorsA
    = .ok kinds
  bk : b.k = p.k + pinsS.length
  grouped : ConLeche.mutualCtorsGrouped b.ctors = true
  nodup : b.blockNames.Nodup
  stage : NestedStageFacts (V := V) (mp := mp) (p := p) (b := b) (fms := fms) (f₀ := f₀) (ctorsA := ctorsA)
    (kinds := kinds) (env := env) (ppsF := ppsF) (W := W) (idxF := idxF) (dsF := dsF) (esF := esF)
    (srcsF := srcsF) (fvsPF := fvsPF) (xrestF := xrestF) (eissF := eissF) (tssF := tssF)
    (ctorsR := ctorsR) (dsR := dsR) (xFvsR := xFvsR) (pinsS := pinsS) st mp₂
  reps : IsBlockModels mp₂.base2 (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF
    dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)
  typed : ∀ ψ : Name → Nat,
    FormersTyped mp₂.base2 (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF
      dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS) ψ ∧
    CtorsTyped mp₂.base2 (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF
      dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS) ψ ∧
    PinsTyped mp₂.base2 (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env ppsF W idxF
      dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS) ψ
  record : NestedBlockModelOf env p st ctorsR (nestedBlockModel (V := V) p b fms f₀ ctorsA kinds env
    ppsF W idxF dsF esF srcsF fvsPF xrestF eissF tssF ctorsR dsR xFvsR pinsS)

/-! ## The named facts -/

/-- **The nested run's stages through the restored constructors keep
the model and leave the block model at the constructors'
environment** — `declNested_of`'s first named fact (M6): from a model
of the pre-block environment carrying the containers' block models
(`PinsModeled`) and the run's conjuncts through `restoreCtors`, a
model of the environment holding the restored formers and
constructors, agreeing with the pre-block model off the block, at
which the nested block's CONCRETE block model `nestedBlockModel` holds
at every member (`IsBlockModels`), with the members, the constructors
and the pins' containers typed, together with the scratch install's
and the loop's data (`NestedCoreOut`).  Consumer: `declNested_of`;
discharged modulo the loop by `nestedCoreModeled_of`. -/
@[expose] def NestedCoreModeled (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (p : NestedParts) (st : ElimState) (b : MutualBlock) (envAux : Env)
    (stored : List AuxStored) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (fmsA ctorsA : List ConstantVal),
    PinsModeled mp.base2 st.pins →
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true →
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true →
    ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA →
    ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA →
    ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st →
    st.pins.length = p.numNested →
    ConLeche.copiesFresh env p.k st = true →
    ConLeche.nestedContainersOk env st.pins = true →
    ConLeche.auxBlock p st = some b →
    ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux →
    ConLeche.auxStoredAll envAux b b.k = some stored →
    ConLeche.pinsClosed p.nP st.pins = true →
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins = .ok () →
    (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true →
    ConLeche.nestedCopySrcOk env p st = true →
    ConLeche.nestedGroupsOk env p st = true →
    -- THE PINS' SCOPE (K.30): every pin's free variables are the first
    -- former's openers, annotation included, and no loose bvar
    ConLeche.pinsScoped p.nP st = true →
    -- **THE COPIES' TARGETS** (K.32, task #315 L-E, DESIGN §U.64): a
    -- copy's group-internal recursive field points at the copy of the
    -- container member its own field points at, which the copies'
    -- identities read on the `ordF` arm (lane L-B's `NestedPinsShape`)
    ConLeche.nestedCopyTargetsOk env p b st stored = true →
    ConLeche.nestedPinKindsOk p b st stored = true →
    ConLeche.nestedPinRankOk env p b st stored = true →
    -- POST-CHECK (a) A THIRD TIME (K.30): the pins typed at the
    -- environment holding the RESTORED formers
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.consNestedFormers (stored.take p.k) env) p.nP st.pins = .ok () →
    (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR →
    ∃ (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
      (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
      (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
      (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
      (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
      (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
      (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
      (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
      (pinsS : List PinSyn)
      (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env))),
      ConLeche.consNestedFormers (stored.take p.k) env
        = ConLeche.consMutualFormers (fms.take p.k) env ∧
      NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
        fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂

/-- **The tail keeps the model**: at a model of the constructors'
environment carrying the nested block's block model, the run's
remaining stages — the restored recursor types at `k + nPins` motives,
their rules at the rule-less provision, the projection tables and the
two post-checks — cons a model of the post-block environment —
`declNested_of`'s second named fact (M7), at the core's CONCRETE output
(`NestedCoreOut`).  Consumer: `declNested_of`; its skeleton
`nestedTailModeled_of` (`NestedRecsStage.lean`). -/
@[expose] def NestedTailModeled (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) : Prop :=
  μ.verifiedChecks = true →
  ∀ {env : Env} (mp : EnvModelM V μ env), ConLeche.EtaFamiliesClosed env →
  ∀ (p : NestedParts) (envOut : Env) (st : ElimState) (b : MutualBlock) (envAux : Env)
    (stored : List AuxStored) (ctorsR : List (List (ConstantVal × Nat × Nat)))
    (cvRms cvRns : List ConstantVal) (rulesM rulesN : List (List RecRule))
    (fmsA ctorsA : List ConstantVal),
    PinsModeled mp.base2 st.pins →
    (p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      (p.ctors.map (fun c => c.cv.type)).all (fun t => !t.mentionsNestedAux)) = true →
    uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP
      (p.ctors.map (fun c => c.cv.type)) = true →
    ConLeche.nestedAnnotFormers (m := ConLeche.CheckM) (fueledOps μ F) env p.nP p.formers
      = .ok fmsA →
    ConLeche.nestedAnnotCtors (m := ConLeche.CheckM) (fueledOps μ F)
      (ConLeche.nestedFormerEnv fmsA env) p.ctors = .ok ctorsA →
    ConLeche.elimNested env p.nP p.lps (ConLeche.nestedTypes0 p fmsA ctorsA) = .ok st →
    st.pins.length = p.numNested →
    ConLeche.copiesFresh env p.k st = true →
    ConLeche.nestedContainersOk env st.pins = true →
    ConLeche.auxBlock p st = some b →
    ConLeche.checkMutualCore (m := ConLeche.CheckM) (fueledOps μ F) env b none true = .ok envAux →
    ConLeche.auxStoredAll envAux b b.k = some stored →
    ConLeche.pinsClosed p.nP st.pins = true →
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envAux p.nP st.pins = .ok () →
    (stored.take p.k).all (fun a => !a.caps.eta && (env.find? a.cvTa.name).isNone) = true →
    ConLeche.nestedCopySrcOk env p st = true →
    ConLeche.nestedGroupsOk env p st = true →
    ConLeche.nestedPinKindsOk p b st stored = true →
    (stored.take p.k).mapM (fun a =>
        ConLeche.restoreCtors (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.consNestedFormers (stored.take p.k) env) (ConLeche.restoreTbl p st) p.lps
          a.ctors)
      = .ok ctorsR →
    ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.k).map fun mIdx => ((p.formers.getD mIdx default).1.name.str "rec"))
        (stored.take p.k) = .ok cvRms →
    ConLeche.restoreRecTys (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        (ConLeche.restoreTbl p st) p.lps
        ((List.range p.numNested).map p.mimicRecName)
        (stored.drop p.k) = .ok cvRns →
    (cvRms.zip (stored.take p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name false cvRa.type a.mI a.rP a.rules)
      = .ok rulesM →
    (cvRns.zip (stored.drop p.k)).mapM (fun (cvRa, a) =>
        ConLeche.restoreRules (m := ConLeche.CheckM) (fueledOps μ F)
          (ConLeche.provisionNestedRecs
            ((cvRms.zip ((stored.take p.k).map fun (a : AuxStored) => (a.mI, a.rP)))
              ++ (cvRns.zip ((stored.drop p.k).map fun (a : AuxStored) => (a.mI, a.rP))))
            (ConLeche.consNestedCtors ctorsR.flatten
              (ConLeche.consNestedFormers (stored.take p.k) env)))
          (ConLeche.restoreTbl p st) cvRa.levelParams cvRa.name true cvRa.type a.mI a.rP a.rules)
      = .ok rulesN →
    ConLeche.nestedTables (m := ConLeche.CheckM)
        (((stored.take p.k).zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
          ((p.formers.getD mIdx default).1.name, a.tbl, cs))
        (ConLeche.storeNestedRecs
          ((cvRms.zip ((stored.take p.k).zip rulesM)).map
              (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
            ++ (cvRns.zip ((stored.drop p.k).zip rulesN)).map
              (fun (cv, a, rs) => (cv, a.mI, a.rP, rs)))
          (ConLeche.consNestedCtors ctorsR.flatten
            (ConLeche.consNestedFormers (stored.take p.k) env))) = .ok envOut →
    ConLeche.nestedPinsOk (m := ConLeche.CheckM) (fueledOps μ F) envOut p.nP st.pins = .ok () →
    (p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length) = true →
    ConLeche.nestedRecsOk (m := ConLeche.CheckM) (fueledOps μ F)
        (ConLeche.consNestedCtors ctorsR.flatten
          (ConLeche.consNestedFormers (stored.take p.k) env))
        p.nP b.k b.n
        ((((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
            (fun (((sr, cv), rs), mIdx) =>
              (sr, (b.ownCtors mIdx).map (fun (J, c) => (J, c.nF)), cv, rs)))
          ++ (((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
            (fun (((sr, cv), rs), j) =>
              (sr, (b.ownCtors (p.k + j)).map (fun (J, c) => (J, c.nF)), cv, rs))))
      = .ok () →
    ∀ (fms : List MutualFormerA) (f₀ : MutualFormerA) (ctorsA : List (ConstantVal × Nat))
      (sortss : List (List Level)) (kinds : List (List (RecFieldKind × Nat)))
      (mp₁ : EnvModelM V μ (ConLeche.consMutualFormers fms env))
      (ppsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (W : (Name → Nat) → Nat)
      (idxF : Nat → List Expr) (dsF : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (esF : Nat → (Name → Nat) → List AnnotTerm) (srcsF : Nat → List (Option Nat))
      (fvsPF xFvsF : Nat → List Expr) (xrestF : Nat → Expr)
      (eissF : Nat → (Name → Nat) → List (List AnnotTerm))
      (tssF : Nat → (Name → Nat) → List (List (Nat × Nat × AnnotTerm)))
      (dsR : Nat → Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)) (xFvsR : Nat → Nat → List Expr)
      (pinsS : List PinSyn)
      (mp₂ : EnvModelM V μ (ConLeche.consNestedCtors ctorsR.flatten
        (ConLeche.consMutualFormers (fms.take p.k) env))),
      ConLeche.consNestedFormers (stored.take p.k) env
        = ConLeche.consMutualFormers (fms.take p.k) env →
      NestedCoreOut F mp p st b ctorsR fms f₀ ctorsA sortss kinds mp₁ ppsF W idxF dsF esF srcsF
        fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂ →
      Nonempty (EnvModelM V μ envOut)

/-! ## The consumer -/

/-- **The model survives a nested block** (the nested half's run-level
consumer): the run's stages through the restored constructors keep the
model and leave the block model (`NestedCoreModeled`), the tail keeps
it from there (`NestedTailModeled`); the containers' block models are
the pre-block carrier's own (`EnvModelB.blocks`, task #315 M7-3). -/
theorem declNested_of (hμ : μ.verifiedChecks = true) {F : Nat} {env envOut : Env}
    {p : NestedParts} (mp : EnvModelB V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hcore : NestedCoreModeled V μ F) (htail : NestedTailModeled V μ F)
    (h : ConLeche.Semantics.DeclNestedRun μ F env p envOut) :
    Nonempty (EnvModelM V μ envOut) := by
  obtain ⟨h0, h1, st, b, envAux, stored, ctorsR, cvRms, cvRns, rulesM, rulesN, fmsA, ctorsA,
    hfA, hcA, helim, hcount, hfresh, hcont, hb, haux, hstored, hclosed, hpinsAux, hcaps, hsrc,
    -, hgrp, hsc, hK32, hkinds, -, hrank, -, -, hpins₁, hctors, hrm, hrn, -, hrulesM, hrulesN, htbl,
    hpinsOut, hcnt, hrecs, -⟩ := h
  -- the `-` after `hsrc` is K.31's `pinsDistinct` conjunct: named for the
  -- identities' discharge (`NestedPinsIdent`, lane L-B), not consumed here;
  -- `hK32` after `hsc` is K.32's `nestedCopyTargetsOk`, carried down to
  -- `NestedPinsRun` for the same discharge's `ordF` arm (task #315 L-E,
  -- DESIGN §U.64) and not consumed here; the `-` after
  -- `hkinds` is K.35's `nestedAuxAppsOk`, and `hrank` after it is K.37's
  -- `nestedPinRankOk` — the global entry theorem's induction measure,
  -- carried down to `NestedPinsRun` (task #315 L-E, DESIGN §U.55) — the
  -- `-` after THAT is K.40's `nestedPinParentOk` and the one after THAT
  -- K.41's `nestedPinRootPairOk`, neither consumed on this path; the
  -- LAST `-` is K.34's
  -- `blockReadBackOk` — the route's own read-back, which `mp.blocks` already
  -- carries for the environments the fold has stored, so nothing here uses it;
  -- the `-` after `hrn` is K.39's `Nodup` of the restored recursors' names,
  -- which the provision loop's conses need and nothing on this path reads
  -- THE CERTIFICATION-ONLY RECORDS (K.35's follow-up): the run carries them
  -- as `certOnly μ …`; this theorem is stated under `hμ`, at which the gate
  -- is the Bool the consumers below expect
  replace hcont := ConLeche.certOnly_elim hcont hμ
  replace hsrc := ConLeche.certOnly_elim hsrc hμ
  replace hgrp := ConLeche.certOnly_elim hgrp hμ
  replace hsc := ConLeche.certOnly_elim hsc hμ
  replace hK32 := ConLeche.certOnly_elim hK32 hμ
  replace hkinds := ConLeche.certOnly_elim hkinds hμ
  replace hrank := ConLeche.certOnly_elim hrank hμ
  have hPM : PinsModeled mp.base2 st.pins := pinsModeled_of_env mp.blocks hcont
  obtain ⟨fms, f₀, ctorsA', sortss, kinds, mp₁, ppsF, W, idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF,
    eissF, tssF, dsR, xFvsR, pinsS, mp₂, henv, O⟩ := hcore hμ mp.toEnvModelM hE p st b envAux stored
    ctorsR fmsA ctorsA hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux
    hcaps hsrc hgrp hsc hK32 hkinds hrank hpins₁ hctors
  exact htail hμ mp.toEnvModelM hE p envOut st b envAux stored ctorsR cvRms cvRns rulesM rulesN fmsA
    ctorsA hPM h0 h1 hfA hcA helim hcount hfresh hcont hb haux hstored hclosed hpinsAux hcaps hsrc
    hgrp hkinds hctors hrm hrn hrulesM hrulesN htbl hpinsOut hcnt hrecs fms f₀ ctorsA' sortss kinds
    mp₁ ppsF W idxF dsF esF srcsF fvsPF xFvsF xrestF eissF tssF dsR xFvsR pinsS mp₂ henv O

/-! ## The core, modulo the restored constructors' loop -/

/-- **The nested core, modulo the restored constructors' loop**: the
scratch run's formers' stage (`mutualFormersStage` at the `auxRoute`
grade), the prefix stage and the loop (`nestedStageFacts_of`), the
block model at every member (`nestedBlockReps_of`), and the block
model's record (`NestedBlockModelOf`: arities off `auxBlock`, names
off the elimination, pins off the loop's records) — the output packaged
CONCRETELY (`NestedCoreOut`). -/
theorem nestedCoreModeled_of {F : Nat} (hst : NestedCtorsStaged V μ F) :
    NestedCoreModeled V μ F := by
  intro hμ env mp hE p st b envAux stored ctorsR fmsA ctorsA₀ hPM h0 h1 hfA hcA helim hcount hfresh
    hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hpins₁ hctors
  obtain ⟨hnd, hlp, hmem, h3, env₁, fms, f₀, tq₀, ctorsA, sortss, kinds, formers4, ctors4, cvRas,
    rulesOf, hformers, hf₀, htq₀, hcross, -, hctorsA, hkindsA, hfo, -, -, -, -⟩ :=
    ConLeche.checkMutualCore_inv haux
  obtain ⟨-, rfl⟩ := ConLeche.mutualFormers_inv hformers
  obtain ⟨mp₁, ppsF, W, idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF, eissF, tssF, h⟩ :=
    mutualFormersStage hμ mp hE b hnd hlp hmem hformers hf₀ htq₀ hcross hctorsA hkindsA hfo
  have hbk : b.k = p.k + st.pins.length := ConLeche.auxBlock_k_count hfA helim hb
  obtain ⟨henv, -⟩ := ConLeche.consNestedFormers_take_eq haux hformers hstored p.k (by omega)
  rw [henv] at hctors hpins₁
  obtain ⟨mp₂, dsR, xFvsR, pinsS, S⟩ := nestedStageFacts_of hst hμ hE hPM h0 h1 hfA hcA helim hcount
    hfresh hcont hb haux hstored hclosed hpinsAux hcaps hsrc hgrp hsc hK32 hkinds hrank hpins₁ hnd h3
    hformers hctorsA h hbk hctors
  have hbk' : b.k = p.k + pinsS.length := by rw [hbk, S.pinsLen]
  obtain ⟨hreps, htyped⟩ := nestedBlockReps_of hμ h h3 hbk' mp₂ S.findM S.leafM S.FD S.ctorsLen
    S.ctorFacts S.domFacts S.groups
  refine ⟨fms, f₀, ctorsA, sortss, kinds, mp₁, ppsF, W, idxF, dsF, esF, srcsF, fvsPF, xFvsF, xrestF,
    eissF, tssF, dsR, xFvsR, pinsS, mp₂, henv, ?_⟩
  exact
    { formers := hformers
      facts := h
      ctors := hctorsA
      kindsRun := hkindsA
      bk := hbk'
      grouped := h3
      nodup := hnd
      stage := S
      reps := hreps
      typed := htyped
      record :=
        { k := rfl
          nP := (ConLeche.auxBlock_fields hb).1
          env₀ := rfl
          memberNames := S.names
          large := (ConLeche.auxBlock_fields hb).2.2.1
          nPins := S.pinsLen
          pin := S.pinRec
          ctors := fun _ _ => rfl } }

end ConLeche.Model
