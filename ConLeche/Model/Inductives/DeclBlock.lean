module

public import ConLeche.Model.Inductives.DeclNative
public import ConLeche.Model.Inductives.BlockDatum
import ConLeche.Model.Inductives.BlockPosRun
import ConLeche.Model.Inductives.BlockModelRecords
import ConLeche.Model.Inductives.BlockHoleGrade
import ConLeche.Model.Annot.BlockLfpMono
import ConLeche.Model.Annot.BlockLfpTup
import ConLeche.Model.Inductives.BlockCtorReads
import ConLeche.Model.Inductives.BlockCover
import ConLeche.Model.Inductives.BlockStageRec
public import ConLeche.Semantics.Inductives.DeclBlock
import ConLeche.Verify.Inductives.BlockPartsInv
import ConLeche.Semantics.Inductives.DeclBlockEta
public import ConLeche.Verify.Inductives.RecStage
public section

/-!
# The uniform block install, assembled (task #315 M3)

`declBlock`: **the P carrier survives the UNIFORM install's run at `k`
members.**  This is the Model tier's half of the milestone-M1 flip
stated over the uniform installer itself (`checkBlock`) — the shape
`Model/Fold.lean`'s dispatch will take once the route is ungated.

`declBlock` covers `k = 1` like every other width; the fold reaches it
through `declBlock_run` (`Model/Inductives/BlockDeclRun.lean`).

**What is NOT here**: `declBlock` for all `k`, and the named fact
`BlockRecStaged` its recursor stage would carry.  Both wait on the
stage theorems (the k-former loop, the constructors' loop over
members, the tables per structure-like member); writing the named fact
before its stage shapes are fixed would be a hypothesis without a
run-level consumer.  What exists of the stage chain today is listed in
`_tmp/uniform-inds/M3-REPORT.md` §3.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal RecFieldKind IndCaps
  BlockShape BlockParts MemberShape BinderMeta RecRule)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## `NoProjEnv` across the block's conses -/

/-- The `k` formers' cons keeps a member's slots free: a former's type
resolves before the block, and an `indInfo` carries nothing else. -/
theorem noProjEnv_consBlockInds {T : Name} {i : Nat} {p₁ : ConLeche.BlockShape} {isRec : Bool} :
    ∀ {cvTas : List ConstantVal} {j : Nat} {env₀ : Env},
      NoProjEnv env₀ T i → (∀ cvTa ∈ cvTas, Expr.NoProjAt T i cvTa.type) →
      NoProjEnv (ConLeche.consBlockInds p₁ isRec cvTas j env₀) T i
  | [], _, _, h, _ => h
  | cvTa :: rest, j, env₀, h, hall => by
    simp only [ConLeche.consBlockInds]
    refine noProjEnv_consBlockInds
      (h.cons (c₀ := .indInfo cvTa (ConLeche.blockCapsAt p₁ j isRec)) (NoProjHead.ofType
        (hall cvTa List.mem_cons_self) (fun _ _ _ h => nomatch h)
        (fun _ _ _ _ h => nomatch h) (fun _ h => nomatch h))) ?_
    exact fun c hc => hall c (List.mem_cons_of_mem _ hc)

/-- The members' constructors' conses keep a member's slots free. -/
theorem noProjEnv_consBlockCtors {T : Name} {i nP : Nat} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env₀ : Env},
      NoProjEnv env₀ T i →
      (∀ ctorsA ∈ ctorsAs, ∀ cA ∈ ctorsA, Expr.NoProjAt T i cA.1.type) →
      NoProjEnv (ConLeche.consBlockCtors nP ctorsAs env₀) T i
  | [], _, h, _ => h
  | ctorsA :: rest, env₀, h, hall => by
    simp only [ConLeche.consBlockCtors]
    refine noProjEnv_consBlockCtors
      (noProjEnv_consSumCtors h (hall ctorsA List.mem_cons_self)) ?_
    exact fun l hl => hall l (List.mem_cons_of_mem _ hl)

/-- A name absent above the constructors' conses was absent below them. -/
theorem find?_none_consBlockCtors {nP : Nat} {n : Name} :
    ∀ {ctorsAs : List (List (ConstantVal × Nat))} {env₀ : Env},
      (ConLeche.consBlockCtors nP ctorsAs env₀).find? n = none → env₀.find? n = none
  | [], _, h => h
  | _ :: rest, _env₀, h =>
    ConLeche.consSumCtors_find?_none (find?_none_consBlockCtors (ctorsAs := rest) h)


/-! ## The recursor stage's own constructor list, positionally

A stored recursor's fourth component IS one of the constructors'
stage's lists (`RecStage.ctorsAt`): the fact that turns the
constructors' stage's STORAGE into the recursor lane's `hctorsIn`. -/

section RecCtors

/-- The recursor stage, at the same fact: every stored recursor's
constructor list is a constructors'-stage list, at its member's index. -/
theorem recStage_ctorsIdx {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
    {ctorsAs : List (List (ConstantVal × Nat))}
    {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {F : Nat}
    (h : ConLeche.RecStageOk μ F envC pp cvTas ctorsAs rs) :
    ∀ r ∈ rs, ∃ c : Nat, ctorsAs[c]? = some r.2.2.2 := by
  obtain ⟨R⟩ := id h
  intro r hr
  obtain ⟨i, hi⟩ := List.getElem?_of_mem hr
  obtain ⟨-, -, hct, -⟩ := R.ctorsAt i r trivial hi
  exact ⟨_, hct⟩

end RecCtors

/-! ## The recursor stage's obligation -/

/-- **What the recursors' stage owes the tables' stage** (milestone
M5's conjunct ⑧, which `DeclBlockRun` deliberately leaves opaque): a
carrier at the post-recursor environment that
* reads every name the pre-recursor environment stores as that
  environment's carrier does (`acval` agreement),
* finds everything it found (`find?` monotonicity),
* reads every pre-recursor-bounded expression the same way
  (`denoteMeta` stability — the constructors' and formers' TYPE
  readings cross the conses), and
* keeps every member's projection slots free (`NoProjEnv`
  preservation — the generated recursor types and rule right-hand
  sides carry no projection of a member; at ONE member this is
  `Expr.NoProjAt.structRecTyR`/`structRecRhsR`).

It is four cons-monotonicities and mentions no `BlockData`: the
recursor lane proves it once, and `declBlock` consumes it. -/
@[expose] def BlockRecStagedAt (μ : CheckMode) {V : Type w} [SetTheory V]
    (envC env₃ : Env) (mpC : EnvModelM V μ envC) : Prop :=
  ∃ mp' : EnvModelM V μ env₃,
    (∀ n : Name, (envC.find? n).isSome = true → mp'.base2.acval n = mpC.base2.acval n) ∧
    (∀ (n : Name) (c : ConstantInfo), envC.find? n = some c → env₃.find? n = some c) ∧
    (∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denoteMeta mp'.base2.acval env₃ ψ dd e = denoteMeta mpC.base2.acval envC ψ dd e) ∧
    (∀ (T : Name) (i : Nat), envC.findProj? T i = none → NoProjEnv envC T i →
      NoProjEnv env₃ T i)

/-- `BlockRecStagedAt` at the switch-off route's cons (`consBlockRecs`). -/
@[expose] def BlockRecStaged (μ : CheckMode) {V : Type w} [SetTheory V]
    (envC : Env) (p : ConLeche.BlockShape) (nP : Nat)
    (rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
    (mpC : EnvModelM V μ envC) : Prop :=
  BlockRecStagedAt μ envC (ConLeche.consBlockRecs envC.find? p nP 0 rs envC) mpC

/-- **The tables' invariant crosses the recursors' conses**, by the
four facts of `BlockRecStaged` and nothing else. -/
theorem BlockTablesCore.consRecs {envC envR : Env} {mC : EnvModel V envC} {mR : EnvModel V envR}
    {d : BlockData V} {lps : List Name} {cvTasAll : List ConstantVal} {p₁ : ConLeche.BlockShape}
    {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
    (h : BlockTablesCore mC d lps cvTasAll p₁ isRec A 0)
    (hag : ∀ n : Name, (envC.find? n).isSome = true → mR.acval n = mC.acval n)
    (hfind : ∀ (n : Name) (c : ConstantInfo), envC.find? n = some c → envR.find? n = some c)
    (hden : ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr), ConstsBound envC e →
      denoteMeta mR.acval envR ψ dd e = denoteMeta mC.acval envC ψ dd e)
    (hnp : ∀ (T : Name) (i : Nat), envC.findProj? T i = none →
      NoProjEnv envC T i → NoProjEnv envR T i)
    (hslot : ∀ c, c < d.k → (∃ cA, d.ctorsM c = [cA]) → d.nIdxAt c = 0 →
      ∀ j, envC.findProj? (d.memberName c) j = none) :
    BlockTablesCore mR d lps cvTasAll p₁ isRec A 0 := by
  obtain ⟨hform, hctor, hnpC⟩ := h
  have hsome : ∀ n : Name, (envC.find? n).isSome = true → (envR.find? n).isSome = true := by
    intro n hn
    cases hc : envC.find? n with
    | none => rw [hc] at hn; exact nomatch hn
    | some c => rw [hfind n c hc]; rfl
  refine ⟨fun c cvTb hc => ?_, fun c j cA hj => ?_,
    fun c hc hck h1 h2 j => hnp _ _ (hslot c hck h1 h2 j) (hnpC c hc hck h1 h2 j)⟩
  · obtain ⟨hfindT, hres, hleaf, hFD⟩ := hform c cvTb hc
    refine ⟨hfind _ _ hfindT, Expr.constsResolve_of_find hsome hres, fun ψ => ?_, ?_⟩
    · rw [hag cvTb.name (by rw [hfindT]; rfl)]; exact hleaf ψ
    · exact ⟨fun ψ => by
        rw [hden ψ 0 cvTb.type (constsBound_of_constsResolve _ hres)]; exact hFD.read ψ,
      hFD.len, hFD.bits, hFD.okTy, hFD.below, hFD.params⟩
  · obtain ⟨hfindC, hlps, hres, hread, hleaf⟩ := hctor c j cA hj
    refine ⟨hfind _ _ hfindC, hlps, Expr.constsResolve_of_find hsome hres, fun ψ => ?_,
      fun ψ => ?_⟩
    · rw [hden ψ 0 cA.1.type (constsBound_of_constsResolve _ hres)]; exact hread ψ
    · rw [hag cA.1.name (by rw [hfindC]; rfl)]; exact hleaf ψ

/-! ## The stages the block step reads, as premises at either switch

The uniform block step (`declBlock_gen`) is written once for both
positions of the route switch (`nst`).  What differs between them is
exactly two producers: the constructors' stage with the operator's
monotonicity (`BlockCtorStageAt`: `blockTablesStage_of` and
`blockCtorPos_of_run` with the switch off, `blockCtorStageAt_flat`) and
the recursor stage (`BlockRecStagedT`, from the stage's own run).  With
the switch on they are the nested lanes' (`declBlock_nested`,
`DeclBlockNested.lean`). -/

/-- **The constructors' stage, as the block step reads it** (lane
NESTKERN): at every run of the formers', the constructors' and the
positivity stage (at the route switch `nst`), the block's representation
record with the formers' carrier (`blockTablesStage_of`'s conclusion)
and every member constructor positive along the tuple order at the hole
frame (`blockCtorPos_of_run`'s, given the stored constructors' closure). -/
@[expose] def BlockCtorStageAt (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) {env : Env}
    (mp : EnvModelM V μ env) (nst : Bool) : Prop :=
  ∀ {envI : Env} {p₀ : BlockParts} {isRec : Bool} {cvTas : List ConstantVal} {q : BlockShape}
    {ctorsAs : List (List (ConstantVal × Nat))} {sortsss : List (List (List Level))}
    {isorts : List (List Level)}
    (_hE : ConLeche.EtaFamiliesClosed env)
    (_hlps₀ : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps)
    (_hndM : q.memberNames.Nodup)
    (_hndC : (q.allCtors.map (·.1.name)).Nodup)
    (_hClps : ∀ c ∈ q.allCtors, c.1.levelParams = q.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false)
    (_hInd : ConLeche.checkBlockInds (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) env p₀ isRec
      = .ok (envI, cvTas, q))
    (_hCtors : ConLeche.checkBlockCtors (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI envI q
      (q.members.zip cvTas) = .ok (ctorsAs, sortsss))
    (_hsorts : ConLeche.checkBlockIdxSorts (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI q
      (q.members.zip cvTas) = .ok isorts)
    -- the positivity stage (`DeclBlockRun` 7b): U2 grades the fields with holes
    {pP : BlockParts}
    {posKs : List (List (List ConLeche.NestFieldKind)) × List (List Expr) × ConLeche.NestNodes}
    (_hPos : ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pP cvTas ctorsAs nst = .ok posKs)
    (_hpN : pP.memberNames = q.memberNames) (_hpL : pP.lps = q.lps) (_hpP : pP.nP = q.nP)
    (_hpI : pP.nIdxs = q.nIdxs) (_hpR : pP.resSort = q.resSort)
    (_hfamFree : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < q.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (q.members.getD m default).nIdx = 0 → 0 < cA.2 →
      envI.find? (projFnName (q.memberNames.getD m .anonymous) 0) = none)
    (_hprojTbl : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < q.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (q.members.getD m default).nIdx = 0 →
      envI.find? (projTableName (q.memberNames.getD m .anonymous)) = none),
    ∃ (pk : Nat → BlockMemberPick) (uOf : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm))
      (mpI : EnvModelM V μ envI),
      BlockNamesOk (V := V) (blockDataOf V q ctorsAs pk uOf ppsOf) cvTas ∧
      BlockTablesStage (V := V) μ F (blockDataOf V q ctorsAs pk uOf ppsOf) q.lps cvTas
        q isRec (blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf)) envI
        q.ctorNamesAt (fun m => (sortsss.getD m []).getD 0 []) ∧
      BlockCtorsCore mpI.base2 (blockDataOf V q ctorsAs pk uOf ppsOf) q.lps cvTas
        q isRec (blockLeafH (blockDataOf V q ctorsAs pk uOf ppsOf)) 0 ∧
      ConLeche.BlockEtaInv envI q.memberNames q.ctorNamesAt ∧
      (∀ (c j : Nat) (cA : ConstantVal × Nat),
        ((blockDataOf V q ctorsAs pk uOf ppsOf).ctorsM c)[j]? = some cA →
        envI.find? cA.1.name = none) ∧
      (∀ (c j : Nat) (cA : ConstantVal × Nat),
        ((blockDataOf V q ctorsAs pk uOf ppsOf).ctorsM c)[j]? = some cA →
        (blockDataOf V q ctorsAs pk uOf ppsOf).nfFF c j = (posKs.2.1.getD c []).getD j default) ∧
      -- every name off the block keeps its leaf (lane COVERB)
      (∀ n : Name, (∀ cvTb ∈ cvTas, n ≠ cvTb.name) → mpI.base2.acval n = mp.base2.acval n) ∧
      -- the operator's MONOTONICITY is positivity's: every constructor positive
      -- along the tuple order at the hole frame (at the formers' carrier)
      ((∀ (c j : Nat) (cA : ConstantVal × Nat),
          ((blockDataOf V q ctorsAs pk uOf ppsOf).ctorsM c)[j]? = some cA →
          cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true) →
        ∀ (ψ : Name → Nat) (ρp : Nat → V),
          Sat V ((blockDataOf V q ctorsAs pk uOf ppsOf).params ψ).reverse ρp →
          ∀ c, c < (blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.N → ∀ j,
            j < (blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.nctors c →
            (blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.CtorPos
              ((blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.tupRel ψ ρp) ψ c j) ∧
      -- the fields with holes are small at a `Type`-valued block (U2's grading;
      -- recorded in the clause, `LfpClause.fieldsOk`, lane ACCMODEL)
      ((∀ (c j : Nat) (cA : ConstantVal × Nat),
          ((blockDataOf V q ctorsAs pk uOf ppsOf).ctorsM c)[j]? = some cA →
          cA.1.type.hasFvar = false ∧ cA.1.type.looseBVarsBounded 0 = true) →
        ∀ (ψ : Name → Nat) (ρp : Nat → V),
          Sat V ((blockDataOf V q ctorsAs pk uOf ppsOf).params ψ).reverse ρp →
          (blockDataOf V q ctorsAs pk uOf ppsOf).w ψ ≠ 0 →
          ∀ X, InTupleSpace ((blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.w ψ)
            (blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.N
            ((blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.idx ψ ρp) X →
          ∀ c, c < (blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.N → ∀ j,
            j < (blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.nctors c →
            FieldsOkB ((blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.w ψ)
              ((blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.frame ψ ρp X)
              ((blockDataOf V q ctorsAs pk uOf ppsOf).toLfp.fields ψ c j))

/-- **The recursors' stage's obligation at the cons at the majors** (lane
NESTKERN): `BlockRecStaged`'s four cons-monotonicities at
`consBlockRecsT`, the family consed with each recursor's rules at ITS
major (`.nested` at an outside one). -/
@[expose] def BlockRecStagedT (μ : CheckMode) {V : Type w} [SetTheory V]
    (envC : Env) (p : ConLeche.BlockShape)
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) : Prop :=
  BlockRecStagedAt μ envC
    (ConLeche.consBlockRecsT envC.find? (·.constsResolve envC) p 0 out envC) mpC

/-- **The constructors' stage with the switch off**, from the stage
theorems: `blockTablesStage_of` and `blockCtorPos_of_run` (the walk's
kinds are flat). -/
theorem blockCtorStageAt_flat (hμ : μ.verifiedChecks = true) {F : Nat} {env : Env}
    (mp : EnvModelM V μ env) : BlockCtorStageAt V μ F mp false := by
  intro envI p₀ isRec cvTas q ctorsAs sortsss isorts hE hlps₀ hndM hndC hClps hInd hCtors hsorts
    pP posKs hPos hpN hpL hpP hpI hpR hfamFree hprojTbl
  obtain ⟨pk, uOf, ppsOf, mpI, hN, hS, hcore, hEtaI, hfreshC, hnfs, hagI⟩ :=
    blockTablesStage_of hμ mp hE hlps₀ hndM hndC hClps hInd hCtors hsorts
      hPos hpN hpL hpP hpI hpR hfamFree hprojTbl
  have hlenCA : ctorsAs.length = q.k := by
    obtain ⟨ppsOf₀, sOf₀, hF⟩ := blockFormerFacts_of hμ mp hInd hlps₀
    obtain ⟨hl, -, -⟩ := ConLeche.checkBlockCtors_inv hCtors
    rw [hl, List.length_zip, hF.lenCv]
    exact Nat.min_self _
  refine ⟨pk, uOf, ppsOf, mpI, hN, hS, hcore, hEtaI, hfreshC, hnfs, hagI, fun hclosed => ?_, ?_⟩
  · exact blockCtorPos_of_run hμ mpI hN hcore.holeCtx hPos hpN hpL hpP hpI
      (by simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
        ConLeche.BlockShape.memberNames])
      rfl hlenCA (fun c hc => by
        show ctorsAs[c]? = some (ctorsAs.getD c [])
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenCA]; exact hc)]
        rfl) hclosed hnfs
  · intro hclosed ψ ρp hs _ X hX c hc j hj
    exact ((blockHoleGrade_of_run hμ mpI hN hcore.holeCtx hPos hpN hpL hpP hpI hpR
      (by simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
        ConLeche.BlockShape.memberNames])
      rfl (fun c hc => by
        show ctorsAs[c]? = some (ctorsAs.getD c [])
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenCA]; exact hc)]
        rfl) hlenCA hclosed hnfs ψ hc hj).2 ρp hs X hX).1

/-- **The constructors' stage with the switch ON** (lane NESTKERN, session
2): the stage theorems at the switch (`blockTablesStage_of_gen`,
`blockCtorPos_of_run_gen`), under the input's coverage — the walk's
container case reads the containers' clauses (`ContCover` at the formers'
carrier, `lfpCover_formers`) and threads its cache invariant — given (W)
for the nested hole operator (`NestedAccOwed`, lane ACCMODEL). -/
theorem blockCtorStageAt_nested (hμ : μ.verifiedChecks = true) {F : Nat} {env : Env}
    (mp : EnvModelM V μ env) (hW : NestedAccOwed V μ F) :
    LfpCover mp [] → BlockCtorStageAt V μ F mp true := by
  intro hcov envI p₀ isRec cvTas q ctorsAs sortsss isorts hE hlps₀ hndM hndC hClps hInd hCtors
    hsorts pP posKs hPos hpN hpL hpP hpI hpR hfamFree hprojTbl
  obtain ⟨pk, uOf, ppsOf, mpI, hN, hS, hcore, hEtaI, hfreshC, hnfs, hagI⟩ :=
    blockTablesStage_of_gen hμ mp hE hlps₀ hndM hndC hClps hInd hCtors hsorts
      hPos hpN hpL hpP hpI hpR hfamFree hprojTbl (fun _ => hcov) (fun _ => hW)
  obtain ⟨ppsOf₀, sOf₀, hF⟩ := blockFormerFacts_of hμ mp hInd hlps₀
  obtain ⟨-, -, -, -, -, -, -, -, hcons, -, -, -⟩ := ConLeche.checkBlockInds_shape hInd
  have hlenCA : ctorsAs.length = q.k := by
    obtain ⟨hl, -, -⟩ := ConLeche.checkBlockCtors_inv hCtors
    rw [hl, List.length_zip, hF.lenCv]
    exact Nat.min_self _
  have hlenN : q.memberNames.length = q.k := by
    show (q.members.map _).length = _; simp; rfl
  -- coverage at the formers' carrier, the members exempt
  have hcovI : ∃ mk : EnvModelM V μ envI, mk.base2 = mpI.base2 ∧ LfpCover mk pP.memberNames := by
    refine (lfpCover_formers mp hcons mpI (fun cvTb hcvTb => ?_) hagI (fun cvTb hcvTb => ?_)
      (fun n hn => ?_) hcov).imp fun _ h => ⟨h.1, h.2.2⟩
    · obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      exact hF.freshOf t cvTb ht
    · obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      have htk : t < q.k := by
        have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hF.lenCv] at this
      rw [hF.nameOf t cvTb ht, hpN]
      exact getD_mem _ (by rw [hlenN]; exact htk)
    · rw [hpN] at hn
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hn
      have htk : t < q.k := by
        have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hlenN] at this
      obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[t]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact htk)⟩
      have hname := hF.nameOf t cvTb hcv
      rw [List.getD_eq_getElem?_getD, ht] at hname
      rw [← show cvTb.name = n from hname]
      exact hF.freshOf t cvTb hcv
  refine ⟨pk, uOf, ppsOf, mpI, hN, hS, hcore, hEtaI, hfreshC, hnfs, hagI, fun hclosed => ?_, ?_⟩
  · exact blockCtorPos_of_run_gen hμ mpI hN hcore.holeCtx hPos hpN hpL hpP hpI
      (by simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
        ConLeche.BlockShape.memberNames])
      rfl hlenCA (fun c hc => by
        show ctorsAs[c]? = some (ctorsAs.getD c [])
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenCA]; exact hc)]
        rfl) hclosed hnfs (fun _ => hcovI)
  · intro hclosed ψ ρp hs _ X hX c hc j hj
    exact ((blockHoleGrade_of_run hμ mpI hN hcore.holeCtx hPos hpN hpL hpP hpI hpR
      (by simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
        ConLeche.BlockShape.memberNames])
      rfl (fun c hc => by
        show ctorsAs[c]? = some (ctorsAs.getD c [])
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by rw [hlenCA]; exact hc)]
        rfl) hlenCA hclosed hnfs ψ hc hj).2 ρp hs X hX).1

/-- **The block over an older environment** (lane NESTIND, session 16: the
(D) bridge's `hXfix`): a well-formed environment `env₀` in which no member
name is stored, and in which every constant of `envC` was stored already
unless it is a former or a constructor concluding in a member.  A
container's constructor (it concludes in its own, non-member inductive)
therefore resolves in `env₀` and names no member. -/
@[expose] def BlockOverEnv (envC : Env) (names : List Name) : Prop :=
  ∃ env₀ : Env, ConLeche.EnvWF env₀ ∧ (∀ n ∈ names, env₀.find? n = none) ∧
    ∀ n ci, envC.find? n = some ci → env₀.find? n = some ci ∨
      (∃ cv caps, ci = .indInfo cv caps) ∨
      ∃ cv nP nF bs body us m, ci = .ctorInfo cv nP nF ∧
        cv.type.stripPis (nP + nF) = some (bs, body) ∧ body.getAppFn = .const m us ∧ m ∈ names

/-- **The positivity model at the formers' environment** (lane NESTIND,
session 19): a carrier at `envI` covering every recorded block but the
block's own members (`names`), whose recorded blocks are among `mpC`'s and
whose leaves are `mpC`'s at every name stored at `envI` — the model the
positivity derivation's monotonicity (`frame_mono`, at the derivation's
environment `envI`) reads, tied to the recursor stage's carrier.  Every
block `mpC` records is `mk`'s or the block's own `D0` (session 20:
`FrameMono` asks a container's block in `mk.lfpBlocks`, `lfpSel` selects
from `mpC.lfpBlocks`). -/
@[expose] def FormersModelAt (envI : Env) (names : List Name) {envC : Env}
    (mpC : EnvModelM V μ envC) (d : BlockData V) (lps : List Name) (cvTas : List ConstantVal)
    (p : BlockShape) (isRec : Bool) : Prop :=
  ∃ mk : EnvModelM V μ envI, LfpCover mk names ∧ (∀ D ∈ mk.lfpBlocks, D ∈ mpC.lfpBlocks) ∧
    (∀ n, (envI.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n) ∧
    (∀ D ∈ mpC.lfpBlocks, D = d.toLfp ∨ D ∈ mk.lfpBlocks) ∧
    -- the member constructors' hole contexts at the formers' model (lane
    -- NESTIND, session 23: the node-semantics induction's root)
    BlockHoleCtxFacts mk.base2 d lps cvTas p isRec ∧
    -- a reading at the formers' environment is one at the constructors'
    ∀ (ψ : Name → Nat) (dd : Nat) (e : Expr) {ea : AnnotTerm},
      denoteMeta mk.base2.acval envI ψ dd e = some ea → denoteMeta mpC.base2.acval envC ψ dd e = some ea

/-- **The uniform block step at either position of the route switch**
(lane NESTKERN): the P carrier survives the uniform install's run at `k`
members, given the constructors' stage (`hstage`) and the recursors'
stage (`hrecT`) as producers — `declBlock` supplies both with the switch
off, `declBlock_nested` names them with the switch on.  Everything else
is read off the run: the formers' and the constructors' conses, the
block's lfp clause and its record, coverage (lane COVERB), the tables.

The run's nine conjuncts, one stage at a time: the formers' and the
constructors' stages are `hstage`'s (conjuncts ①②③⑥⑦,
with the two freshness facts of conjunct ⑨ supplied here), the
constructors are consed by `stageBlockCtors` (conjunct ②'s install
half), the recursors' stage is the named `BlockRecStagedT` (conjunct
⑧), and the tables are `stageBlockTables` (conjunct ⑨).  The
invariant that crosses all of it is `BlockCtorsCore` → (at the
recursors) `BlockTablesCore`. -/
theorem declBlock_gen (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts} {nst : Bool}
    (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂ nst)
    -- the constructors' stage and the operator's monotonicity (switch off:
    -- `blockCtorStageAt_flat`)
    (hstage : BlockCtorStageAt V μ F mp nst)
    -- the recursors' stage, from its own run (switch off: `declBlock`'s `hrec`)
    (hrecT : ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
        (ctorsAsR : List (List (ConstantVal × Nat)))
        (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
        (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
        (A : Nat → (Name → Nat) → AnnotTerm)
        (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)) (nodesR : ConLeche.NestNodes),
        -- the recursor stage's own run (the target check at the switch, then —
        -- where every kind is flat — the reject-only conformance check)
        ConLeche.checkBlockRec (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp nst
          (nst && ConLeche.blockNestedBit pp.toBlockShape kindsR)
          (ConLeche.nestKindsFlat kindsR) nodesR block cvTasR ctorsAsR
          (ConLeche.blockNormalCtors pp.toBlockShape ctorsAsR nfsR) = .ok out →
        -- the block's POSITIVITY run, whose kinds and normal forms the
        -- recursor stage reads (route A, maintainer 2026-09-25: the
        -- recursor stage may read it — lane NESTIND), at the formers'
        -- environment `envI`, whose constructors' cons is `envC`
        ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
          envI.find? envI.consts pp cvTasR ctorsAsR nst = .ok (kindsR, nfsR, nodesR) →
        envC = ConLeche.consBlockCtors pp.nP ctorsAsR envI →
        -- the stored constructors are the recogniser's, one for one
        ctorsAsR.map (·.map (fun cA => (cA.1.name, cA.2)))
          = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) →
        -- the recogniser's member names
        pp.toBlockShape.memberNames.Nodup →
        -- the block's REPRESENTATION at the constructors' environment,
        -- in the three records `blockModelAt_of_stages` consumes
        BlockNamesOk (V := V) dR cvTasR →
        BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A envI
          pp.ctorNamesAt →
        BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k →
        (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) →
        -- the block's REPRESENTATION is the run's own record
        (∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
            (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
          dR = blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf) →
        -- the block's LFP CLAUSE is recorded in the carrier
        dR.toLfp ∈ mpC.lfpBlocks →
        -- the carrier is covered where the input is (lane COVERB): an outside
        -- major's clause is recorded
        (LfpCover mp [] → LfpCover mpC []) →
        -- the positivity model at the formers' environment (lane NESTIND,
        -- session 19: the derivation's monotonicity reads it)
        (LfpCover mp [] → FormersModelAt (V := V) envI pp.toBlockShape.memberNames mpC dR pp.lps
          cvTasR pp.toBlockShape isRecR) →
        -- the block over the input environment: its names fresh there, every
        -- other constant stored there already (lane NESTIND, `hXfix`)
        BlockOverEnv envC pp.toBlockShape.memberNames →
        BlockRecStagedT (V := V) μ envC pp.toBlockShape out mpC) :
    CoverStep mp env₂ := by
  classical
  obtain ⟨hndC₀, hndM₀, isRec, env₁, cvTas, p₁, p, ctorsAs, sortsss, kinds, nfs, nodes, isorts, outR,
    hInd, hp, hCtors, hPos, -, -, hsorts, hRec, hTbl⟩ := hrun
  subst hp
  -- ## the recogniser's facts, moved to the shape the formers' stage completed
  obtain ⟨hshape, -⟩ := ConLeche.blockParts?_inv hdp
  obtain ⟨-, -, -, hmembersOk, -, hClps₀, -, -, -⟩ := ConLeche.blockShape?_inv hshape
  obtain ⟨ms0, mrest, cvTa0, s0, cvs, hmem0, hcvTas, hq, hcons, htele0, -, -⟩ :=
    ConLeche.checkBlockInds_shape hInd
  have hlps₀ : ∀ ms ∈ p₀.members, ms.cvT.levelParams = p₀.lps :=
    fun ms hms => (hmembersOk ms hms).1
  have hndM : p₁.memberNames.Nodup := by rw [hq]; exact hndM₀
  have hndC : (p₁.allCtors.map (·.1.name)).Nodup := by rw [hq]; exact hndC₀
  have hClps : ∀ c ∈ p₁.allCtors, c.1.levelParams = p₁.lps ∧
      ConLeche.reservedBasisNames.contains c.1.name = false := by rw [hq]; exact hClps₀
  -- ## the formers' and the constructors' run, read positionally
  obtain ⟨ppsOf₀, sOf₀, hF⟩ := blockFormerFacts_of hμ mp hInd hlps₀
  obtain ⟨hlenCA, hlenSA, -⟩ := ConLeche.checkBlockCtors_inv hCtors
  have hkm : p₁.k = p₁.members.length := rfl
  have hlenCtorsAs : ctorsAs.length = p₁.k := by
    rw [hlenCA, List.length_zip, hF.lenCv, hkm]
    exact Nat.min_self _
  have hlenSortsss : sortsss.length = p₁.k := by
    rw [hlenSA, List.length_zip, hF.lenCv, hkm]
    exact Nat.min_self _
  -- ## the recursor stage IS the uniform check (the switch off: every major
  -- a member), read through the conformance check after it; the cons at
  -- the majors is the member cons of its stored family
  have hnames : ctorsAs.map (·.map (fun cA => (cA.1.name, cA.2)))
      = p₁.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) := by
    have hz : (p₁.members.zip cvTas).map Prod.fst = p₁.members :=
      List.map_fst_zip (Nat.le_of_eq (by rw [hF.lenCv]; rfl))
    rw [(ConLeche.Semantics.checkBlockCtors_names hCtors).1, ← hz, List.map_map]
    rfl
  have hmemCtors : ∀ (m : Nat), m < p₁.k →
      ∀ c ∈ (p₁.members.getD m default).ctors, c ∈ p₁.allCtors := by
    intro m hm c hc
    rw [ConLeche.BlockShape.allCtors, List.mem_flatten]
    refine ⟨_, List.mem_map.mpr ⟨_, ?_, rfl⟩, hc⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
    exact List.getElem_mem _
  have hfacts := fun (m : Nat) (cvTa : ConstantVal) (hm : m < p₁.k)
      (hcv : cvTas[m]? = some cvTa) =>
    blockCtorFacts_of (blockCtorRuns_of hCtors hF.nameOf m cvTa hm hcv)
      (fun c hc => hClps c (hmemCtors m hm c hc))
  -- ## the member name, read off the member list
  have hmnameEq : ∀ (m : Nat), m < p₁.k →
      p₁.memberNames.getD m .anonymous = (p₁.members.getD m default).cvT.name := by
    intro m hm
    rw [ConLeche.BlockShape.memberNames, List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_getElem (show m < p₁.members.length from hm),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
    rfl
  -- ## the tables' loop's entries, positionally
  have hzipEntry : ∀ (m : Nat), m < p₁.k →
      (p₁.members.zip (ctorsAs.zip sortsss))[m]?
        = some (p₁.members.getD m default, ctorsAs.getD m [], sortsss.getD m []) := by
    intro m hm
    have hc1 : ctorsAs[m]? = some (ctorsAs.getD m []) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenCtorsAs]; exact hm)]
      rfl
    have hs1 : sortsss[m]? = some (sortsss.getD m []) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (by rw [hlenSortsss]; exact hm)]
      rfl
    have hm1 : p₁.members[m]? = some (p₁.members.getD m default) := by
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (show m < p₁.members.length from hm)]
      rfl
    rw [List.getElem?_zip_eq_some]
    exact ⟨hm1, by rw [List.getElem?_zip_eq_some]; exact ⟨hc1, hs1⟩⟩
  -- ## conjunct ⑨'s two freshness facts, pulled back to the formers'
  -- environment (a name absent above a cons was absent below it)
  have hpull : ∀ n : Name,
      (ConLeche.consBlockRecsT (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        (·.constsResolve (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)) p₁ 0 outR
        (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)).find? n = none → env₁.find? n = none :=
    fun n h => find?_none_consBlockCtors (find?_none_consBlockRecsT h)
  have hfamFree : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < p₁.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (p₁.members.getD m default).nIdx = 0 → 0 < cA.2 →
      env₁.find? (projFnName (p₁.memberNames.getD m .anonymous) 0) = none := by
    intro m cA sorts hm hcA hs hn0 hpos
    rw [hmnameEq m hm]
    exact hpull _ (blockTablesFamFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
      hTbl m _ (hzipEntry m hm) cA sorts hcA hs hn0 hpos)
  have hprojTbl : ∀ (m : Nat) (cA : ConstantVal × Nat) (sorts : List Level), m < p₁.k →
      ctorsAs.getD m [] = [cA] → sortsss.getD m [] = [sorts] →
      (p₁.members.getD m default).nIdx = 0 →
      env₁.find? (projTableName (p₁.memberNames.getD m .anonymous)) = none := by
    intro m cA sorts hm hcA hs hn0
    rw [hmnameEq m hm]
    exact hpull _ (blockTablesTblFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
      hTbl m _ (hzipEntry m hm) cA sorts hcA hs hn0)
  -- ## the recursor stage IS the uniform check, read through the
  -- conformance check after it (`checkBlockRecK_of_rec`)
  -- ## the formers' and the constructors' stage
  obtain ⟨pk, uOf, ppsOf, mpI, hN, hS, hcore, hEtaI, hfreshC, hnfs, hagI, hposI, hfokI⟩ :=
    hstage hE hlps₀ hndM hndC hClps hInd hCtors hsorts
      hPos rfl rfl rfl rfl rfl hfamFree hprojTbl
  -- ## the constructors, consed
  have hctorsAs : ∀ c, c < ctorsAs.length →
      ctorsAs[c]? = some ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c) := by
    intro c hc
    show ctorsAs[c]? = some (ctorsAs.getD c [])
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hc]
    rfl
  obtain ⟨mpC₀', hEtaC, hcoreC', hagC⟩ :=
    stageBlockCtors hμ hN hN.2.2 hS.toBlockCtorsStage hlenCtorsAs hctorsAs ctorsAs 0 env₁ mpI
      (fun c => by rw [Nat.zero_add]) (Nat.zero_add _) hEtaI hcore
      (fun c _ j cA hj => hfreshC c j cA hj)
  -- ## coverage across the formers' and the constructors' conses (lane COVERB):
  -- the stage's carrier, rebuilt with the input's recorded list; the block's
  -- members pending
  have hcvOfK : ∀ m, m < p₁.k → ∃ cvTb, cvTas[m]? = some cvTb :=
    fun m hm => ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hm)⟩
  have hmemCv : ∀ cvTb ∈ cvTas, env.find? cvTb.name = none := by
    intro cvTb hcvTb
    obtain ⟨m, hm⟩ := List.getElem?_of_mem hcvTb
    exact hF.freshOf m cvTb hm
  -- every constructor's result head is its member (the check's `is_valid_ind_app`)
  have hheadK : ∀ m, m < p₁.k → ∀ cA ∈ ctorsAs.getD m [], ∃ bs body us,
      cA.1.type.stripPis (p₁.nP + cA.2) = some (bs, body) ∧
      body.getAppFn = .const ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m) us := by
    intro m hm cA hcA
    obtain ⟨cvTa, hcv⟩ := hcvOfK m hm
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨c, sorts, -, -, -, -, -, -, -, -, -, -, -, hCtor⟩ := (hfacts m cvTa hm hcv).2 j cA hj
    obtain ⟨-, ⟨cbs, es, hs, -⟩, -⟩ := ConLeche.checkSumCtor_shape hCtor
    exact ⟨cbs, _, List.map Level.param (p₀.complete p₁).lps, hs, by
      rw [getAppFn_mkAppN_const, hN.1 m cvTa hcv]⟩
  -- F8: every constructor concludes in its member at `nP + nIdx` arguments
  have hshapeK : ∀ m, m < p₁.k → ∀ cA ∈ ctorsAs.getD m [], ∃ bs args,
      cA.1.type.stripPis ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP + cA.2)
        = some (bs, Expr.mkAppN (.const ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m)
            (cA.1.levelParams.map .param)) args) ∧
      ∀ ψ, args.length = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP
        + ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).IdsM m ψ).length := by
    intro m hm cA hcA
    obtain ⟨cvTa, hcv⟩ := hcvOfK m hm
    obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
    obtain ⟨c, sorts, -, -, -, hlpsA, -, -, -, -, -, -, -, hCtor⟩ :=
      (hfacts m cvTa hm hcv).2 j cA hj
    obtain ⟨-, ⟨cbs, es, hs, hes⟩, -⟩ := ConLeche.checkSumCtor_shape hCtor
    refine ⟨cbs, ConLeche.structPsAt cA.2 p₁.nP ++ es, ?_, fun ψ => ?_⟩
    · rw [hN.1 m cvTa hcv, hlpsA]; exact hs
    · have hlen := (hcoreC'.1 m cvTa hcv).2.2.2.len ψ
      have hIds : ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).IdsM m ψ).length
          = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt m := by
        show (((ppsOf m ψ).drop p₁.nP).map (·.2.2)).length = _
        rw [List.length_map, List.length_drop]
        have : (ppsOf m ψ).length
            = p₁.nP + (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt m := hlen
        omega
      rw [hIds, List.length_append, hes]
      simp [ConLeche.structPsAt]
      rfl
  obtain ⟨newI, hnewI, hnewIall⟩ :=
    consBlockInds_consts (p₁ := p₁) (isRec := isRec) cvTas 0 env
  have henv₁ : env₁.consts = newI ++ env.consts := by rw [hcons]; exact hnewI
  have hnewC : ∀ c ∈ (ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse,
      ∃ m cA, m < p₁.k ∧ cA ∈ ctorsAs.getD m [] ∧ c = .ctorInfo cA.1 p₁.nP cA.2 := by
    intro c hc
    obtain ⟨cA, hcA, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hc)
    obtain ⟨l, hl, hcAl⟩ := List.mem_flatten.mp hcA
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hl
    refine ⟨m, cA, by rw [← hlenCtorsAs]; exact hm, ?_, rfl⟩
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
    exact hcAl
  obtain ⟨mpC₀, hbC, hlC, hcovC⟩ := lfpCover_append (ex := []) (ex' := cvTas.map (·.name)) mp mpC₀'
    (new := (ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse ++ newI)
    (by rw [consBlockCtors_consts, henv₁, List.append_assoc]; rfl)
    (fun n ci hf => by
      have hfr : ∀ c ∈ (ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse
          ++ newI, env.find? c.name = none := by
        intro c hc
        rcases List.mem_append.mp hc with hc | hc
        · obtain ⟨m, cA, hm, hcA, rfl⟩ := hnewC c hc
          obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
          exact consBlockInds_find?_none (hcons ▸ hfreshC m j cA hj)
        · obtain ⟨cv, hcv, j, rfl⟩ := hnewIall c hc
          exact hmemCv cv hcv
      show List.find? _ _ = _
      rw [consBlockCtors_consts, henv₁, ← List.append_assoc]
      exact find?_append_of_fresh hfr hf)
    (fun c hc tbl h => by
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨m, cA, -, -, rfl⟩ := hnewC c hc; exact nomatch h
      · obtain ⟨cv, -, j, rfl⟩ := hnewIall c hc; exact nomatch h)
    (fun n hn => by
      have hnI : (env₁.find? n).isSome = true := by
        rw [hcons]; exact consBlockInds_find?_isSome_mono cvTas 0 env n hn
      rw [hagC n hnI]
      exact hagI n fun cvTb hcvTb h => by
        rw [h, hmemCv cvTb hcvTb] at hn; exact nomatch hn)
    (fun _ h => nomatch h)
    (fun n hn => by
      obtain ⟨cvTb, hcvTb, rfl⟩ := List.mem_map.mp hn
      exact Or.inr (hmemCv cvTb hcvTb))
    (fun c hc cv caps h => by
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨m, cA, -, -, rfl⟩ := hnewC c hc; exact nomatch h
      · obtain ⟨cv', hcv', j, rfl⟩ := hnewIall c hc
        exact List.mem_map.mpr ⟨cv', hcv', rfl⟩)
    (fun c hc C hC => by
      rcases List.mem_append.mp hc with hc | hc
      · obtain ⟨m, cA, hm, hcA, rfl⟩ := hnewC c hc
        obtain ⟨bs, body, us, hs, hg⟩ := hheadK m hm cA hcA
        rw [ctorEntry_head rfl hs hg hC]
        obtain ⟨cvTa, hcv⟩ := hcvOfK m hm
        rw [hN.1 m cvTa hcv]
        exact Or.inr (Or.inl (hF.freshOf m cvTa hcv))
      · obtain ⟨cv', -, j, rfl⟩ := hnewIall c hc
        simp [ctorEntry] at hC)
  have hcoreC : BlockCtorsCore mpC₀.base2 (blockDataOf V p₁ ctorsAs pk uOf ppsOf) p₁.lps cvTas
      p₁ isRec (blockLeafH (blockDataOf V p₁ ctorsAs pk uOf ppsOf))
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
    rw [hbC]; exact hcoreC'
  -- ## the block's LFP CLAUSE, recorded at the constructors' environment
  -- (lane ENVLFP): the representation is built from the stages' three
  -- records (`blockModelAt_of_records`) and its `functor`/`fibre`/`leaf`
  -- enter the invariant (`EnvModelM.addLfp`), so the recursor stage
  -- below — and every later environment — carries it
  have hk0 : 0 < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
    rw [← hN.2.2, hcvTas]; exact Nat.succ_pos _
  -- the operator's MONOTONICITY is positivity's (lane HOLE2): every
  -- constructor positive along the tuple order at the hole frame, from the
  -- positivity stage's run at the formers' environment (conjunct 7b)
  have hposC := hposI
    (fun c j cA hj => by
      have hck : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
        rw [← hN.2.2]; exact hN.2.1 c j cA hj
      have hf := (hcoreC.2.2.2 c hck j cA hj).1
      have hw := mpC₀.base2.wf _ (List.mem_of_find?_eq_some hf)
      exact ⟨hw.1, hw.2.2.2.1⟩)
  have hMC := blockModelAt_of_records hN hS.toBlockCtorsStage hcoreC rfl hk0
    (fun _ _ => rfl) (fun _ _ _ _ => rfl)
    (blockMono_of_pos hN hS.toBlockCtorsStage hcoreC hk0 (fun _ _ => rfl) (fun _ _ _ _ => rfl)
      hposC) (blockFitsMono_of_pos hposC)
  have hLC := blockLfpClause_of_records hN hS.toBlockCtorsStage hcoreC rfl hk0
    (fun _ _ => rfl) (fun _ _ _ _ => rfl) hposC
    (hfokI (fun c j cA hj => by
      have hck : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
        rw [← hN.2.2]; exact hN.2.1 c j cA hj
      have hf := (hcoreC.2.2.2 c hck j cA hj).1
      have hw := mpC₀.base2.wf _ (List.mem_of_find?_eq_some hf)
      exact ⟨hw.1, hw.2.2.2.1⟩))
  have hstC : LfpStored (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp := by
    refine ⟨fun mm hmm => ?_, fun c hc j hj => ?_⟩
    · obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
        ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hmm)⟩
      have hname := hN.1 mm cvTb hcv
      exact ⟨cvTb, _, by
        show (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
          ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName mm) = _
        rw [hname]; exact (hcoreC.1 mm cvTb hcv).1⟩
    · have hck : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
        have : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k + 0 := hc
        omega
      have hcj : ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j]?
          = some ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j] :=
        List.getElem?_eq_getElem hj
      refine ⟨((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j].1,
        (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP,
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j].2, ?_⟩
      show (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        (((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c).getD j default).1.name
          = some (.ctorInfo ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j].1
              (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP
              ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c)[j].2)
      rw [List.getD_eq_getElem?_getD, hcj, Option.getD_some]
      exact (hcoreC.2.2.2 c hck j _ hcj).1
  -- M4 (lane CONTSEM): each member's stored type reads as its hole telescope
  have hrdC : LfpReads mpC₀.base2.acval (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp := by
    intro mm hmm
    obtain ⟨cvTb, hcv⟩ : ∃ cvTb, cvTas[mm]? = some cvTb :=
      ⟨_, List.getElem?_eq_getElem (by rw [hN.2.2]; exact hmm)⟩
    have hname := hN.1 mm cvTb hcv
    obtain ⟨hfind, -, -, hFD⟩ := hcoreC.1 mm cvTb hcv
    refine ⟨cvTb, _, by
      show (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName mm) = _
      rw [hname]; exact hfind, fun ψ => ⟨_, hFD.read ψ, ?_, hFD.bits ψ⟩⟩
    show _ = (((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ppsM mm ψ).take
        (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP).map (·.2.2) ++
      (((blockDataOf V p₁ ctorsAs pk uOf ppsOf).ppsM mm ψ).drop
        (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nP).map (·.2.2)
    rw [← List.map_append, List.take_append_drop]
  -- M2 (lane CONTSEM): each constructor reads as its hole telescope, canonically
  have hkLen : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k
      = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length := by
    simp [blockDataOf, blockDataPre, BlockData.withPhi, ConLeche.BlockShape.k,
      ConLeche.BlockShape.memberNames]
  have hcrC : LfpCtorReads mpC₀.base2.acval (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp :=
    blockCtorReads_of hN hcoreC hkLen
      (fun c cvTb hc hcv => hS.toBlockCtorsStage.lpsT c cvTb hc hcv)
      (fun c j cA hj => by
        have hck : c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k := by
          rw [← hN.2.2]; exact hN.2.1 c j cA hj
        have hf := (hcoreC.2.2.2 c hck j cA hj).1
        exact (mpC₀.base2.wf _ (List.mem_of_find?_eq_some hf)).1)
      (canonOcc_of_positivity hPos rfl rfl hkLen
        (fun c hc => hctorsAs c (by rw [hlenCtorsAs]; exact hc)))
      (fun c hc j cA hj ψ ρ hsat =>
        ((hS.toBlockCtorsStage.frames c hc j cA hj).1 ψ ρ).mp
          (hS.toBlockCtorsStage.paramsOf 0 hk0 ψ ρ hsat c hc))
  let mpC := mpC₀.addLfp (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp hLC hstC hrdC
    hcrC
  -- ## coverage at the block's record (lane COVERB): the members leave the
  -- exemption list; the block owns its constructors
  have hlpsNd : p₁.lps.Nodup := by
    have h0 := checkBlockTele_nodup htele0
    rw [hlps₀ ms0 (by rw [hmem0]; exact List.mem_cons_self)] at h0
    rw [hq]; exact h0
  have hcovMpC : LfpCover mp [] → LfpCover mpC [] := fun h0 =>
    (hcovC h0).addLfp_to _ _ _ _ _ hndM hkLen.symm
      (fun mm hmm cv caps hf => by
        obtain ⟨cvTb, hcv⟩ := hcvOfK mm hmm
        have hf' := (hcoreC.1 mm cvTb hcv).1
        rw [← hN.1 mm cvTb hcv] at hf'
        rw [show (blockDataOf V p₁ ctorsAs pk uOf ppsOf).toLfp.member mm
          = (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName mm from rfl, hf'] at hf
        injection hf with hf; injection hf with hcv' hcaps
        rw [← hcaps, blockCapsAt_all]; rfl)
      (blockLfpOwn (d := blockDataOf V p₁ ctorsAs pk uOf ppsOf) (lps := p₁.lps)
        (consBlockCtors_consts p₁.nP ctorsAs env₁)
        (fun m hm => by
          rw [henv₁, List.filterMap_append]
          obtain ⟨cvTa, hcv⟩ := hcvOfK m hm
          have hnil : newI.filterMap
              (ctorEntry ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m)) = [] := by
            rw [List.filterMap_eq_nil_iff]
            intro c hc
            obtain ⟨cv', -, j, rfl⟩ := hnewIall c hc
            rfl
          rw [hnil, List.nil_append]
          exact ctorEntries_fresh mp.base2.wf (by rw [hN.1 m cvTa hcv]; exact hF.freshOf m cvTa hcv))
        hlenCtorsAs (fun _ => rfl) hndM hkLen.symm hheadK
        (fun m hm => by
          obtain ⟨cvTb, hcv⟩ := hcvOfK m hm
          refine ⟨cvTb, _, by rw [hN.1 m cvTb hcv]; exact (hcoreC.1 m cvTb hcv).1,
            blockCapsAt_nparams _ _ _, hF.lpsOf m cvTb hcv⟩)
        hlpsNd
        (fun ψ => by
          obtain ⟨cvTb, hcv⟩ := hcvOfK 0 hk0
          have hlen := (hcoreC.1 0 cvTb hcv).2.2.2.len ψ
          show (((ppsOf 0 ψ).take p₁.nP).map (·.2.2)).length = p₁.nP
          rw [List.length_map, List.length_take]
          have : (ppsOf 0 ψ).length
              = p₁.nP + (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt 0 := hlen
          omega)
        (fun c hc j cA hj => (hcoreC.2.2.2 c hc j cA hj).1) hshapeK)
      (by
        rw [List.filter_eq_nil_iff]
        intro n hn
        obtain ⟨cvTb, hcvTb, rfl⟩ := List.mem_map.mp hn
        obtain ⟨m, hm⟩ := List.getElem?_of_mem hcvTb
        have hmk : m < p₁.k := by
          rw [← hF.lenCv]; exact (List.getElem?_eq_some_iff.mp hm).1
        simp only [decide_not, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not,
          Classical.not_not]
        rw [← hN.1 m cvTb hm]
        exact getD_mem _ (by
          show m < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length
          rw [← hkLen]; exact hmk))
  -- ## every member's projection slots, free at the constructors' environment
  have hnpEnvC : ∀ c, c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k →
      (∃ cA, (blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c = [cA]) →
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt c = 0 → ∀ j,
      NoProjEnv (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c) j := by
    intro c hc h1 h2 j
    obtain ⟨cvTa, hcv⟩ : ∃ cvTa, cvTas[c]? = some cvTa :=
      ⟨_, List.getElem?_eq_getElem (by rw [hF.lenCv]; exact hc)⟩
    have hname : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c = cvTa.name :=
      (hF.nameOf c cvTa hcv).symm
    have h0 : NoProjEnv env
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c) j := by
      rw [hname]
      exact noProjEnv_of_fresh mp.base2.wf (hF.freshOf c cvTa hcv) j
    have h1' : NoProjEnv env₁
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c) j := by
      rw [hcons]
      refine noProjEnv_consBlockInds h0 (fun cvTb hcvTb => ?_)
      obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
      exact hS.noProjT c t cvTb hc ht j
    refine noProjEnv_consBlockCtors h1' (fun ctorsA hl cA hcA => ?_)
    obtain ⟨t, ht⟩ := List.getElem?_of_mem hl
    obtain ⟨jj, hjj⟩ := List.getElem?_of_mem hcA
    refine hS.noProjC c t jj cA hc h1 h2 ?_ j
    show (ctorsAs.getD t [])[jj]? = some cA
    rw [List.getD_eq_getElem?_getD, ht]
    exact hjj
  -- ## every member's projection TABLE is absent at the constructors'
  -- environment: the tables' stage checked it free above the
  -- recursors, and a name absent there was absent below them
  have hslotC : ∀ c, c < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).k →
      (∃ cA, (blockDataOf V p₁ ctorsAs pk uOf ppsOf).ctorsM c = [cA]) →
      (blockDataOf V p₁ ctorsAs pk uOf ppsOf).nIdxAt c = 0 → ∀ j,
      (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).findProj?
        ((blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c) j = none := by
    intro c hc h1 h2 j
    obtain ⟨cA, hcA⟩ := h1
    have hck : c < p₁.k := hc
    have hcAs : ctorsAs.getD c [] = [cA] := by
      rw [List.getD_eq_getElem?_getD,
        hctorsAs c (by rw [hlenCtorsAs]; exact hck), hcA]
      rfl
    -- the member's sorts list is a singleton, because it is as long as
    -- its constructor list (`checkSumCtors_inv`)
    obtain ⟨sorts, hs⟩ : ∃ sorts, sortsss.getD c [] = [sorts] := by
      obtain ⟨-, -, hall⟩ := ConLeche.checkBlockCtors_inv hCtors
      obtain ⟨mc, hmc⟩ : ∃ mc, (p₁.members.zip cvTas)[c]? = some mc := by
        refine ⟨_, List.getElem?_eq_getElem ?_⟩
        rw [List.length_zip, hF.lenCv, hkm, Nat.min_self]
        exact Nat.lt_of_lt_of_eq hck hkm
      obtain ⟨ctorsA, sortss, hcs, hss, hsum⟩ := hall c mc hmc
      obtain ⟨hlc, hls, -⟩ := ConLeche.checkSumCtors_inv hsum
      have hlen1 : sortss.length = 1 := by
        rw [hls, ← hlc]
        have : ctorsA = ctorsAs.getD c [] := by
          rw [List.getD_eq_getElem?_getD, hcs]; rfl
        rw [this, hcAs]
        rfl
      match sortss, hlen1 with
      | [sorts], _ => exact ⟨sorts, by rw [List.getD_eq_getElem?_getD, hss]; rfl⟩
    have hn0 : (p₁.members.getD c default).nIdx = 0 := by
      rw [← blockNIdxs_getD (q := p₁) (j := c) (Nat.lt_of_lt_of_eq hck hkm)]
      exact h2
    have hfree := find?_none_consBlockRecsT
      (blockTablesTblFree (q := p₁) (p₁.members.zip (ctorsAs.zip sortsss)) _ env₂
        hTbl c _ (hzipEntry c hck) cA sorts hcAs hs hn0)
    have hname : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName c
        = (p₁.members.getD c default).cvT.name := hmnameEq c hck
    have hfree' : (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?
        (projTableName (p₁.members.getD c default).cvT.name) = none := hfree
    rw [hname, ConLeche.Env.findProj?, hfree']
  -- ## the block over the input environment (lane NESTIND, `hXfix`)
  have hover : BlockOverEnv (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
      (p₀.complete p₁).toBlockShape.memberNames := by
    show BlockOverEnv _ p₁.memberNames
    refine ⟨env, mp.base2.wf, fun n hn => ?_, fun n ci hf => ?_⟩
    · obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hn
      have hmk : m < p₁.k := by
        have : m < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length := hm
        rw [← hkLen] at this; exact this
      obtain ⟨cvTb, hcv⟩ := hcvOfK m hmk
      have hname : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m = cvTb.name :=
        hN.1 m cvTb hcv
      have hget : (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberName m = p₁.memberNames[m] := by
        show p₁.memberNames.getD m .anonymous = _
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
        rfl
      show env.find? p₁.memberNames[m] = none
      rw [← hget, hname]
      exact hF.freshOf m cvTb hcv
    · have hcs : (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).consts
          = (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 p₁.nP c.2).reverse
            ++ (newI ++ env.consts) := by
        rw [consBlockCtors_consts, henv₁]
      unfold ConLeche.Env.find? at hf
      rw [hcs, List.find?_append, List.find?_append] at hf
      cases h1 : List.find? (fun x => x.name == n)
          (ctorsAs.flatten.map fun c => ConstantInfo.ctorInfo c.1 p₁.nP c.2).reverse with
      | some ci' =>
        rw [h1] at hf
        obtain rfl : ci' = ci := Option.some.inj hf
        have hmem := List.mem_of_find?_eq_some h1
        rw [List.mem_reverse, List.mem_map] at hmem
        obtain ⟨cA, hcA, rfl⟩ := hmem
        obtain ⟨l, hl, hcAl⟩ := List.mem_flatten.mp hcA
        obtain ⟨m, hm⟩ := List.getElem?_of_mem hl
        have hmk : m < p₁.k := by
          have := (List.getElem?_eq_some_iff.mp hm).1
          rw [hlenCtorsAs] at this; exact this
        have hgl : ctorsAs.getD m [] = l := by
          rw [List.getD_eq_getElem?_getD, hm]; rfl
        obtain ⟨bs, body, us, hs, hhd⟩ := hheadK m hmk cA (by rw [hgl]; exact hcAl)
        refine Or.inr (Or.inr ⟨cA.1, p₁.nP, cA.2, bs, body, us, _, rfl, hs, hhd, ?_⟩)
        exact getD_mem _ (by
          show m < (blockDataOf V p₁ ctorsAs pk uOf ppsOf).memberNames.length
          rw [← hkLen]; exact hmk)
      | none =>
        rw [h1, Option.none_or] at hf
        cases h2 : List.find? (fun x => x.name == n) newI with
        | some ci' =>
          rw [h2] at hf
          obtain rfl : ci' = ci := Option.some.inj hf
          obtain ⟨cv, -, j, rfl⟩ := hnewIall _ (List.mem_of_find?_eq_some h2)
          exact Or.inr (Or.inl ⟨cv, _, rfl⟩)
        | none =>
          rw [h2, Option.none_or] at hf
          exact Or.inl hf
  -- ## the positivity model at the formers' environment (lane NESTIND,
  -- session 19): the input's clauses, the members exempt, `mpC`'s leaves
  have hmkI : LfpCover mp [] →
      FormersModelAt (V := V) env₁ (p₀.complete p₁).toBlockShape.memberNames mpC
        (blockDataOf V p₁ ctorsAs pk uOf ppsOf) p₁.lps cvTas p₁ isRec := by
    intro h0
    have hlenN : p₁.memberNames.length = p₁.k := by
      show (p₁.members.map _).length = _; simp; rfl
    obtain ⟨mk, hbk, hlk, hck⟩ := lfpCover_formers mp hcons mpI hmemCv hagI
      (names := p₁.memberNames)
      (fun cvTb hcvTb => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hcvTb
        have htk : t < p₁.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hF.lenCv] at this
        rw [hF.nameOf t cvTb ht]
        exact getD_mem _ (by rw [hlenN]; exact htk))
      (fun n hn => by
        obtain ⟨t, ht⟩ := List.getElem?_of_mem hn
        have htk : t < p₁.k := by
          have := (List.getElem?_eq_some_iff.mp ht).1; rwa [hlenN] at this
        obtain ⟨cvTb, hcv⟩ := hcvOfK t htk
        have hname := hF.nameOf t cvTb hcv
        rw [List.getD_eq_getElem?_getD, ht] at hname
        rw [← show cvTb.name = n from hname]
        exact hF.freshOf t cvTb hcv) h0
    have hagk : ∀ n, (env₁.find? n).isSome = true → mpC.base2.acval n = mk.base2.acval n := by
      intro n hn
      show mpC₀.base2.acval n = mk.base2.acval n
      rw [hbC, hbk]
      exact hagC n hn
    -- the constructors' conses keep every lookup (their names fresh at `env₁`)
    have hEq : ConLeche.consBlockCtors p₁.nP ctorsAs env₁
        = ⟨(ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse
            ++ env₁.consts⟩ := by
      rw [← consBlockCtors_consts]
    have hfrC : ∀ c ∈ (ctorsAs.flatten.map fun cA => ConstantInfo.ctorInfo cA.1 p₁.nP cA.2).reverse,
        env₁.find? c.name = none := by
      intro c hc
      obtain ⟨m, cA, -, hcA, rfl⟩ := hnewC c hc
      obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
      exact hfreshC m j cA hj
    have hfwdC : ∀ (n : Name) (ci : ConstantInfo), env₁.find? n = some ci →
        (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find? n = some ci := by
      intro n ci hf
      rw [hEq]
      exact find?_append_of_fresh hfrC hf
    have hprojC : ∀ (sn : Name) (i : Nat), env₁.findProj? sn i = none →
        (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).findProj? sn i = none := by
      intro sn i h
      rw [hEq]
      exact findProj?_append_none (fun c hc tbl h' => by
        obtain ⟨m, cA, -, -, rfl⟩ := hnewC c hc; exact nomatch h') sn i h
    refine ⟨mk, hck, fun D hD => ?_, hagk, fun D hD => ?_, ?_, ?_⟩
    · rw [hlk, ← hlC] at hD
      exact List.mem_cons_of_mem _ hD
    · rcases List.mem_cons.mp hD with rfl | hD
      · exact Or.inl rfl
      · rw [hlC, ← hlk] at hD
        exact Or.inr hD
    · rw [hbk]; exact hcore.holeCtx
    · intro ψ dd e ea h
      refine denoteMeta_envExtend_mono_ok (fun hf => hfwdC _ _ hf)
        ⟨natLitSupported_mono_of_keep hfwdC, strLitSupported_mono_of_keep hfwdC⟩ hprojC dd e ?_
      rw [denoteMeta_acval_congr (env := env₁) (acval₂ := mk.base2.acval) hagk]
      exact h
  -- ## the recursors' stage, and the tables' invariant across it
  obtain ⟨mpR₀, hag, hfindMono, hden, hnpMono⟩ :=
    hrecT (ConLeche.consBlockCtors p₁.nP ctorsAs env₁) env₁
      (p₀.complete p₁)
      cvTas ctorsAs outR mpC (blockDataOf V p₁ ctorsAs pk uOf ppsOf) isRec
      (blockLeafH (blockDataOf V p₁ ctorsAs pk uOf ppsOf)) kinds nfs nodes
      hRec hPos rfl hnames hndM hN hS.toBlockCtorsStage hcoreC
      (fun c hc => hctorsAs c hc) ⟨pk, uOf, ppsOf, rfl⟩
      (EnvModelM.mem_addLfp mpC₀ _ hLC hstC hrdC hcrC) hcovMpC hmkI hover
  have hcoreT :=
    (blockTablesCore_of hN hcoreC hnpEnvC).consRecs hag hfindMono hden hnpMono hslotC
  -- ## coverage across the recursors' conses (lane COVERB): only recursors
  -- are stored, every old name keeps its leaf
  obtain ⟨newR, hnewR, hnewRall⟩ := consBlockRecsT_consts
    (find? := (ConLeche.consBlockCtors p₁.nP ctorsAs env₁).find?)
    (res := (·.constsResolve (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)))
    (q := (p₀.complete p₁).toBlockShape) 0 outR
    (ConLeche.consBlockCtors p₁.nP ctorsAs env₁)
  obtain ⟨mpR, hbR, -, hcovR⟩ := lfpCover_append (ex := []) (ex' := []) mpC mpR₀ hnewR hfindMono
    (fun c hc tbl h => by obtain ⟨r, -, mI, rP, rules, rfl⟩ := hnewRall c hc; exact nomatch h)
    hag (fun _ h => h) (fun _ h => Or.inl h)
    (fun c hc cv caps h => by obtain ⟨r, -, mI, rP, rules, rfl⟩ := hnewRall c hc; exact nomatch h)
    (fun c hc C hC => by
      obtain ⟨r, -, mI, rP, rules, rfl⟩ := hnewRall c hc
      simp [ctorEntry] at hC)
  rw [← hbR] at hcoreT
  -- ## the tables
  suffices hT : CoverTo mpR [] env₂ [] by
    obtain ⟨mpF, hF'⟩ := hT
    exact ⟨mpF, fun h0 => hF' (hcovR (hcovMpC h0))⟩
  refine stageBlockTables hN hS rfl rfl rfl (p₁.members.zip (ctorsAs.zip sortsss)) 0 _ env₂
    mpR ?_ hTbl hcoreT
  intro c e hce
  have hck : c < p₁.k := by
    have h := (List.getElem?_eq_some_iff.mp hce).1
    rw [List.length_zip, List.length_zip, hlenCtorsAs, hlenSortsss] at h
    simp only [Nat.min_self] at h
    rw [hkm]
    omega
  obtain rfl : e = (p₁.members.getD c default, ctorsAs.getD c [], sortsss.getD c []) :=
    Option.some.inj (hce.symm.trans (hzipEntry c hck))
  refine ⟨by rw [Nat.zero_add]; exact hck, ?_, ?_, ?_, ?_⟩
  · rw [Nat.zero_add]; exact (hmnameEq c hck).symm
  · rw [Nat.zero_add]
    show (p₁.members.getD c default).nIdx = p₁.nIdxs.getD c 0
    rw [blockNIdxs_getD (q := p₁) (j := c) (show c < p₁.members.length from hck)]
  · rw [Nat.zero_add]; rfl
  · intro sorts hss
    rw [Nat.zero_add]
    show sorts = (sortsss.getD c []).getD 0 []
    have hss' : sortsss.getD c [] = [sorts] := hss
    rw [hss']
    rfl


/-- **The P carrier survives the uniform install at `k` members** — the
block step with the route switch off (see `declBlock_gen`).

Two things about `hrec`, the recursor stage's obligation:

* it is stated at the stage's own run: the target check (at member
  majors only), which the stage `checkBlockRec` runs before its
  reject-only conformance check (`recStage_of_rec`);
* it is handed everything the CONSTRUCTORS' environment knows: the
  model `mpC`, the block data `dR` with the three records
  `blockModelAt_of_stages` consumes (`BlockNamesOk`,
  `BlockCtorsStage`, `BlockCtorsCore`) and the positional link from
  the stage's `ctorsAs` to `dR.ctorsM`, plus the recogniser's member
  names and the STORAGE of the constructors the recursors carry. -/
theorem declBlock (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts} (mp : EnvModelM V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂)
    (hrec : ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
        (ctorsAsR : List (List (ConstantVal × Nat)))
        (rsR : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat)))
        (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
        (A : Nat → (Name → Nat) → AnnotTerm)
       ,
        -- the recursor stage's own run: the target check's, and its kind-free
        -- facts
        (∃ out, rsR = ConLeche.tgtRs out ∧ Nonempty (ConLeche.TargetRecRun μ F
          (ConLeche.mkFEnv envC) pp.toBlockShape false false block cvTasR ctorsAsR out)) →
        ConLeche.RecStageOk μ F envC pp cvTasR ctorsAsR rsR →
        -- the recogniser's member names
        pp.toBlockShape.memberNames.Nodup →
        -- the block's REPRESENTATION at the constructors' environment,
        -- in the three records `blockModelAt_of_stages` consumes
        BlockNamesOk (V := V) dR cvTasR →
        BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A envI
          pp.ctorNamesAt →
        BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k →
        (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) →
        -- the constructors' STORAGE, at the lists the recursors carry
        (∀ r ∈ rsR, ∀ cA ∈ r.2.2.2,
          ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF)) →
        -- the block's REPRESENTATION is the run's own record (lane RM49:
        -- without it `dR` is over-quantified — nothing ties its `nP`,
        -- `resSort`, operator or injections to the block, and the
        -- regimes' `BlockModelAt` cannot be built)
        (∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
            (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
          dR = blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf) →
        -- the block's LFP CLAUSE is recorded in the carrier (lane ENVLFP): the
        -- recursor model's induction reads it (lane GRAPH1)
        dR.toLfp ∈ mpC.lfpBlocks →
        BlockRecStaged (V := V) μ envC pp.toBlockShape pp.nP rsR mpC) :
    CoverStep mp env₂ :=
  declBlock_gen hμ mp hE hdp hrun (blockCtorStageAt_flat hμ mp)
    fun envC envI pp cvTasR ctorsAsR out mpC dR isRecR A _kindsR _nfsR _nodesR hRec _hPos _henvC
      hnames hnd hN hS hcore hctorsAs hdR hlfp _hcovC _hmk _hover => by
      obtain ⟨hRT, hRecK, hmaj⟩ := ConLeche.recStage_of_rec hRec hnames
      -- the constructors the recursors carry are the constructors' stage's
      -- own lists, so they are stored
      have hctorsIn : ∀ r ∈ ConLeche.tgtRs out, ∀ cA ∈ r.2.2.2,
          ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF) := by
        intro r hr cA hcA
        obtain ⟨c, hc⟩ := recStage_ctorsIdx hRecK r hr
        have hcl : c < ctorsAsR.length := (List.getElem?_eq_some_iff.mp hc).1
        have heq : r.2.2.2 = dR.ctorsM c := Option.some.inj (hc.symm.trans (hctorsAs c hcl))
        rw [heq] at hcA
        obtain ⟨j, hj⟩ := List.getElem?_of_mem hcA
        have hck : c < dR.k := by
          have := hN.2.1 c j cA hj
          rwa [hN.2.2] at this
        exact ⟨cA.1, _, _, (hcore.2.2.2 c hck j cA hj).1⟩
      have h := hrec envC envI pp cvTasR ctorsAsR (ConLeche.tgtRs out) mpC dR isRecR A
        ⟨out, rfl, hRT⟩ hRecK hnd hN hS hcore hctorsAs hctorsIn hdR hlfp
      unfold BlockRecStagedT
      rw [ConLeche.consBlockRecsT_member _ _ _ _ _ _ _ hmaj]
      exact h

end ConLeche.Model
