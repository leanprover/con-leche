module

public import ConLeche.Model.Inductives.DeclBlock
public import ConLeche.Model.Inductives.ClassRecKit
public import ConLeche.Model.Inductives.ClassGenStep
public import ConLeche.Verify.Inductives.GenRecRun
public import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Model.Inductives.BlockRecAssembly
import ConLeche.Model.Inductives.GenRecClasses
import ConLeche.Model.Inductives.GenRecPins
public import ConLeche.Model.Inductives.TargetClassRows

public section

/-!
# SKELETON (not for landing): the generated recursor stage, assembled

`genRecStage` — the recursors' stage's obligation (`BlockRecStagedT`)
from the GENERATED stage's run, through the generic stage
(`blockRecStaged_dataR`) at the generated family's equation components.
Every `sorry` below is a sub-lane's target.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape BlockParts TargetMajor
  ClassGen ClassCtor ClassRead FEnv GenRecRun)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-! ## 1. The generated family's equation components -/

section Components

/-- Recursor `c`'s class (the pre-pass's reading). -/
@[expose] def genClsOf (rd : ClassRead) (c : Nat) : Nat := rd.recCls.getD c 0

/-- Recursor `c`'s `j`-th constructor, as the generator read it. -/
@[expose] def genCtorAt (g : ClassGen) (rd : ClassRead) (c j : Nat) : ClassCtor :=
  (g.ctors.getD (genClsOf rd c) []).getD j default

/-- The prefix slot of the minor premise of recursor `c`'s `j`-th
constructor. -/
@[expose] def genMinorSlot (g : ClassGen) (rd : ClassRead) (c j : Nat) : Nat :=
  ((List.range g.slots.length).find? fun s => match g.slots.getD s default with
    | .minor c' C _ => c' == genClsOf rd c && C == (genCtorAt g rd c j).cv.name
    | _ => false).getD 0

/-- The recursor the generated rules call at class `t`: the family's
first recursor at that class (the kernel's `classRecOf`, as a position). -/
@[expose] def genRecIdx (rd : ClassRead) (t : Nat) : Nat :=
  ((List.range rd.recCls.length).find? fun r => rd.recCls.getD r 0 == t).getD 0

/-- **The `ih` data of the generated rule**, read at the rule's frame
(depth `rP + nF`): per recursive field `(i, t, tele)` (`ClassCtor.recs`),
the callee RECURSOR (`genRecIdx rd t`, the graph's class index), the
walked field's telescope (read, at the family's elimination bit `bit`),
its index arguments and the applied field. -/
@[expose] noncomputable def genIhdAV (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
    (g : ClassGen) (rd : ClassRead) (bit : Nat) (ψ : Name → Nat) (c j : Nat) :
    List IhDatum :=
  let x := genCtorAt g rd c j
  let rP := g.pre.length
  let D := rP + x.nF
  let fvs := ((ConLeche.openPisAtFvars x.nF x.tyD rP).map (·.1)).getD []
  let ws := (ConLeche.targetPiDomsWith fvs x.tyN).getD []
  x.recs.map fun q =>
    let (xs, idx) := (g.ihParts q.2.1 q.2.2 (ws.getD q.1 default) D).getD ([], [])
    (genRecIdx rd q.2.1,
     (readOpenedDoms acval env ψ D xs).map fun a => (bit, a),
     idx.map fun e => (denoteMeta acval env ψ (D + xs.length) e).getD default,
     (denoteMeta acval env ψ (D + xs.length)
        (Expr.mkAppN (fvs.getD q.1 default) xs)).getD default)

/-- **The `ih` terms** of the generated rule, in chain form (`genIhAV`:
the callee its chain variable below the frame). -/
@[expose] noncomputable def genIhsAV (acval : Name → (Name → Nat) → AnnotTerm) (env : Env)
    (K : Nat) (g : ClassGen) (rd : ClassRead) (bit : Nat) (ψ : Name → Nat) (c j : Nat) :
    List AnnotTerm :=
  (genIhdAV acval env g rd bit ψ c j).map
    (genIhAV K g.pre.length (g.pre.length + (genCtorAt g rd c j).nF))

/-- **The residue** of the generated rule: its minor premise applied to
the fields and the `ih` values (`genRb0`). -/
@[expose] def genRbAV (g : ClassGen) (rd : ClassRead) (c j : Nat) : AnnotTerm :=
  genRb0 g.pre.length (g.nP + genMinorSlot g rd c j) (genCtorAt g rd c j).nF
    (genCtorAt g rd c j).recs.length

/-- **The generated calls** at class data `tup` (the graph kit's call
relation): at the `j`-th rule of recursor `c`, the prefix spine `xs` and
the fields `fs`, every `ih` names, at every spine `bs` of its telescope,
its callee's tagged element at the index readings and the applied
field. -/
@[expose] def genCallT (tup : Nat → List V → V) (ρ : Nat → V)
    (ihd : Nat → Nat → List IhDatum) (xs : List V) (c j : Nat) (fs : List V) (v : V) : Prop :=
  ∃ q ∈ ihd c j, ∃ bs : List V,
    SpineFit (consList (xs ++ fs) ρ) (q.2.1.map (·.2)) bs ∧
    v = tagged q.1 (tup q.1 (q.2.2.1.map (interp V (consList bs (consList (xs ++ fs) ρ)))))
      (interp V (consList bs (consList (xs ++ fs) ρ)) q.2.2.2)

end Components

/-! ## 2. The context -/

/-- **The recursors' stage's context at the GENERATED stage**:
`NestedRecCtx` with the generated stage's run in place of the target
check's. -/
@[expose] def GenRecCtx (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) (envC envI : Env) (pp : BlockParts)
    (cvTasR : List ConstantVal) (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr))
    (posR : ConLeche.NestState) : Prop :=
  ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pp cvTasR ctorsAsR = .ok (kindsR, nfsR, posR) ∧
  envC = ConLeche.consBlockCtors pp.nP ctorsAsR envI ∧
  ctorsAsR.map (·.map (fun cA => (cA.1.name, cA.2)))
    = pp.members.map (fun ms => ms.ctors.map (fun c => (c.1.name, c.2))) ∧
  pp.toBlockShape.memberNames.Nodup ∧
  BlockNamesOk (V := V) dR cvTasR ∧
  BlockCtorsStage (V := V) μ F dR pp.lps cvTasR pp.toBlockShape isRecR A envI pp.ctorNamesAt ∧
  BlockCtorsCore mpC.base2 dR pp.lps cvTasR pp.toBlockShape isRecR A dR.k ∧
  (∀ c, c < ctorsAsR.length → ctorsAsR[c]? = some (dR.ctorsM c)) ∧
  (∃ (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
      (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
    dR = blockDataOf V pp.toBlockShape ctorsAsR pk uOfD ppsOf) ∧
  dR.toLfp ∈ mpC.lfpBlocks ∧
  LfpCover mpC [] ∧
  FormersModelAt (V := V) envI pp.toBlockShape.memberNames mpC dR pp.lps cvTasR
    pp.toBlockShape isRecR ∧
  BlockOverEnv envC pp.toBlockShape.memberNames ∧
  -- the generated stage's run: its seeds walked at `envI`, continuing the
  -- positivity run's state
  Nonempty (GenRecRun μ F (ConLeche.mkFEnv envI) envI (ConLeche.mkFEnv envC) pp.toBlockShape
    (ConLeche.blockNestedBit pp.toBlockShape kindsR) posR cvTasR block ctorsAsR out) ∧
  -- the block's constructors conclude in its members
  (∀ c ∈ ctorsAsR.flatten, ∀ C, (ctorEntry C (.ctorInfo c.1 pp.nP c.2)).isSome = true →
    C ∈ pp.toBlockShape.memberNames)

/-- **The induction over the classes' majors, at the GENERATED calls**
(`TgtClassInd` with `genCallT` in place of the target check's calls):
the interface between the family premise and the node route. -/
@[expose] def GenClassInd (acval : Name → (Name → Nat) → AnnotTerm) (envC : Env)
    (p : BlockShape) (out : List (ConstantVal × TargetMajor × List Expr)) (d : BlockData V)
    (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal)
    (ihd : Nat → Nat → List IhDatum) (ψ : Name → Nat) (ρ : Nat → V) : Prop :=
  ∀ xs : List V, ∀ P : V → Prop,
    (∀ u, u ∈ˢ unionSet (tgtRs out).length
        (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) →
      (∃ e, graphDecG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
          (tgtClsInj d Dc mc cvc p out ψ) (blockRecNCt (tgtRs out))
          (tgtRs out).length
          (tgtClsFit d Dc mc cvc acval envC p out ψ ρ) xs u e ∧
        ∀ v, v ∈ˢ graphPredG (tgtClsIs d Dc mc cvc acval envC p out ψ ρ)
            (tgtClsCr d Dc mc cvc acval envC p out ψ ρ)
            (tgtRs out).length
            (genCallT (tgtClsTup d Dc mc cvc p out ψ) ρ ihd) xs e →
          P v) → P u) →
    ∀ u, u ∈ˢ unionSet (tgtRs out).length
        (tgtClsIs d Dc mc cvc acval envC p out ψ ρ xs)
        (tgtClsCr d Dc mc cvc acval envC p out ψ ρ xs) → P u

/-! ## 3. The stage -/

/-- The family's elimination bit at `ψ`. -/
@[expose] def genBit (pp : BlockParts) (ψ : Name → Nat) : Nat :=
  pwBit ψ (Level.zeronessOf (ConLeche.structElimLevel pp.elim pp.large))

set_option maxHeartbeats 1000000 in
/-- **THE GENERATED RECURSORS' STAGE**: the four cons-monotonicities at
the cons at the classes (`BlockRecStagedT`). -/
theorem genRecStage (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo} {envC envI : Env} {pp : BlockParts} {cvTasR : List ConstantVal}
    {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × TargetMajor × List Expr)}
    {mpC : EnvModelM V μ envC} {dR : BlockData V} {isRecR : Bool}
    {A : Nat → (Name → Nat) → AnnotTerm}
    {kindsR : List (List (List ConLeche.NestFieldKind))} {nfsR : List (List Expr)}
    {posR : ConLeche.NestState}
    (hctx : GenRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR
      posR) :
    BlockRecStagedT (V := V) μ envC pp.toBlockShape out mpC := by
  obtain ⟨hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov, hmk, hover,
    ⟨R⟩, hheads⟩ := hctx
  have h : ConLeche.RecStageG μ F envC pp cvTasR ctorsAsR (tgtRs out) (fun _ => False) := sorry
  obtain ⟨s, hsP, hTy⟩ := blockRecLevel_run (V := V) (mpC := mpC) hμ h
  unfold BlockRecStagedT
  rw [ConLeche.consBlockRecsT_eq_R]
  refine blockRecStaged_dataR (ctorTy := fun j i ψ =>
      blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ) hμ mpC h
    (ConLeche.recStageG_nodup h hndM)
    (ConLeche.recRulesShape_tgt envC.find? (·.constsResolve envC) pp.toBlockShape out)
    (fun j r hr lvls pins hf => by
      obtain ⟨n1, n2, n3, n4⟩ := ConLeche.tgtFireOf_nested hf
      exact ⟨n1, n2, fun pin hpin => ⟨(n3 pin hpin).1, (n3 pin hpin).2.1,
        (n3 pin hpin).2.2.1, (n3 pin hpin).2.2.2,
        tgtFire_pinsNoProj h j r hr lvls pins hf pin hpin⟩, n4⟩)
    (genRecCtor_in R hN hcore hctorsAs hdR hcov)
    (pdoms0 := fun ψ => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
    (fdoms0 := fun ψ => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ)
    (es0 := fun ψ => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ)
    (ihs := fun ψ => genIhsAV mpC.base2.acval envC (tgtRs out).length R.g R.rd (genBit pp ψ) ψ)
    (mk0 := fun ψ => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ)
    (Rb0 := fun _ => genRbAV R.g R.rd) (s := s) (nCt := blockRecNCt (tgtRs out))
    ?heqB ?heqV ?heqP ?hpre
    (fun j r hr => blockRecNCt_ge hr)
    (fun ψ j r hr => blockRulePdomsAV_length hμ mpC h hr ψ)
    (genRecCtor_seam R hN hcore hctorsAs hdR hcov) ?htower
    (fun m₃ hac φ j r hr _ cA rhs _ _ => recStagePinsOk hμ mpC h m₃ hac φ j r hr cA rhs) ?hdataS (blockRecTyZ_run hμ mpC h) ?hRaZ
  all_goals sorry

end ConLeche.Model
