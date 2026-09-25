module

public import ConLeche.Model.Inductives.DeclBlockNested
public import ConLeche.Model.Inductives.TargetClassRows
import ConLeche.Model.Inductives.BlockRecData
public import ConLeche.Model.Inductives.BlockDeclRun
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.RecCheckRun
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Model.Inductives.BlockRecPreHpre
import ConLeche.Model.Inductives.BlockRecPreRun

public section

/-!
# The recursors' stage at NESTED blocks, composed (lane NESTIND, session 14)

`NestedRecStageOwed` (`DeclBlockNested.lean`) from TWO named premises:

* `NestedClassIndOwed` — the induction over the recursor CLASSES
  (`TgtClassInd`, `tgtRecPre_clsI`'s `hind`), at every choice of the
  outside classes' data.  This is what route A's positivity derivation
  (lane POSDERIV) and the (D) typing are to supply (DESIGN F13);
* `NestedRecRestOwed` — every other fact the generic stage
  (`blockRecStaged_dataR`) asks of the switch-on cons, at the TARGET rule
  data (`tgtFdomsAV`/`tgtEsAV`/`tgtIhsAV`/`tgtMkAV`/`tgtRbAV`), bundled as
  `NestedRecRest`'s named fields, each to be discharged at `outside`.

What is DISCHARGED here: the stage record at any majors
(`recStage_of_targetG`), the switch-on cons as the generic one
(`consBlockRecsT_eq_R`) with its rules' shape (`recRulesShape_tgt`) and
the `.nested` firings' guards (`tgtFireOf_nested`), the per-recursor
bounds (`blockRecNCt_ge`, `blockRulePdomsAV_length`), the outside
classes' data (`tgtOutCls_of`, chosen), and the family premise's
CANDIDATE (`BlockRecPre.hCand`) from the class induction
(`tgtRecPre_clsI`) at the target equation list.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- **What the nested stage owes beyond the class induction**, at one
block's context and the family's level `s`, at the TARGET rule data. -/
structure NestedRecRest (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat) (envC : Env)
    (pp : BlockParts) (cvTasR : List ConstantVal)
    (out : List (ConstantVal × TargetMajor × List Expr)) (mpC : EnvModelM V μ envC)
    (s : (Name → Nat) → Nat) : Prop where
  /-- the stored recursors' names are distinct (the auxiliary ones by the
  `T.rec_i` name check, not yet inverted) -/
  hnd : ((tgtRs out).map (·.1.name)).Nodup
  /-- a `.nested` firing's pins mention no empty projection slot -/
  pinsNoProj : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    (tgtRs out)[j]? = some r → ∀ lvls pins, (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) j r = .nested lvls pins →
      ∀ pin ∈ pins, ∀ (T : Name) (i : Nat), envC.findProj? T i = none → Expr.NoProjAt T i pin
  /-- every constructor a recursor carries is stored (a container's too) -/
  ctorsIn : ∀ r ∈ (tgtRs out), ∀ cA ∈ r.2.2.2,
    ∃ cvj cnP cnF, envC.find? cA.1.name = some (.ctorInfo cvj cnP cnF)
  /-- the family premise's type half (`BlockRecPre.hTy`) -/
  hTy : ∀ (ψ : Name → Nat) (ρ : Nat → V), ∀ c, c < (tgtRs out).length →
    interp V ρ ((blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ) c) ∈ˢ (univ (s ψ) : V) ∧ WellDenoted V ρ ((blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ) c)
  /-- the family premise's equation half (`BlockRecPre.hEq`) -/
  hEq : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
    (∀ c, c < (tgtRs out).length → tup.getD c pt ∈ˢ interp V ρ ((blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ) c)) →
    ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') ψ),
      interp V (consList tup ρ) e ∈ˢ (univZero : V) ∧ WellDenoted V (consList tup ρ) e
  eqB : ∀ ψ : Name → Nat, ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') ψ), Term.bvarsBelow (tgtRs out).length e.erase
  eqV : ∀ (ψ : Name → Nat) (ρ : Nat → V) (tup : List V), tup.length = (tgtRs out).length →
    (∀ mm, mm < (tgtRs out).length →
      tup.getD mm pt ∈ˢ interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ mm)) →
    ∀ e ∈ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') ψ), AnnotValid V (consList tup ρ) e
  eqP : ∀ (i : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    (tgtRs out)[i]? = some r → ∀ ψ₁ ψ₂ : Name → Nat,
      (∀ q ∈ r.1.levelParams, ψ₁ q = ψ₂ q) → s ψ₁ = s ψ₂ ∧ (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') ψ₁) = (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') ψ₂)
  /-- the constructors a recursor carries: stored at the MAJOR's parameter
  count, their types bound and read -/
  ctor : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat), r.2.2.2[i]? = some cA →
      envC.find? cA.1.name = some (.ctorInfo cA.1 (ConLeche.tgtMajorsOf out j).nPc cA.2) ∧
      ConstsBound envC cA.1.type ∧
      ∀ ψ : Name → Nat,
        denoteMeta mpC.base2.acval envC ψ 0 cA.1.type = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ)
  /-- every fired stored rule reads as a λ-tower over the prefix and the
  fields (at a member major: `blockRuleTower_run`) -/
  tower : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
    r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) j r ≠ .inert →
    ∀ (acv : Name → (Name → Nat) → AnnotTerm) (ψ : Name → Nat) (Ra : AnnotTerm),
      denoteMeta acv (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find? (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp.toBlockShape 0 (tgtRs out) envC) ψ 0 rhs = some Ra →
      ∃ (lds : List (Nat × AnnotTerm)) (A : AnnotTerm), Ra = mkLamsAV lds A ∧
        lds.length = pp.toBlockShape.rulePrefixAt j + cA.2
  /-- **L6**: the `.nested` pins' law (vacuous at `.plain`) -/
  pins : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find? (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp.toBlockShape 0 (tgtRs out) envC),
    m₃.acval = (blockRecAcv mpC.base2.acval envC (tgtRs out) s
          (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out) (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ') (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ'))) →
    ∀ (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat ×
      List (ConstantVal × Nat)), (tgtRs out)[j]? = some r →
    ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs →
      RecRulePinsOk m₃ φ r.1 (pp.toBlockShape.rulePrefixAt j)
        (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := (ConLeche.tgtMajorsOf out j).nPc,
              fire := (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) j r, rhs := rhs, paramsBlind := true })
  /-- **L5 (O12)**: the rule data at every fired pair -/
  data : ∀ m₃ : EnvModel V (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find? (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp.toBlockShape 0 (tgtRs out) envC),
    m₃.acval = (blockRecAcv mpC.base2.acval envC (tgtRs out) s
          (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out) (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ') (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ'))) →
    ∀ (φ : Name → Nat) (j : Nat)
      (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)), (tgtRs out)[j]? = some r →
    ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
      r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) j r ≠ .inert →
      BlockRuleDataB (V := V) mpC pp ((ConLeche.tgtMajorsOf out j).nPc) (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find? (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp.toBlockShape 0 (tgtRs out) envC) (tgtRs out) s (blockRecNCt (tgtRs out))
        (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ') (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ')
        (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i) φ j i r cA
        (ConLeche.recRuleBits envC.find? r.1.name
            { ctor := cA.1.name, nfields := cA.2, ctorParams := (ConLeche.tgtMajorsOf out j).nPc,
              fire := (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) j r, rhs := rhs, paramsBlind := true }) rhs
  /-- the `ℓ = 0` arm: every recursor's type is a truth value -/
  tyZ : ∀ j, j < (tgtRs out).length → ∀ (ψ : Name → Nat) (ρ : Nat → V),
    Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0 →
    interp V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j) ∈ˢ (univZero : V)
  /-- the `ℓ = 0` arm: every fired stored rule reads as the point -/
  raZ : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
    (tgtRs out)[j]? = some r → ∀ (i : Nat) (cA : ConstantVal × Nat) (rhs : Expr),
    r.2.2.2[i]? = some cA → r.2.1[i]? = some rhs → (ConLeche.tgtFireOf (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) j r ≠ .inert →
    ∀ (ψ : Name → Nat) (Ra : AnnotTerm),
      denoteMeta (blockRecAcv mpC.base2.acval envC (tgtRs out) s
          (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out) (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ') (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ') (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ') (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out mpC.base2.acval envC ψ'))) (ConLeche.consBlockRecsR (ConLeche.tgtRulesR envC.find? (·.constsResolve envC) pp.toBlockShape (ConLeche.tgtMajorsOf out)) pp.toBlockShape 0 (tgtRs out) envC) ψ 0 rhs = some Ra →
      Level.eval ψ (ConLeche.structElimLevel pp.toBlockShape.elim pp.toBlockShape.large) = 0 →
      ∀ ρ : Nat → V, interp V ρ Ra = pt

/-- **The nested stage's context**: `NestedRecStageOwed`'s run facts, as
one predicate (the two owed premises below quantify over it once). -/
@[expose] def NestedRecCtx (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) (envC envI : Env) (pp : BlockParts)
    (cvTasR : List ConstantVal) (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)) : Prop :=
  ConLeche.checkBlockRec (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envC pp true
      (true && ConLeche.blockNestedBit pp.toBlockShape kindsR)
      (ConLeche.nestKindsFlat kindsR) block cvTasR ctorsAsR
      (ConLeche.blockNormalCtors pp.toBlockShape ctorsAsR nfsR) = .ok out ∧
  ConLeche.checkBlockPositivity (m := ConLeche.CheckM) (ConLeche.fueledOps μ F) envI
      envI.find? envI.consts pp cvTasR ctorsAsR true = .ok (kindsR, nfsR) ∧
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
  LfpCover mpC []

/-- **OWED — the induction over the recursor classes** (route A + (D);
DESIGN F13): at every nested stage's context and every choice of the
outside classes' data, `TgtClassInd`. -/
@[expose] def NestedClassIndOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR →
    ∀ (Dc : Nat → LfpDatum V) (mc : Nat → Nat) (cvc : Nat → ConstantVal),
      (∀ c, c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) (Dc c) (mc c) (cvc c)) →
      ∀ (ψ : Name → Nat) (ρ : Nat → V),
        TgtClassInd μ F envC mpC.base2.acval pp.toBlockShape (cvTasR.map (·.type)) out
          dR Dc mc cvc ψ ρ

/-- **OWED — the rest of the nested stage** (`NestedRecRest`'s fields), at
every nested stage's context, at some family level. -/
@[expose] def NestedRecRestOwed (V : Type w) [SetTheory V] (μ : CheckMode) (F : Nat)
    (block : List ConstantInfo) : Prop :=
  ∀ (envC envI : Env) (pp : BlockParts) (cvTasR : List ConstantVal)
    (ctorsAsR : List (List (ConstantVal × Nat)))
    (out : List (ConstantVal × ConLeche.TargetMajor × List Expr))
    (mpC : EnvModelM V μ envC) (dR : BlockData V) (isRecR : Bool)
    (A : Nat → (Name → Nat) → AnnotTerm)
    (kindsR : List (List (List ConLeche.NestFieldKind))) (nfsR : List (List Expr)),
    NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR →
    ∃ s : (Name → Nat) → Nat, NestedRecRest V μ F envC pp cvTasR out mpC s

/-- The target equation list `tgtRecPre_clsI` concludes at IS the stage's
(`blockRecEqs` at the target rule data): the prefix domains are closed
(`blockRecPdomsK_run`), and the chain lifts keep the field domains'
lengths (`liftDomsK_length`). -/
theorem tgtClsEqs_eq {F : Nat} {envC : Env} {mpC : EnvModelM V μ envC} (hμ : μ.verifiedChecks = true)
    {pp : BlockParts} {cvTasR : List ConstantVal} {ctorsAsR : List (List (ConstantVal × Nat))}
    {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)} {memR : Nat → Prop}
    (h : ConLeche.RecStageG μ F envC pp cvTasR ctorsAsR (tgtRs out) memR) (ψ : Name → Nat) :
    iotaEqsAV (tgtRs out).length (blockRecNCt (tgtRs out))
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ)
        (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
        (fun c j => liftEsK (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ c j).length)
          (tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ c j))
        (tgtMkK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ)
        (tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out
          mpC.base2.acval envC ψ)
        (fun c j => (tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ c j).liftN (tgtRs out).length
          ((blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ c).length
            + (tgtFdomsK (tgtRs out).length mpC.base2.acval envC pp.toBlockShape out ψ c
              j).length
            + (tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type)) out
              mpC.base2.acval envC ψ c j).length))
      = blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ') ψ := by
  show _ = iotaEqsAV _ _ _ _ _ _ _ _
  refine iotaEqsAV_congr (fun c hc => ?_) (fun c _ j _ => ?_)
  · exact (blockRecPdomsK_run (V := V) hμ mpC h (List.getElem?_eq_getElem hc) ψ _).symm
  · simp only [tgtFdomsK, liftDomsK_length]

/-- **THE NESTED RECURSORS' STAGE, from the class induction and the rest**
(lane NESTIND, session 14): `NestedRecStageOwed` reduces to
`NestedClassIndOwed` (the one premise route A + (D) supply) and
`NestedRecRestOwed` (the remaining named facts at the target rule data). -/
theorem nestedRecStageOwed_of (hμ : μ.verifiedChecks = true) {F : Nat}
    {block : List ConstantInfo}
    (hind : NestedClassIndOwed V μ F block) (hrest : NestedRecRestOwed V μ F block) :
    NestedRecStageOwed V μ F block := by
  intro envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hRec hPos henvC hnames
    hndM hN hS hcore hctorsAs hdR hlfp hcov
  have hctx : NestedRecCtx V μ F block envC envI pp cvTasR ctorsAsR out mpC dR isRecR A
      kindsR nfsR :=
    ⟨hRec, hPos, henvC, hnames, hndM, hN, hS, hcore, hctorsAs, hdR, hlfp, hcov⟩
  obtain ⟨s, H⟩ := hrest envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx
  have hind' := hind envC envI pp cvTasR ctorsAsR out mpC dR isRecR A kindsR nfsR hctx
  obtain ⟨R⟩ := ConLeche.targetRecCheck_run
    (ConLeche.checkBlockRecT_run (ConLeche.checkBlockRecT_of_rec hRec))
  have h := ConLeche.recStage_of_targetG R (ConLeche.ctorsLen_of_names hnames)
  -- the outside classes' data, chosen
  have hcls0 : ∀ c, ∃ t : LfpDatum V × Nat × ConstantVal,
      c < (tgtRs out).length → (tgtMajor out c).member = none →
        TgtOutCls mpC (tgtMajor out c) t.1 t.2.1 t.2.2 := by
    intro c
    by_cases hc : c < (tgtRs out).length
    · by_cases hm : (tgtMajor out c).member = none
      · obtain ⟨r, hr⟩ : ∃ r, (tgtRs out)[c]? = some r := ⟨_, List.getElem?_eq_getElem hc⟩
        obtain ⟨rc, cvRi, M, u, rhssA, -, -, ho, -, -, -, ⟨E⟩⟩ := ConLeche.targetRecRun_at R hr
        have hM : tgtMajor out c = M := by
          simp [tgtMajor, List.getD_eq_getElem?_getD, ho]
        rw [hM] at hm ⊢
        obtain ⟨D, mm, cvI, hD⟩ := tgtOutCls_of hcov E hm
        exact ⟨(D, mm, cvI), fun _ _ => hD⟩
      · exact ⟨(dR.toLfp, 0, default), fun _ h' => absurd h' hm⟩
    · exact ⟨(dR.toLfp, 0, default), fun h' => absurd h' hc⟩
  obtain ⟨tc, hcls⟩ := Classical.axiomOfChoice hcls0
  -- the family premise: its type and equation halves owed, its candidate
  -- from the class induction
  obtain ⟨pk, uOfD, ppsOf, rfl⟩ := hdR
  have hmr := blockMembersRun_seam hN hS hcore
  have hM := blockModelAt_seam h hN hS hcore hlfp
  have hpre : ∀ (ψ : Name → Nat) (ρ : Nat → V),
      ConLeche.Semantics.BlockRecPre V (s ψ) (tgtRs out).length
        (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ)
        (blockRecEqs (blockRecNCt (tgtRs out)) (tgtRs out)
          (fun ψ' => blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ')
          (fun ψ' => tgtFdomsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtEsAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtIhsAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ')
          (fun ψ' => tgtMkAV pp.toBlockShape out mpC.base2.acval envC ψ')
          (fun ψ' => tgtRbAV μ F (ConLeche.mkFEnv envC) pp.toBlockShape (cvTasR.map (·.type))
            out mpC.base2.acval envC ψ') ψ) ρ := by
    intro ψ ρ
    refine ⟨H.hTy ψ ρ, H.hEq ψ ρ, ?_⟩
    obtain ⟨a, ha, hb⟩ := tgtRecPre_clsI hμ hcov h R
      (Dc := fun c => (tc c).1) (mc := fun c => (tc c).2.1) (cvc := fun c => (tc c).2.2)
      (fun c hc hm => hcls c hc hm) ⟨pk, uOfD, ppsOf, rfl⟩ hN hS hcore hmr hM hlfp hndM ψ ρ
      (hind' _ _ _ (fun c hc hm => hcls c hc hm) ψ ρ)
    refine ⟨a, ha, fun e he => hb e ?_⟩
    rw [tgtClsEqs_eq hμ h ψ]
    exact he
  unfold BlockRecStagedT
  rw [ConLeche.consBlockRecsT_eq_R]
  exact blockRecStaged_dataR hμ mpC h H.hnd
    (ConLeche.recRulesShape_tgt envC.find? (·.constsResolve envC) pp.toBlockShape out)
    (fun j r hr lvls pins hf => by
      obtain ⟨n1, n2, n3, n4⟩ := ConLeche.tgtFireOf_nested hf
      exact ⟨n1, n2, fun pin hpin => ⟨(n3 pin hpin).1, (n3 pin hpin).2.1,
        (n3 pin hpin).2.2.1, (n3 pin hpin).2.2.2,
        H.pinsNoProj j r hr lvls pins hf pin hpin⟩, n4⟩)
    H.ctorsIn H.eqB H.eqV H.eqP hpre (fun j r hr => blockRecNCt_ge hr)
    (fun ψ j r hr => blockRulePdomsAV_length hμ mpC h hr ψ)
    H.ctor H.tower H.pins H.data H.tyZ H.raZ

/-- **The uniform block step at nested blocks, at the two owed premises**:
`declBlock_nested` with `NestedRecStageOwed` from `nestedRecStageOwed_of`. -/
theorem declBlock_nested_of (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nPd : Nat} {p₀ : BlockParts}
    (mp : EnvModelM V μ env) (hE : ConLeche.EtaFamiliesClosed env)
    (hdp : ConLeche.blockParts? nPd block = some p₀)
    (hrun : ConLeche.Semantics.DeclBlockRun μ F env block p₀ env₂ true)
    (hind : NestedClassIndOwed V μ F block) (hrest : NestedRecRestOwed V μ F block) :
    LfpCover mp [] → ∃ mp' : EnvModelM V μ env₂, LfpCover mp' [] :=
  declBlock_nested hμ mp hE hdp hrun (nestedRecStageOwed_of hμ hind hrest)

end ConLeche.Model
