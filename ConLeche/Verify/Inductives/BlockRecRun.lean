module

public import ConLeche.Kernel.Inductives.BlockInstall
public import ConLeche.Verify.ProjSlots
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Shift

public section

/-!
# Stage (b)'s record and the shared prefix's inversion

`RecTyEntry`: one recursor's type as checked against its MAJOR member —
the checked constant, the member's former and its parameter domains, the
major at the index binders, the conclusion's sort.  The target check's
run produces it (`recTyEntry_of_targetG`, `Verify/Inductives/RecStage.lean`),
and the stage record `RecStage` hands it out per recursor.  Also the
inversion of the family's shared rule prefix (`checkBlockRecPrefixAgree`).
-/

namespace ConLeche

variable {mode : CheckMode}

local syntax "close_throw" term : tactic
local macro_rules
  | `(tactic| close_throw $h:term) =>
    `(tactic| first
        | exact nomatch $h
        | exact absurd $h (by
            simp only [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]
            exact fun hh => nomatch hh)
        | exact absurd $h
            (by simp [bind, Except.bind, throw, throwThe, MonadExceptOf.throw]))

/-! ## Stage (b): one recursor's TYPE -/

/-- **Stage (b) at ONE recursor**.  `ri` is the recursor's position in the block, `rc` its
record, and `(cvRi, nIdx, u)` the entry the stage returns for it: the
CHECKED constant, the member's index count and the conclusion's
sort. -/
structure RecTyEntry (mode : CheckMode) (F : Nat) (env : Env) (p : BlockShape)
    (nested : Bool) (cvTas : List ConstantVal) (ri : Nat) (rc : RecShape)
    (cvRi : ConstantVal) (nIdx : Nat) (u : Level) : Type where
  /-- the member the recursor's major names -/
  ms : MemberShape
  /-- that member's checked type former -/
  cvTa : ConstantVal
  /-- the recursor type's `mI + 1` openers and its conclusion -/
  fvs : List Expr
  concl : Expr
  /-- the former's `nP` parameter openers and the rest of its type -/
  tfvs : List Expr
  trest : Expr
  /-- the MAJOR's opener -/
  maj : Expr
  /-- the conclusion's inferred type -/
  sty : Expr
  hms : p.members[p.recTgtAt ri]? = some ms
  hcvTa : cvTas[p.recTgtAt ri]? = some cvTa
  hcv : checkConstantVal (fueledOps mode F) env rc.cvR = .ok cvRi
  hnIdx : nIdx = ms.nIdx
  /-- the prefix starts with the block's parameters (nothing is counted
  after them: a motive is a parameter like any other) -/
  hroom : p.nP ≤ p.rulePrefixAt ri
  hmI : p.majorIdxAt ri = p.rulePrefixAt ri + ms.nIdx
  hopen : openPisAtFvars (p.majorIdxAt ri + 1) cvRi.type 0 = some (fvs, concl)
  hopenT : openPisAtFvars p.nP cvTa.type 0 = some (tfvs, trest)
  htfvs : tfvs.length = p.nP
  /-- the parameter domains, binder by binder, against the former's -/
  hparams : ∀ l, l < p.nP →
    isDefEqCore mode env F p.nP ((tfvs.map Expr.fvarTypeD).getD l default)
      (((fvs.take p.nP).map Expr.fvarTypeD).getD l default) = .ok true
  hmaj : fvs[p.majorIdxAt ri]? = some maj
  hmajFn : (Expr.fvarTypeD maj).getAppFn = Expr.const ms.cvT.name (p.lps.map .param)
  hmajLen : (Expr.fvarTypeD maj).getAppArgs.length = p.nP + ms.nIdx
  hmajParams : (Expr.fvarTypeD maj).getAppArgs.take p.nP = fvs.take p.nP
  hmajIdx : (Expr.fvarTypeD maj).getAppArgs.drop p.nP
    = (fvs.drop (p.rulePrefixAt ri)).take ms.nIdx
  hsty : inferTypeCore mode env F (p.majorIdxAt ri + 1) concl = .ok sty
  hu : ensureSortCore mode env F (p.majorIdxAt ri + 1) sty = .ok u
  /-- the elimination restriction's per-recursor half -/
  hsmall : blockLargeElimAllowed p nested = true ∨
    isDefEqCore mode env F (p.majorIdxAt ri + 1) sty (.sort .zero) = .ok true

namespace RecTyEntry

variable {F : Nat} {env : Env} {p : BlockShape} {nested : Bool} {cvTas : List ConstantVal}
  {ri : Nat} {rc : RecShape} {cvRi : ConstantVal} {nIdx : Nat} {u : Level}

/-- The rule prefix is longer than the parameters. -/
theorem nP_le (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    p.nP ≤ p.rulePrefixAt ri := E.hroom

/-- The major-premise index is the rule prefix plus the index count. -/
theorem mI_eq (E : RecTyEntry mode F env p nested cvTas ri rc cvRi nIdx u) :
    p.majorIdxAt ri = p.rulePrefixAt ri + nIdx := E.hnIdx ▸ E.hmI

end RecTyEntry

/-- **A checked constant's facts** — what every consumer of a recursor
type's check reads, whichever check stored it: `checkConstantVal` (the
stream's type, annotated: `checkConstantVal_checked`) or `classConstOk`
(the GENERATED type, stored as generated: the generated stage's
`classConstOk_inv`).  `cv0` is the constant checked, `cv` the stored
one: the name guards, the stored type closed, its levels declared, its
constants resolved, its inference sorted, and no `.proj` node at an
empty table slot. -/
structure ConstChecked (mode : CheckMode) (F : Nat) (env : Env) (cv0 cv : ConstantVal) :
    Prop where
  name : cv.name = cv0.name
  lps : cv.levelParams = cv0.levelParams
  fresh : env.find? cv0.name = none
  unreserved : reservedBasisNames.contains cv0.name = false
  notProjShape : cv0.name.isProjFnShape = false
  nodup : Name.nodup cv0.levelParams = true
  bounded : cv.type.looseBVarsBounded 0 = true
  noFvar : cv.type.hasFvar = false
  lpsDef : cv.type.allLevelParamsDefined cv.levelParams = true
  resolves : cv.type.constsResolve env = true
  sorted : ∃ stype u, inferTypeCore mode env F 0 cv.type = .ok stype ∧
    ensureSortCore mode env F 0 stype = .ok u
  noProj : ∀ (T : Name) (i : Nat), env.findProj? T i = none → Expr.NoProjAt T i cv.type

/-- **Stage (b) at ONE recursor, at ANY major**: the part
of `RecTyEntry` that does not name the major's inductive — the checked
constant, the prefix and the major's position, the recursor type's
openers, the conclusion's sort and the elimination half.  A nested
block's auxiliary recursor (an OUTSIDE major, a container) has it with
`nIdx` the container's index count. -/
structure RecTyGen (mode : CheckMode) (F : Nat) (env : Env) (p : BlockShape)
    (nested : Bool) (ri : Nat) (rc : RecShape) (cvRi : ConstantVal) (nIdx : Nat) (u : Level) :
    Type where
  fvs : List Expr
  concl : Expr
  maj : Expr
  sty : Expr
  /-- the constant checked: the record's own, or (a generated recursor)
  one under the record's name and level parameters -/
  cv0 : ConstantVal
  hcv0 : cv0.name = rc.cvR.name ∧ cv0.levelParams = rc.cvR.levelParams
  hcv : ConstChecked mode F env cv0 cvRi
  hroom : p.nP ≤ p.rulePrefixAt ri
  hmI' : p.majorIdxAt ri = p.rulePrefixAt ri + nIdx
  hopen : openPisAtFvars (p.majorIdxAt ri + 1) cvRi.type 0 = some (fvs, concl)
  hmaj : fvs[p.majorIdxAt ri]? = some maj
  hsty : inferTypeCore mode env F (p.majorIdxAt ri + 1) concl = .ok sty
  hu : ensureSortCore mode env F (p.majorIdxAt ri + 1) sty = .ok u
  hsmall : blockLargeElimAllowed p nested = true ∨
    isDefEqCore mode env F (p.majorIdxAt ri + 1) sty (.sort .zero) = .ok true

namespace RecTyGen

variable {F : Nat} {env : Env} {p : BlockShape} {nested : Bool}
  {ri : Nat} {rc : RecShape} {cvRi : ConstantVal} {nIdx : Nat} {u : Level}

theorem nP_le (E : RecTyGen mode F env p nested ri rc cvRi nIdx u) :
    p.nP ≤ p.rulePrefixAt ri := E.hroom

theorem mI_eq (E : RecTyGen mode F env p nested ri rc cvRi nIdx u) :
    p.majorIdxAt ri = p.rulePrefixAt ri + nIdx := E.hmI'

theorem name_eq (E : RecTyGen mode F env p nested ri rc cvRi nIdx u) :
    cvRi.name = rc.cvR.name := E.hcv.name.trans E.hcv0.1

theorem lps_eq (E : RecTyGen mode F env p nested ri rc cvRi nIdx u) :
    cvRi.levelParams = rc.cvR.levelParams := E.hcv.lps.trans E.hcv0.2

end RecTyGen

end ConLeche
