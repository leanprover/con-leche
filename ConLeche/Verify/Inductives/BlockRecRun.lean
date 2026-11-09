module

public import ConLeche.Kernel.Inductives.BlockInstall
import ConLeche.Verify.Inductives.BlockWF
import ConLeche.Verify.ExceptBind
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Shift

public section

/-!
# Stage (b)'s record

`RecTyGen`: one recursor's type as checked at ANY major — the checked
constant, the prefix and the major's position, the recursor type's
openers, the conclusion's sort and the elimination half.  The stage
record `RecStage` hands it out per recursor (`tyGen`).
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

/-- **A checked constant's facts** — what every consumer of a recursor
type's check reads, whichever check stored it: `checkConstantVal` (the
stream's type, as declared: `checkConstantVal_checked`) or `classConstOk`
(the GENERATED type, stored as generated: the generated stage's
`classConstOk_inv`).  `cv0` is the constant checked, `cv` the stored
one: the name guards, the stored type closed, its levels declared, its
constants resolved, its inference sorted. -/
structure ConstChecked (mode : CheckMode) (F : Nat) (env : Env) (cv0 cv : ConstantVal) :
    Prop where
  name : cv.name = cv0.name
  lps : cv.levelParams = cv0.levelParams
  fresh : env.find? cv0.name = none
  nodup : Name.nodup cv0.levelParams = true
  bounded : cv.type.looseBVarsBounded 0 = true
  noFvar : cv.type.hasFvar = false
  lpsDef : cv.type.allLevelParamsDefined cv.levelParams = true
  resolves : cv.type.constsResolve env = true
  sorted : ∃ stype u, inferTypeCore mode false env F 0 cv.type = .ok stype ∧
    ensureSortCore mode false env F 0 stype = .ok u

/-- **Stage (b) at ONE recursor, at ANY major**: the checked constant,
the prefix and the major's position, the recursor type's openers, the
conclusion's sort and the elimination half.  A nested block's auxiliary
recursor (an OUTSIDE major, a container) has it with `nIdx` the
container's index count. -/
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
  hsty : inferTypeCore mode false env F (p.majorIdxAt ri + 1) concl = .ok sty
  hu : ensureSortCore mode false env F (p.majorIdxAt ri + 1) sty = .ok u
  hsmall : blockLargeElimAllowed p nested = true ∨
    isDefEqCore mode false env F (p.majorIdxAt ri + 1) sty (.sort .zero) = .ok true

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
