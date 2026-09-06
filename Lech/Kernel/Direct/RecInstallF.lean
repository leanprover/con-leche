import Lech.Kernel.Direct.SumInstallF
import Lech.Kernel.Direct.RecInstall

/-!
# The direct recursive install, through the index (task #188)

`checkDirectFix`'s recursor stage (`Lech/Kernel/Direct/RecInstall.lean`)
over an `FEnv`, the mirror the cached drivers run; the former's and
the constructors' stages are the sum route's mirrors.
-/

namespace Lech

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `directFixFieldsOk` through the index. -/
def directFixFieldsOkF (fe₀ : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 &&
      (match cA.1.type.stripPis (nP + cA.2) with
       | some (cbs, cbody) =>
         (cbody.getAppArgs.drop nP).all (fun a => !a.mentionsConst T) &&
         (List.range cA.2).all fun i =>
           let dom := (cbs.getD (nP + i) default).2.1
           match ks.getD i .ordinary with
           | .ordinary => dom.constsResolveF fe₀
           | .recursive => recFamOk T lps nP nIdx i dom && !directUsedLater cA.1.type nP i
           | _ => false
       | none => false)
    | _, _ => false

/-- `checkDirectFixRules` through the index. -/
def checkDirectFixRulesF (feR : FEnv) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (directRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && rhs.constsResolveF feR &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkDirectFixRulesF feR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- `checkDirectFixRec` through the index. -/
def checkDirectFixRecF (ops : CheckerOps m) (fe : FEnv) (p : DirectFixParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  let cvRi ← checkConstantValF ops fe p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := directFixCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (directRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && recTy.constsResolveF fe &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType fe.env 0 recTy
  let _u ← ops.ensureSort fe.env 0 sty
  unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let feR := fe.push (.recInfo cvRa p.majorIdx p.rulePrefix [])
  let rhss ← checkDirectFixRulesF feR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

end Mirrors

end Lech
