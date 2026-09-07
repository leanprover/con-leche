import ConLeche.Kernel.Direct.SumInstallF
import ConLeche.Kernel.Direct.RecInstall

/-!
# The direct recursive install, through the index (task #188)

`checkDirectFix`'s recursor stage (`ConLeche/Kernel/Direct/RecInstall.lean`)
over an `FEnv`, the mirror the cached drivers run; the former's and
the constructors' stages are the sum route's mirrors.
-/

namespace ConLeche

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `directFixOpenedOk` through the index. -/
def directFixOpenedOkF (w : DirectWalkers) (fe₀ : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (cty : Expr) (nF : Nat) (ks : List RecFieldKind) : Bool :=
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (w.resolve fe₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i .ordinary with
        | some x, .ordinary => w.resolve fe₀ x.fvarTypeD
        | some x, .recursive =>
          x.fvarTypeD.getAppFn == Expr.const T (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdx &&
          (x.fvarTypeD.getAppArgs.drop nP).all (w.resolve fe₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, .reflexive =>
          -- the field's own telescope, OPENED at variables at the field's
          -- depth (as the constructor's was): its domains resolve in
          -- `env₀` (so they are free of the block), its body is the family
          -- at the parameter variables and `nIdx` index expressions
          -- resolving in `env₀` (task #202)
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
            afvs.length != 0 &&
            afvs.all (fun a => w.resolve fe₀ a.fvarTypeD) &&
            body.getAppFn == Expr.const T (lps.map .param) &&
            body.getAppArgs.take nP == fvsP &&
            body.getAppArgs.length == nP + nIdx &&
            (body.getAppArgs.drop nP).all (w.resolve fe₀) &&
            !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
            !xrest.mentionsFvar (nP + i)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- `directFixFieldsOk` through the index. -/
def directFixFieldsOkF (w : DirectWalkers) (fe₀ : FEnv) (T : Name) (lps : List Name) (nP nIdx : Nat)
    (ctorsA : List (ConstantVal × Nat)) (kinds : List (List RecFieldKind)) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && directFixOpenedOkF w fe₀ T lps nP nIdx cA.1.type cA.2 ks
    | _, _ => false

/-- `checkDirectFixRules` through the index. -/
def checkDirectFixRulesF (w : DirectWalkers) (feR : FEnv) (rlps : List Name) (T : Name) (lps : List Name)
    (elim : Name) (large : Bool) (nP nIdx : Nat) (tty : Expr)
    (ctors : List (Name × Nat × Expr × List Nat)) (recC : Name) (rlvls : List Level) :
    Nat → Nat → m (List Expr)
  | 0, _ => pure []
  | k + 1, j => do
    let rhs ← unwrapOr (directRecRhsR T lps elim large nP nIdx tty ctors recC rlvls j)
      (.internal "direct rec: recursor rule")
    unless rhs.allLevelParamsDefined rlps && w.resolve feR rhs &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "direct rec: recursor rule scoping")
    let rest ← checkDirectFixRulesF w feR rlps T lps elim large nP nIdx tty ctors recC rlvls k
      (j + 1)
    pure (rhs :: rest)

/-- `checkDirectFixRec` through the index. -/
def checkDirectFixRecF (ops : CheckerOps m) (w : DirectWalkers) (fe : FEnv) (p : DirectFixParts)
    (cvTa : ConstantVal) (ctorsA : List (ConstantVal × Nat)) :
    m (ConstantVal × List Expr) := do
  let cvRi ← checkConstantValF ops fe p.cvR
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  let ctors := directFixCtors4 ctorsA p.kinds
  let recTy ← unwrapOr (directRecTyR T lps p.elim p.large p.nP p.nIdx cvTa.type ctors)
    (.internal "direct rec: recursor type")
  unless recTy.allLevelParamsDefined p.cvR.levelParams && w.resolve fe recTy &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "direct rec: recursor type scoping")
  let sty ← ops.inferType fe.env 0 recTy
  let _u ← ops.ensureSort fe.env 0 sty
  unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
    throw (.invalid "direct rec: recursor type is not the generated one")
  let cvRa : ConstantVal := ⟨p.cvR.name, p.cvR.levelParams, recTy⟩
  let feR := fe.push (.recInfo cvRa p.majorIdx p.rulePrefix [])
  let rhss ← checkDirectFixRulesF w feR p.cvR.levelParams T lps p.elim p.large p.nP p.nIdx
    cvTa.type ctors p.cvR.name (p.cvR.levelParams.map .param) ctors.length 0
  pure (cvRa, rhss)

/-- `checkDirectFixTable` through the index (task #210 Part A). -/
def checkDirectFixTableF (w : DirectWalkers) (p : DirectFixParts) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) (fe : FEnv) : m FEnv :=
  match ctorsA, sortss with
  | [cA], [sorts] =>
    if p.nIdx == 0 then
      checkDirectProjTableF w p.cvT.name cA.1.name p.cvT.levelParams p.nP cA.2 p.resSort
        (directProjGuards cA.1.type p.nP cA.2 sorts) 1 cA.1 fe
    else pure fe
  | _, _ => pure fe

end Mirrors

end ConLeche
