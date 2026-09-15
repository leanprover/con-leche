module

public import ConLeche.Kernel.Inductives.NativeInstallF
public import ConLeche.Kernel.Inductives.MutualInstall

@[expose] public section

/-!
# The mutual install, through the index (task #278)

`checkMutualCore`'s stages (`ConLeche/Kernel/Inductives/MutualInstall.lean`)
over an `FEnv`, the mirrors the cached driver runs
(`ConLeche/Cached/CheckerC.lean`, `checkMutualCoreS`): every
environment lookup through the index, the constant-resolution gate
through the walkers.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- `mutualFormerChecks` through the index: every former checked at
the pre-block index. -/
def mutualFormerChecksF (ops : FEnv → CheckerOps m) (fe : FEnv) (nP : Nat) :
    List (ConstantVal × Nat) → m (List MutualFormerA)
  | [] => pure []
  | (cv, nIdx) :: rest => do
    let cvTa₀ ← checkConstantValF (ops fe) fe cv
    let (cvTa, s) ← checkSumTeleF (ops fe) fe cv (nP + nIdx) cvTa₀
    let (_, tbody) ← unwrapOr (cvTa.type.stripPis (nP + nIdx))
      (.internal "mutual: type former telescope")
    unless tbody == Expr.sort s do
      throw (.internal "mutual: type former result sort")
    let fs ← mutualFormerChecksF ops fe nP rest
    pure (⟨cvTa, nIdx, s⟩ :: fs)

/-- `consMutualFormers` through the index. -/
def consMutualFormersF : List MutualFormerA → FEnv → FEnv
  | [], fe => fe
  | f :: fs, fe => consMutualFormersF fs (fe.push (.indInfo f.cvTa {}))

/-- `mutualFormers` through the index. -/
def mutualFormersF (ops : FEnv → CheckerOps m) (nP : Nat)
    (formers : List (ConstantVal × Nat)) (fe : FEnv) : m (FEnv × List MutualFormerA) := do
  let fms ← mutualFormerChecksF ops fe nP formers
  pure (consMutualFormersF fms fe, fms)

/-- `normCtorValM` through the index. -/
def normCtorValMF (ops : CheckerOps m) (fe : FEnv) (memberNames : List Name) (nP nF : Nat)
    (cvC cvCa : ConstantVal) : m ConstantVal := do
  let (cbs, _) ← unwrapOr (cvCa.type.stripPis nP)
    (.notImplemented "mutual: constructor telescope")
  let (fvsP, crest) ← unwrapOr (openPisAtFvars nP cvCa.type 0)
    (.notImplemented "mutual: constructor telescope")
  let pbs := List.zipWith (fun (x : Expr) (b : Expr × BinderMeta) => (x.fvarTypeD, b.2)) fvsP cbs
  let (fbs, resid) ← normFieldDomsM ops fe.env memberNames nP nF crest
  let ty' := closeTelescope (pbs ++ fbs) 0 resid
  if ty' == cvCa.type then pure cvCa
  else checkConstantValF ops fe { cvC with type := ty' }

/-- `checkMutualCtor` through the index. -/
def checkMutualCtorF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv)
    (memberNames : List Name) (T : Name) (lps : List Name) (nP nIdx : Nat) (resSort : Level)
    (isProp large : Bool) (cvC : ConstantVal) (nF : Nat) (cvTa : ConstantVal) :
    m (ConstantVal × List Level) := do
  let cvCa₀ ← checkConstantValF ops fe cvC
  let cvCa ← normCtorValMF ops fe memberNames nP nF cvC cvCa₀
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (nP + nF))
    (.notImplemented "mutual: constructor telescope")
  unless structCtorResidOk T lps nP nF nIdx cbody do
    throw (.invalid "mutual: invalid constructor return type")
  let cq ← unwrapOr (openPisAtFvarsF nP cvCa.type 0)
    (.notImplemented "mutual: constructor telescope")
  let tq ← unwrapOr (openPisAtFvarsF nP cvTa.type 0)
    (.notImplemented "mutual: type former telescope")
  checkStructDomsAtFA ops fe 0 cq.1.toArray (tq.1.map Expr.fvarTypeD).toArray nP
  let xq ← unwrapOr (openPisAtFvarsF nF cq.2 nP)
    (.notImplemented "mutual: constructor field telescope")
  unless xq.2.getAppFn == Expr.const T (lps.map .param) &&
      xq.2.getAppArgs.take nP == cq.1 && xq.2.getAppArgs.length == nP + nIdx do
    throw (.notImplemented "mutual: opened constructor residual")
  unless xq.1.all fun x => w.resolve fe x.fvarTypeD do
    throw (.notImplemented "mutual: field domain after the block")
  unless (xq.2.getAppArgs.drop nP).all fun e => w.resolve fe e do
    throw (.invalid "mutual: index expression mentions an unknown constant")
  let sorts ← checkStructFieldSortsIFA ops fe isProp large resSort nP xq.1.toArray
    (xq.2.getAppArgs.drop nP) nF
  pure (cvCa, sorts)

/-- `checkMutualCtors` through the index. -/
def checkMutualCtorsF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (b : MutualBlock)
    (fms : List MutualFormerA) (isProp : Bool) :
    List MutualCtor → m (List (ConstantVal × Nat) × List (List Level))
  | [] => pure ([], [])
  | c :: cs => do
    let f := fms.getD c.member default
    let (cvCa, sorts) ← checkMutualCtorF ops w fe b.memberNames f.cvTa.name b.lps b.nP f.nIdx
      f.s isProp b.large c.cv c.nF f.cvTa
    let (rest, srest) ← checkMutualCtorsF ops w fe b fms isProp cs
    pure ((cvCa, c.nF) :: rest, sorts :: srest)

/-- `mutualOpenedOk` through the index. -/
def mutualOpenedOkF (w : StructWalkers) (fe₀ : FEnv) (members : List (Name × Nat × Nat))
    (lps : List Name) (nP : Nat) (cty : Expr) (nF : Nat) (ks : List (RecFieldKind × Nat)) :
    Bool :=
  let nIdxOf : Nat → Nat := fun m' => ((members.find? (·.2.1 == m')).map (·.2.2)).getD 0
  let nameOf : Nat → Name := fun m' => ((members.find? (·.2.1 == m')).map (·.1)).getD .anonymous
  match openPisAtFvars nP cty 0 with
  | some (fvsP, crest) =>
    match openPisAtFvars nF crest nP with
    | some (xFvs, xrest) =>
      (xrest.getAppArgs.drop nP).all (w.resolve fe₀) &&
      (List.range nF).all fun i =>
        match xFvs[i]?, ks.getD i (.ordinary, 0) with
        | some x, (.ordinary, _) => w.resolve fe₀ x.fvarTypeD
        | some x, (.recursive, m') =>
          x.fvarTypeD.getAppFn == Expr.const (nameOf m') (lps.map .param) &&
          x.fvarTypeD.getAppArgs.take nP == fvsP &&
          x.fvarTypeD.getAppArgs.length == nP + nIdxOf m' &&
          (x.fvarTypeD.getAppArgs.drop nP).all (w.resolve fe₀) &&
          !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
          !xrest.mentionsFvar (nP + i)
        | some x, (.reflexive, m') =>
          match openPisAtFvars (x.fvarTypeD.piBinders).1.length x.fvarTypeD (nP + i) with
          | some (afvs, body) =>
            afvs.length != 0 &&
            afvs.all (fun a => w.resolve fe₀ a.fvarTypeD) &&
            body.getAppFn == Expr.const (nameOf m') (lps.map .param) &&
            body.getAppArgs.take nP == fvsP &&
            body.getAppArgs.length == nP + nIdxOf m' &&
            (body.getAppArgs.drop nP).all (w.resolve fe₀) &&
            !(xFvs.drop (i + 1)).any (fun y => y.fvarTypeD.mentionsFvar (nP + i)) &&
            !xrest.mentionsFvar (nP + i)
          | none => false
        | _, _ => false
    | none => false
  | none => false

/-- `mutualFieldsOk` through the index. -/
def mutualFieldsOkF (w : StructWalkers) (fe₀ : FEnv) (members : List (Name × Nat × Nat))
    (lps : List Name) (nP : Nat) (ctorsA : List (ConstantVal × Nat))
    (kinds : List (List (RecFieldKind × Nat))) : Bool :=
  ctorsA.length == kinds.length &&
  (List.range ctorsA.length).all fun j =>
    match ctorsA[j]?, kinds[j]? with
    | some cA, some ks =>
      ks.length == cA.2 && mutualOpenedOkF w fe₀ members lps nP cA.1.type cA.2 ks
    | _, _ => false

/-- `consMutualCtors` through the index. -/
def consMutualCtorsF (nP : Nat) : List (ConstantVal × Nat) → FEnv → FEnv
  | [], fe => fe
  | c :: cs, fe => consMutualCtorsF nP cs (fe.push (.ctorInfo c.1 nP c.2))

/-- `checkMutualRecTy` through the index. -/
def checkMutualRecTyF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4) (mIdx : Nat)
    (streamRec : Option ConstantVal) : m ConstantVal := do
  let recTy ← unwrapOr (mutualRecTy b.lps b.elim b.large b.nP formers4 ctors4 mIdx)
    (.internal "mutual: recursor type")
  unless recTy.allLevelParamsDefined b.rlps && w.resolve fe recTy &&
      recTy.looseBVarsBounded 0 && !recTy.hasFvar do
    throw (.internal "mutual: recursor type scoping")
  let sty ← ops.inferType fe.env 0 recTy
  let _u ← ops.ensureSort fe.env 0 sty
  if let some cvR := streamRec then
    let cvRi ← checkConstantValF ops fe cvR
    unless ← ops.isDefEq fe.env 0 cvRi.type recTy do
      throw (.invalid s!"mutual: the type of {cvR.name} is not the generated one")
  pure ⟨b.recName mIdx, b.rlps, recTy⟩

/-- `checkMutualRecTys` through the index. -/
def checkMutualRecTysF (ops : CheckerOps m) (w : StructWalkers) (fe : FEnv) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
    (streamRecs : Option (List (ConstantVal × List RecRule))) :
    Nat → m (List ConstantVal)
  | 0 => pure []
  | mIdx' + 1 => do
    let earlier ← checkMutualRecTysF ops w fe b formers4 ctors4 streamRecs mIdx'
    let cvRa ← checkMutualRecTyF ops w fe b formers4 ctors4 mIdx'
      (streamRecs.bind fun rs => (rs[mIdx']?).map (·.1))
    pure (earlier ++ [cvRa])

/-- `provisionMutualRecs` through the index. -/
def provisionMutualRecsF (b : MutualBlock) (fms : List MutualFormerA) :
    List (ConstantVal × Nat) → FEnv → FEnv
  | [], fe => fe
  | (cvRa, mIdx) :: rest, fe =>
    let rP := b.rulePrefix
    let mI := rP + (fms.getD mIdx default).nIdx
    provisionMutualRecsF b fms rest (fe.push (.recInfo cvRa mI rP []))

/-- `checkMutualMemberRules` through the index. -/
def checkMutualMemberRulesF (w : StructWalkers) (feR : FEnv) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4) (mIdx : Nat)
    (streamRec : Option (ConstantVal × List RecRule)) : m (List (MutualCtor × Expr)) := do
  let recOf : Nat → Name := b.recName
  let rlvls := b.rlps.map Level.param
  let own := b.ownCtors mIdx
  if let some (cvR, rules) := streamRec then
    unless mutualRulesOk recOf rlvls b.nP b.k b.n ctors4 (own.map (·.1)) (rules.map (·.rhs))
        cvR.type do
      throw (.invalid s!"mutual: the rules of {cvR.name} are not the generated ones")
  own.mapM fun (J, c) => do
    let rhs ← unwrapOr (mutualRecRhs b.lps b.elim b.large b.nP formers4 ctors4 recOf rlvls J)
      (.internal "mutual: recursor rule")
    unless rhs.allLevelParamsDefined b.rlps && w.resolve feR rhs &&
        rhs.looseBVarsBounded 0 && !rhs.hasFvar do
      throw (.internal "mutual: recursor rule scoping")
    pure (c, rhs)

/-- `checkMutualAllRules` through the index. -/
def checkMutualAllRulesF (w : StructWalkers) (feR : FEnv) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4)
    (streamRecs : Option (List (ConstantVal × List RecRule))) :
    Nat → m (List (List (MutualCtor × Expr)))
  | 0 => pure []
  | mIdx' + 1 => do
    let earlier ← checkMutualAllRulesF w feR b formers4 ctors4 streamRecs mIdx'
    let rules ← checkMutualMemberRulesF w feR b formers4 ctors4 mIdx'
      (streamRecs.bind (·[mIdx']?))
    pure (earlier ++ [rules])

/-- `storeMutualRecs` through the index. -/
def storeMutualRecsF (fe₂ : FEnv) (b : MutualBlock) (fms : List MutualFormerA)
    (rulesOf : List (List (MutualCtor × Expr))) : List (ConstantVal × Nat) → FEnv → FEnv
  | [], fe => fe
  | (cvRa, mIdx) :: rest, fe =>
    let rP := b.rulePrefix
    let mI := rP + (fms.getD mIdx default).nIdx
    storeMutualRecsF fe₂ b fms rulesOf rest
      (fe.push (.recInfo cvRa mI rP (mutualRules fe₂.find? cvRa.name b.nP mI rP cvRa.type
          (rulesOf.getD mIdx []))))

/-- `mutualMemberTable` through the index. -/
def mutualMemberTableF (w : StructWalkers) (b : MutualBlock) (f : MutualFormerA)
    (ctorsA : List (ConstantVal × Nat)) (sortss : List (List Level)) (mIdx : Nat) (fe : FEnv) :
    m FEnv :=
  match b.ownCtors mIdx with
  | [(J, c)] =>
    if f.nIdx == 0 then
      let cvCa := (ctorsA.getD J default).1
      checkStructProjTableF w f.cvTa.name c.cv.name b.lps b.nP c.nF f.s
        (structProjGuards cvCa.type b.nP c.nF (sortss.getD J [])) 1 cvCa fe
    else pure fe
  | _ => pure fe

/-- `mutualTables` through the index. -/
def mutualTablesF (w : StructWalkers) (b : MutualBlock) (ctorsA : List (ConstantVal × Nat))
    (sortss : List (List Level)) : List (MutualFormerA × Nat) → FEnv → m FEnv
  | [], fe => pure fe
  | (f, mIdx) :: rest, fe => do
    let fe' ← mutualMemberTableF w b f ctorsA sortss mIdx fe
    mutualTablesF w b ctorsA sortss rest fe'

end ConLeche
