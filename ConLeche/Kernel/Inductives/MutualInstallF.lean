module

public import ConLeche.Kernel.Inductives.NativeInstallF
public import ConLeche.Kernel.Inductives.MutualInstall

@[expose] public section

/-!
# The mutual install, through the index (task #278)

`checkMutualCore`'s stages (`ConLeche/Kernel/Inductives/MutualInstall.lean`)
over an `FEnv`, the mirrors the cached driver runs: the stages that
read the environment — a constant check, a definition check, the
former's telescope, the scoping of the block's records, the stored
block — go through the index; the stages that only run the shared
operations are the pure ones at the index's environment.  The scaffold
installs (`checkNative` on the tag and on the auxiliary family) are the
cached driver's own `checkNativeS`, so the assembly lives there
(`ConLeche/Cached/CheckerC.lean`, `checkMutualCoreS`).
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- `mutualFormers` through the index. -/
def mutualFormersF (ops : CheckerOps m) (fe : FEnv) (nP : Nat) :
    List (ConstantVal × Nat) → m (List MutualFormerA)
  | [] => pure []
  | (cv, nIdx) :: rest => do
    let cvTa₀ ← checkConstantValF ops fe cv
    let (cvTa, s) ← checkSumTeleF ops fe cv (nP + nIdx) cvTa₀
    let fs ← mutualFormersF ops fe nP rest
    pure (⟨cvTa, nIdx, s⟩ :: fs)

/-- `mutualScopeOk` through the index (`w.resolve` at the index with
the block's dummies pushed). -/
def mutualScopeOkF (w : StructWalkers) (fe : FEnv) (b : MutualBlock)
    (streamRecs : Option (List (ConstantVal × List RecRule))) : Bool :=
  let feF : FEnv := b.formers.foldr (fun f acc => acc.push (.indInfo f.1 {})) fe
  let feN : FEnv := b.ctors.foldr (fun c acc => acc.push (.ctorInfo c.cv b.nP c.nF)) feF
  b.ctors.all (fun c => w.resolve feF c.cv.type) &&
  (match streamRecs with
   | none => true
   | some rs =>
     let feR : FEnv := rs.foldr (fun (cvR, _) acc => acc.push (.recInfo cvR 0 0 [])) feN
     rs.all fun (cvR, rules) =>
       w.resolve feR cvR.type && rules.all fun r => w.resolve feR r.rhs)

/-- `mutualDefine` through the index. -/
def mutualDefineF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal) (value : Expr) :
    m (FEnv × ConstantVal) := do
  let cvA ← checkConstantValF ops fe cv
  let fe' ← checkDefnValF ops fe cvA value
    (MutualKit.hintFor (MutualKit.heightOf fe.find?) value)
  pure (fe', cvA)

/-- `mutualDefineFormers` through the index. -/
def mutualDefineFormersF (ops : FEnv → CheckerOps m) (sc : MutualScaffold) (lps : List Name)
    (nP : Nat) : List (MutualFormerA × Nat) → FEnv → m FEnv
  | [], fe => pure fe
  | (f, mIdx) :: rest, fe => do
    let value ← unwrapOr (mutualFormerValue sc lps nP mIdx f) (.internal "mutual: former value")
    let (fe', _) ← mutualDefineF (ops fe) fe ⟨f.cvTa.name, lps, f.cvTa.type⟩ value
    mutualDefineFormersF ops sc lps nP rest fe'

/-- `mutualDefineCtors` through the index. -/
def mutualDefineCtorsF (ops : FEnv → CheckerOps m) (sc : MutualScaffold) (lps : List Name)
    (nP : Nat) : List (MutualCtor × Nat) → FEnv → m (FEnv × List ConstantVal)
  | [], fe => pure (fe, [])
  | (c, J) :: rest, fe => do
    let value ← unwrapOr (mutualCtorValue sc lps nP J c) (.internal "mutual: constructor value")
    let (fe', cvCa) ← mutualDefineF (ops fe) fe c.cv value
    let (fe'', rest') ← mutualDefineCtorsF ops sc lps nP rest fe'
    pure (fe'', cvCa :: rest')

/-- `mutualDefineRec` through the index. -/
def mutualDefineRecF (ops : CheckerOps m) (sc : MutualScaffold) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4) (u : Level) (mIdx nIdx : Nat)
    (streamRec : Option ConstantVal) (fe : FEnv) : m (FEnv × Expr) := do
  let recTy ← unwrapOr (mutualRecTy b.lps b.elim b.large b.nP formers4 ctors4 mIdx)
    (.internal "mutual: recursor type")
  let cvRa ← checkConstantValF ops fe ⟨b.recName mIdx, b.rlps, recTy⟩
  if let some cvR := streamRec then
    let cvRi ← checkConstantValF ops fe cvR
    unless ← ops.isDefEq fe.env 0 cvRi.type cvRa.type do
      throw (.invalid s!"mutual: the type of {cvR.name} is not the generated one")
  let value ← unwrapOr
    (mutualRecValue sc b.lps (b.rlps.map Level.param) u b.elimLevel b.nP b.k b.n mIdx nIdx
      cvRa.type)
    (.internal "mutual: recursor value")
  let fe' ← checkDefnValF ops fe cvRa value
    (MutualKit.hintFor (MutualKit.heightOf fe.find?) value)
  pure (fe', cvRa.type)

/-- `mutualDefineRecs` through the index. -/
def mutualDefineRecsF (ops : FEnv → CheckerOps m) (sc : MutualScaffold) (b : MutualBlock)
    (formers4 : List MutualFormer) (ctors4 : List MutualCtor4) (u : Level)
    (streamRecs : Option (List (ConstantVal × List RecRule))) :
    List (MutualFormerA × Nat) → FEnv → m (FEnv × List Expr)
  | [], fe => pure (fe, [])
  | (f, mIdx) :: rest, fe => do
    let (fe', recTy) ← mutualDefineRecF (ops fe) sc b formers4 ctors4 u mIdx f.nIdx
      (streamRecs.bind fun rs => (rs[mIdx]?).map (·.1)) fe
    let (fe'', tys) ← mutualDefineRecsF ops sc b formers4 ctors4 u streamRecs rest fe'
    pure (fe'', recTy :: tys)

/-- `mutualStore` through the index. -/
def mutualStoreF (fe : FEnv) (b : MutualBlock) (fms : List MutualFormerA)
    (ctorsA : List ConstantVal) (recTys : List Expr)
    (rulesOf : List (List (MutualCtor × Expr))) : FEnv :=
  let fe₁ : FEnv := fms.foldl (fun e f => e.push (.indInfo f.cvTa {})) fe
  let fe₂ : FEnv := (b.ctors.zip ctorsA).foldl
    (fun e (c, cvCa) => e.push (.ctorInfo cvCa b.nP c.nF)) fe₁
  (fms.zipIdx).foldl
    (fun e (f, mIdx) =>
      let recTy := recTys.getD mIdx default
      let rP := b.rulePrefix
      let mI := rP + f.nIdx
      e.push (.recInfo ⟨b.recName mIdx, b.rlps, recTy⟩ mI rP
        (mutualRules fe₂.find? (b.recName mIdx) b.nP mI rP recTy (rulesOf.getD mIdx []))))
    fe₂

/-- `mutualMemberTable` through the index. -/
def mutualMemberTableF (ops : CheckerOps m) (w : StructWalkers) (b : MutualBlock)
    (f : MutualFormerA) (ctorsA : List ConstantVal) (mIdx : Nat) (fe : FEnv) : m FEnv :=
  match b.ownCtors mIdx with
  | [(J, c)] =>
    if f.nIdx == 0 then do
      let cvCa := ctorsA.getD J default
      let (_, crest) ← unwrapOr (openPisAtFvars b.nP cvCa.type 0)
        (.internal "mutual: constructor telescope")
      let (xFvs, _) ← unwrapOr (openPisAtFvars c.nF crest b.nP)
        (.internal "mutual: constructor field telescope")
      let sorts ← checkStructFieldSortsIF ops fe true false f.s b.nP xFvs [] c.nF
      checkStructProjTableF w f.cvTa.name c.cv.name b.lps b.nP c.nF f.s
        (structProjGuards cvCa.type b.nP c.nF sorts) 1 cvCa fe
    else pure fe
  | _ => pure fe

/-- `mutualTables` through the index. -/
def mutualTablesF (ops : FEnv → CheckerOps m) (w : StructWalkers) (b : MutualBlock)
    (ctorsA : List ConstantVal) : List (MutualFormerA × Nat) → FEnv → m FEnv
  | [], fe => pure fe
  | (f, mIdx) :: rest, fe => do
    let fe' ← mutualMemberTableF (ops fe) w b f ctorsA mIdx fe
    mutualTablesF ops w b ctorsA rest fe'

end ConLeche
