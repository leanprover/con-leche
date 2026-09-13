module

public import ConLeche.Kernel.Inductives.NestedInstall
public import ConLeche.Kernel.DeclCheck
public import ConLeche.Kernel.Inductives.SumInstallF
public import ConLeche.Kernel.Inductives.StructInstallF

@[expose] public section

/-!
# The nested install, through the index (task #279 K.20)

`checkNested`'s stages (`ConLeche/Kernel/Inductives/NestedInstall.lean`)
over an `FEnv`, the mirrors the cached driver runs
(`ConLeche/Cached/CheckerC.lean`, `checkNestedS`).

**What is mirrored and what is not.**  The per-constant front doors are
the hot lookups, so they go through the index (`checkConstantValF`,
`checkConstantValPreF`, `checkSumTeleF`, `checkStructProjTableF`), and
so does every CONS (`FEnv.push` keeps the index and the environment in
step).  The route's own pure readers — the elimination, the container
recovery, the read-back, the restore table, the fire shape — keep taking
the `Env`, which the cached driver passes as `fe.env`: they run a
handful of times per nested block (41 in all of Mathlib), where the
front doors run once per stored constant, and the mutual mirror already
does the same for `mutualCrossChecks`.  `nestedPinsOk` and
`nestedCtorsWhnfOk` take no lookup at all — only `ops` — so they are
shared verbatim.
-/

namespace ConLeche

variable {m : Type -> Type} [Monad m] [MonadExceptOf CheckError m]

/-- `nestedAnnotFormers` through the index. -/
def nestedAnnotFormersF (ops : CheckerOps m) (fe : FEnv) (nP : Nat) :
    List (ConstantVal × Nat) → m (List ConstantVal)
  | [] => pure []
  | (cv, nIdx) :: rest => do
    let cvTa₀ ← checkConstantValF ops fe cv
    let (cvTa, _s) ← checkSumTeleF ops fe cv (nP + nIdx) cvTa₀
    let restA ← nestedAnnotFormersF ops fe nP rest
    pure (cvTa :: restA)

/-- `nestedFormerEnv` through the index. -/
def nestedFormerEnvF : List ConstantVal → FEnv → FEnv
  | [], fe => fe
  | cv :: cvs, fe => nestedFormerEnvF cvs (fe.push (.indInfo cv {}))

/-- `nestedAnnotCtors` through the index. -/
def nestedAnnotCtorsF (ops : CheckerOps m) (feF : FEnv) :
    List MutualCtor → m (List ConstantVal)
  | [] => pure []
  | c :: rest => do
    let cvCa ← checkConstantValF ops feF c.cv
    let restA ← nestedAnnotCtorsF ops feF rest
    pure (cvCa :: restA)

/-- `consNestedFormers` through the index. -/
def consNestedFormersF : List AuxStored → FEnv → FEnv
  | [], fe => fe
  | a :: rest, fe => consNestedFormersF rest (fe.push (.indInfo a.cvTa a.caps))

/-- `consNestedCtors` through the index. -/
def consNestedCtorsF : List (ConstantVal × Nat × Nat) → FEnv → FEnv
  | [], fe => fe
  | (cv, nP, nF) :: cs, fe => consNestedCtorsF cs (fe.push (.ctorInfo cv nP nF))

/-- `provisionNestedRecs` through the index. -/
def provisionNestedRecsF : List (ConstantVal × Nat × Nat) → FEnv → FEnv
  | [], fe => fe
  | (cvRa, mI, rP) :: rest, fe =>
    provisionNestedRecsF rest (fe.push (.recInfo cvRa mI rP []))

/-- `storeNestedRecs` through the index. -/
def storeNestedRecsF : List (ConstantVal × Nat × Nat × List RecRule) → FEnv → FEnv
  | [], fe => fe
  | (cvRa, mI, rP, rules) :: rest, fe =>
    storeNestedRecsF rest (fe.push (.recInfo cvRa mI rP rules))

/-- `restoreCtors` through the index. -/
def restoreCtorsF (ops : CheckerOps m) (fe : FEnv) (R : RestoreTbl) (lps : List Name) :
    List (ConstantVal × Nat × Nat) → m (List (ConstantVal × Nat × Nat))
  | [] => pure []
  | (cvCa, nP, nF) :: rest => do
    let ty ← nestedLift (restoreNested R cvCa.type)
    let cvA ← checkConstantValPreF ops fe { cvCa with levelParams := lps, type := ty }
    let rest' ← restoreCtorsF ops fe R lps rest
    pure ((cvA, nP, nF) :: rest')

/-- `restoreRecTys` through the index. -/
def restoreRecTysF (ops : CheckerOps m) (fe : FEnv) (R : RestoreTbl) (lps : List Name)
    (names : List Name) : List AuxStored → m (List ConstantVal)
  | [] => pure []
  | a :: rest => do
    let nm := names.headD a.cvRa.name
    let ty ← nestedLift (restoreNested R a.cvRa.type)
    let cvA ← checkConstantValPreF ops fe ⟨nm, a.cvRa.levelParams, ty⟩
    let rest' ← restoreRecTysF ops fe R lps (names.drop 1) rest
    pure (cvA :: rest')

/-- `restoreRules` through the index: the scope tests through the
walkers, the lookups through `fe.find?`. -/
def restoreRulesF (ops : CheckerOps m) (feR : FEnv) (R : RestoreTbl) (lps : List Name)
    (recName : Name) (isMimic : Bool) (recTy : Expr) (mI rP : Nat) :
    List RecRule → m (List RecRule)
  | [] => pure []
  | rl :: rest => do
    let rhsA ← nestedLift (restoreNested R rl.rhs)
    unless rhsA.allLevelParamsDefined lps && rhsA.constsResolveF feR &&
        rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
      throw (.invalid s!"nested: the restored rule of {recName} does not scope")
    unless rhsA.projTablesOkF feR do
      throw (.invalid "invalid projection: the node names another structure")
    let _ty ← ops.inferType feR.env 0 rhsA
    let ctor : Name :=
      if isMimic then
        match R.ctorPins.find? (fun q => q.1 == rl.ctor) with
        | some (_, _, nm) => nm
        | none => rl.ctor
      else rl.ctor
    unless !isMimic || (R.ctorPins.any fun q => q.1 == rl.ctor) do
      throw (.invalid s!"failed to restore nested inductive types, '{rl.ctor}' is not a \
        constructor of an auxiliary type")
    let cnP : Nat :=
      match feR.find? ctor with
      | some (.ctorInfo _ n _) => n
      | _ => rl.ctorParams
    let fire : RecRuleFire :=
      if isMimic then
        match nestedFireShape feR.env lps recTy mI rP cnP with
        | some (lvls, pins) => .nested lvls pins
        | none => .inert
      else if Expr.recRulePlain recTy mI rP cnP then .plain else .inert
    let rest' ← restoreRulesF ops feR R lps recName isMimic recTy mI rP rest
    pure (recRuleBits feR.find? recName
      { rl with ctor := ctor, ctorParams := cnP, fire := fire, rhs := rhsA,
                paramsBlind := !isMimic } :: rest')

/-- `nestedMemberTable` through the index. -/
def nestedMemberTableF (w : StructWalkers) (T : Name) (tbl? : Option ProjTable)
    (ctors : List (ConstantVal × Nat × Nat)) (fe : FEnv) : m FEnv :=
  match tbl?, ctors with
  | some tbl, [(cvCa, nP, nF)] =>
    checkStructProjTableF w T tbl.ctor tbl.levelParams nP nF tbl.structSort tbl.guards
      tbl.off cvCa fe
  | _, _ => pure fe

/-- `nestedTables` through the index. -/
def nestedTablesF (w : StructWalkers) :
    List (Name × Option ProjTable × List (ConstantVal × Nat × Nat)) → FEnv → m FEnv
  | [], fe => pure fe
  | (T, tbl?, cs) :: rest, fe => do
    let fe' ← nestedMemberTableF (m := m) w T tbl? cs fe
    nestedTablesF w rest fe'

/-- `nestedRecOk` through the index. -/
def nestedRecOkF (ops : CheckerOps m) (fe : FEnv) (nP k n : Nat)
    (streamRec : ConstantVal × List RecRule) (own : List (Nat × Nat))
    (cvRa : ConstantVal) (rules : List RecRule) : m Unit := do
  let (cvR, srules) := streamRec
  unless cvR.name == cvRa.name && cvR.levelParams == cvRa.levelParams do
    throw (.invalid s!"nested: {cvR.name} is not the generated recursor")
  let cvRi ← checkConstantValF ops fe cvR
  unless ← ops.isDefEq fe.env 0 cvRi.type cvRa.type do
    throw (.invalid s!"nested: the type of {cvR.name} is not the generated one")
  unless nestedRulesOk nP k n cvRi.type own srules rules do
    throw (.invalid s!"nested: the rules of {cvR.name} are not the generated ones")

/-- `nestedRecsOk` through the index. -/
def nestedRecsOkF (ops : CheckerOps m) (fe : FEnv) (nP k n : Nat) :
    List ((ConstantVal × List RecRule) × List (Nat × Nat) × ConstantVal × List RecRule) →
      m Unit
  | [] => pure ()
  | (sr, own, cvRa, rules) :: rest => do
    nestedRecOkF ops fe nP k n sr own cvRa rules
    nestedRecsOkF ops fe nP k n rest

end ConLeche
