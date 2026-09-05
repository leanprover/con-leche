import Setlec.Kernel.Checker
import Setlec.Kernel.FEnv

/-!
# The declaration checker through the environment index (task #63)

The `FEnv`-indexed guard twins and the `F`-mirrors of every
`Setlec/Kernel/Checker.lean` declaration-level function.  Each mirror
is its generic counterpart with every environment lookup
(`Env.find?`, `Env.findCV?`, `Expr.constsResolve` and the compound
guards built from them) routed through the index; under `mkFEnv` the
two are equal (`Setlec/Verify/CheckerF.lean`), and environment-
extending mirrors return the pushed index (`FEnv.push`, definitionally
`mkFEnv` of the cons-extended environment).

**Representation-free.**  Everything here is `Expr`-typed and
monad-polymorphic over `CheckerOps m`: no core, no state, no
expression representation.  Both executable drivers instantiate these
same functions.

It lived in `Setlec/Kernel/CheckerS.lean` until task #172's interned
removal took that file's shared-state drivers with the arena.
-/

namespace Setlec

variable (mode : CheckMode)

/-- Indexed `Env.findCV?`. -/
def FEnv.findCV? (fe : FEnv) (n : Name) : Option ConstantVal :=
  (fe.find? n).map (·.toConstantVal)

/-- Indexed `Expr.constsResolve` (same clauses, lookups through the
index). -/
def Expr.constsResolveF (fe : FEnv) : Expr → Bool
  | .bvar _ | .sort _ => true
  | .lit (.natVal _) =>
    (fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome
  | .lit (.strVal _) =>
    (fe.find? natName).isSome && (fe.find? natZeroName).isSome &&
      (fe.find? natSuccName).isSome && (fe.find? stringName).isSome &&
      (fe.find? stringOfListName).isSome && (fe.find? listName).isSome &&
      (fe.find? listNilName).isSome && (fe.find? listConsName).isSome &&
      (fe.find? charName).isSome && (fe.find? charOfNatName).isSome
  | .const n _ => (fe.find? n).isSome
  | .fvar _ _ ty => ty.constsResolveF fe
  | .app f a => f.constsResolveF fe && a.constsResolveF fe
  | .lam _ ty body _ | .forallE _ ty body _ =>
    ty.constsResolveF fe && body.constsResolveF fe
  | .letE _ ty val body =>
    ty.constsResolveF fe && val.constsResolveF fe &&
      body.constsResolveF fe
  | .proj s _ e => (fe.find? s).isSome && e.constsResolveF fe

/-! ## Indexed guard twins (same result as the `Env` versions under
`mkFEnv`; agreement lemmas in `Setlec/Verify/CheckerF.lean`) -/

/-- `natOpCod` through the index. -/
def natOpCodF (fe : FEnv) (c : Name) (e : Expr) : Bool :=
  if c = natBeqName || c = natBleName then
    e == .const boolName [] &&
    (match fe.find? boolName with
     | some ci => ci.toConstantVal.levelParams.isEmpty &&
         ci.toConstantVal.type == .sort (.succ .zero)
     | none => false)
  else e == .const natName []

/-- `natOpTyPinned` through the index. -/
def natOpTyPinnedF (fe : FEnv) (c : Name) (ty : Expr) : Bool :=
  if c = natPredName || c = natLog2Name then
    match ty with
    | .forallE _ dom body _mb =>
      dom == .const natName [] && natOpCodF fe c body
    | _ => false
  else
    match ty with
    | .forallE _ dom (.forallE _ dom2 body _mb2) _mb =>
      dom == .const natName [] && dom2 == .const natName [] &&
      natOpCodF fe c body
    | _ => false

/-- `natOpStoredOk` through the index. -/
def natOpStoredOkF (fe : FEnv) (n : Name) : Bool :=
  match fe.find? n with
  | some (.defnInfo cv _ _) =>
    cv.levelParams.isEmpty && natOpTyPinnedF fe n cv.type
  | _ => false

/-- `stdAxiomOk` through the index. -/
def stdAxiomOkF (fe : FEnv) (cvA : ConstantVal) : Bool :=
  if cvA.name = propextName then
    decide (fe.find? eqName = some eqA) &&
    (match fe.find? iffName with
     | some (.indInfo cvI _) => ConstantVal.matchesPin cvI iffA.toConstantVal
     | _ => false) &&
    (match fe.find? iffIntroName with
     | some (.ctorInfo cvIi 2 2) =>
       ConstantVal.matchesPin cvIi iffIntroA.toConstantVal
     | _ => false) &&
    (match fe.find? iffRecName with
     | some (.recInfo cvIr 4 4 _) =>
       ConstantVal.matchesPin cvIr iffRecA.toConstantVal
     | _ => false) &&
    ConstantVal.matchesPin cvA propextA
  else if cvA.name = choiceName then
    (match fe.find? nonemptyName with
     | some (.indInfo cvN _) =>
       ConstantVal.matchesPin cvN nonemptyA.toConstantVal
     | _ => false) &&
    (match fe.find? nonemptyIntroName with
     | some (.ctorInfo cvNi 1 1) =>
       ConstantVal.matchesPin cvNi nonemptyIntroA.toConstantVal
     | _ => false) &&
    (match fe.find? nonemptyRecName with
     | some (.recInfo cvNr 3 3 _) =>
       ConstantVal.matchesPin cvNr nonemptyRecA.toConstantVal
     | _ => false) &&
    ConstantVal.matchesPin cvA choiceA
  else false

/-- `trustCompilerOk` through the index. -/
def trustCompilerOkF (fe : FEnv) (cvA : ConstantVal) : Bool :=
  (match fe.find? trueName with
   | some (.indInfo cvT _) => ConstantVal.matchesPin cvT trueCvA
   | _ => false) &&
  (match fe.find? trueIntroName with
   | some (.ctorInfo cvTi 0 0) => ConstantVal.matchesPin cvTi trueIntroCvA
   | _ => false) &&
  ConstantVal.matchesPin cvA trustCompilerA

/-- `reduceStoredOk` through the index. -/
def reduceStoredOkF (fe : FEnv) (c : Name) : Bool :=
  match fe.find? c with
  | some (.axiomInfo cvR) => ConstantVal.matchesPin cvR (reduceOpCvA c)
  | _ => false

/-- `reduceElemOk` through the index. -/
def reduceElemOkF (fe : FEnv) (c : Name) : Bool :=
  if c = reduceNatName then decide (fe.find? natName = some natA)
  else
    match fe.find? boolName with
    | some (.indInfo cvB _) => ConstantVal.matchesPin cvB boolCvA
    | _ => false

/-- `ofReduceAxOk` through the index. -/
def ofReduceAxOkF (fe : FEnv) (cvA : ConstantVal) : Bool :=
  let c := ofReduceOp cvA.name
  decide (fe.find? eqName = some eqA) &&
  reduceElemOkF fe c &&
  reduceStoredOkF fe c &&
  ConstantVal.matchesPin cvA (ofReducePinA cvA.name)

/-- `reducePinGuard` through the index. -/
def reducePinGuardF (fe : FEnv) (c : Name) : Bool :=
  (reduceDeclPin c).looseBVarsBounded 0 && !(reduceDeclPin c).hasFvar &&
  (reduceDeclPin c).allLevelParamsDefined [] &&
  (reduceDeclPin c).constsResolveF fe

/-- `divModEnvGuard` through the index. -/
def divModEnvGuardF (fe2 : FEnv) (c : Name) : Bool :=
  natOpGuardF fe2 c && (natOpDeps c).all (natOpStoredOkF fe2) &&
  fe2.find? eqName == some eqA &&
  (match fe2.find? boolTrueName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false) &&
  (match fe2.find? boolFalseName with
    | some ci => ci.toConstantVal.type == .const boolName []
    | none => false)

/-- `divModCertGuard` through the index. -/
def divModCertGuardF (fe : FEnv) (c : Name) (annVal : Expr)
    (hyps : List Expr) (eqE proof : Expr) : Bool :=
  (Expr.substConstAll c annVal proof).looseBVarsBounded 0 &&
  !(Expr.substConstAll c annVal proof).hasFvar &&
  (Expr.substConstAll c annVal proof).allLevelParamsDefined [] &&
  (Expr.substConstAll c annVal proof).constsResolveF fe &&
  (hyps.map (Expr.substConst0 c annVal)).all
    (fun h => h.constsResolveF fe) &&
  (Expr.substConst0 c annVal eqE).constsResolveF fe

/-- `divModPinGuard` through the index. -/
def divModPinGuardF (fe : FEnv) (c : Name) : Bool :=
  (divModDeclPin c).looseBVarsBounded 0 && !(divModDeclPin c).hasFvar &&
  (divModDeclPin c).allLevelParamsDefined [] &&
  (divModDeclPin c).constsResolveF fe

/-- `divModCertsGuard` through the index. -/
def divModCertsGuardF (fe : FEnv) (c : Name) (annVal : Expr) : Bool :=
  ((divModCertStmts c).zip (divModCertProofs c)).all
    (fun p => divModCertGuardF fe c annVal p.1.1 p.1.2 p.2)

/-- `checkEtaThm` through the index. -/
def checkEtaThmF (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) : Bool :=
  match fe.find? ((T.str "_model").str "eta"),
      fe.find? (T.str "_model"),
      fe.find? (ctorName.str "_model"), fe.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _ _),
      some (.defnInfo cvmC _ _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps && cvmC.levelParams == lps &&
    (List.range nF).all (fun j =>
      match fe.find? (projModelName T j) with
      | some (.defnInfo cvmj _ _) => cvmj.levelParams == lps
      | _ => false) &&
    (match tcv.type.stripPis (nP + 1), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, tbodyM) =>
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (_, xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 0 &&
          tySlot == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - k)) &&
          rhsC == Expr.mkAppN
            (.const (ctorName.str "_model") (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
             (List.range nF).map fun j => Expr.mkAppN
               (.const (projModelName T j) (lps.map .param))
               (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                [Expr.bvar 0])) &&
          -- TT-lane check (task #147): skipped unless `mode.ttChecks`
          (!mode.ttChecks || tbodyM == Expr.sort ℓA)
        | _ => false)
     | _, _ => false)
  | _, _, _, _ => false

/-- `checkUnitThm` through the index. -/
def checkUnitThmF (fe : FEnv) (T : Name) (lps : List Name)
    (nP : Nat) : Bool :=
  match fe.find? ((T.str "_model").str "unitlike"),
      fe.find? (T.str "_model"), fe.find? eqName with
  | some (.thmInfo tcv _), some (.defnInfo cvmT _ _), some eqStored =>
    eqStored == eqA && tcv.levelParams == lps &&
    cvmT.levelParams == lps &&
    (match tcv.type.stripPis (nP + 2), cvmT.type.stripPis nP with
     | some (sbinders, sbody), some (tbindersM, tbodyM) =>
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (_, xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbinders[nP + 1]? with
        | some (_, ydom, _) =>
          ydom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [ℓA]) tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 1 && rhsC == Expr.bvar 0 &&
          tySlot == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP + 1 - k)) &&
          -- TT-lane check (task #147): skipped unless `mode.ttChecks`
          (!mode.ttChecks || tbodyM == Expr.sort ℓA)
        | _ => false)
     | _, _ => false)
  | _, _, _ => false

/-- `ctorResidualOk` through the index (task #136; the reasoning,
including why the subject is the *stored* constant and why the
capability guard is load-bearing, is at `ctorResidualOk`). -/
def ctorResidualOkF (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (eta : Bool) : Bool :=
  -- TT-lane check (task #147): trivially true unless `mode.ttChecks`.
  !mode.ttChecks || !eta ||
  (match fe.find? ctorName with
   | some (.ctorInfo cvCA _ _) =>
     (match cvCA.type.stripPis (nP + nF) with
      | some (_, cbody) => cbody == directFam T lps nP nF
      | none => false)
   | _ => false)

/-- `indBlockCaps` through the index. -/
def indBlockCapsF (fe : FEnv) (cvT cvC : ConstantVal) (nP nF : Nat) :
    IndCaps where
  eta := (cvC.levelParams = cvT.levelParams) &&
    checkEtaThmF mode fe cvT.name cvC.name cvT.levelParams nP nF
  etaCtor := cvC.name
  etaParams := nP
  etaFields := nF
  unitlike := checkUnitThmF mode fe cvT.name cvT.levelParams nP
  unitParams := nP
  ruleK := nF == 0 && piResultIsProp cvT.type

/-! ## Indexed mirrors of the declaration-checker functions (task #63)

Each mirrors its `Setlec/Kernel/Checker.lean` counterpart clause by
clause; the only difference is that every environment lookup
(`Env.find?`, `Env.findCV?`, `Expr.constsResolve` and the compound
guards built from them) goes through the `FEnv` index.  Under
`mkFEnv` each mirror *is* its generic counterpart
(`Setlec/Verify/CheckerF.lean`); environment-extending mirrors return
the pushed index (`FEnv.push`, definitionally `mkFEnv` of the
cons-extended environment). -/

section Mirrors

variable {m : Type → Type} [Monad m] [MonadExceptOf CheckError m]

/-- `checkConstantVal` through the index. -/
def checkConstantValF (ops : CheckerOps m) (fe : FEnv)
    (cv : ConstantVal) : m ConstantVal := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless cv.type.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if cv.type.hasFvar then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let type ← ops.annotate fe.env 0 cv.type
  unless type.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless type.constsResolveF fe do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let stype ← ops.inferType fe.env 0 type
  let _u ← ops.ensureSort fe.env 0 stype
  pure { cv with type := type }

/-- `checkMemberVal` through the index. -/
def checkMemberValF (ops : CheckerOps m) (blockNames : List Name)
    (fe : FEnv) (cv : ConstantVal) : m ConstantVal := do
  let f : Name → Name := fun n =>
    if blockNames.contains n then n.str "_model" else n
  let cvA ← checkConstantValF ops fe cv
  if cvA.name.isModelSuffix then
    throw (.invalid s!"model-shaped member name {cvA.name}")
  let some (.defnInfo cvm _mval _) := fe.find? (cvA.name.str "_model")
    | throw (.notImplemented s!"missing model for {cvA.name}")
  unless cvm.levelParams = cvA.levelParams do
    throw (.notImplemented s!"model level parameters mismatch for {cvA.name}")
  unless Expr.eqUpToNames (cvA.type.renameConsts f) cvm.type do
    throw (.notImplemented
      s!"model type mismatch for {cvA.name}\n  member (renamed): \
        {reprStr (cvA.type.renameConsts f)}\n  model: {reprStr cvm.type}")
  pure cvA

/-- `checkIotaThm` through the index. -/
def checkIotaThmF (ops : CheckerOps m) (fe' feSelf : FEnv)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) : m Unit := do
    let cvt ← unwrapOr
        (fe'.findCV? ((cvName.str "_model").str s!"iota_{j}"))
        (.notImplemented s!"missing iota theorem for {cvName}")
    unless cvt.levelParams = lps do
      throw (.notImplemented s!"iota theorem level mismatch for {cvName}")
    let depth := rP + cnF
    let (fvs, tbody) ← unwrapOr (openPisAtFvars depth cvt.type 0)
      (.notImplemented s!"iota statement shape mismatch for {cvName}")
    let targs := tbody.getAppArgs
    unless isEqHead tbody.getAppFn do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    unless targs.length = 3 do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    let lhsS := targs.getD 1 (.bvar 0)
    let rhsS := targs.getD 2 (.bvar 0)
    let xFvs := fvs.drop rP
    let largs := lhsS.getAppArgs
    unless lhsS.getAppFn == Expr.const (f cvName) (lps.map .param) do
      throw (.notImplemented s!"iota statement head mismatch for {cvName}")
    unless largs.length = mI + 1 do
      throw (.notImplemented s!"iota statement arity mismatch for {cvName}")
    unless largs.take rP == fvs.take rP do
      throw (.notImplemented s!"iota statement prefix mismatch for {cvName}")
    let major := largs.getLastD (.bvar 0)
    unless major == Expr.mkAppN
        (.const (f r.ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ xFvs) do
      throw (.notImplemented s!"iota statement major mismatch for {cvName}")
    unless (cvj.type.stripPis (cnP + cnF)).isSome do
      throw (.notImplemented s!"iota constructor telescope for {cvName}")
    let (cdoms, cres) ← unwrapOr
        (Expr.instPisAt (fvs.take cnP ++ xFvs) (cvj.type.renameConsts f))
        (.notImplemented s!"iota constructor telescope for {cvName}")
    unless cres.getAppArgs.length = cnP + (mI - rP) do
      throw (.notImplemented s!"iota constructor indices for {cvName}")
    checkDefEqList ops feSelf.env depth ((largs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP)
    checkDefEqList ops feSelf.env depth (xFvs.map Expr.fvarTypeD)
      (cdoms.drop cnP)
    let (rdoms, _) ← unwrapOr
        (Expr.instPisAt (fvs.take rP) (tyA.renameConsts f))
        (.notImplemented s!"iota recursor telescope for {cvName}")
    checkDefEqList ops feSelf.env depth
      ((fvs.take rP).map Expr.fvarTypeD) rdoms
    let (fvsP, _) ← unwrapOr (openPisAtFvars rP tyA 0)
      (.notImplemented s!"iota recursor telescope for {cvName}")
    let (cdomsP, crestP) ← unwrapOr
      (Expr.instPisAt (fvsP.take cnP) cvj.type)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    checkDefEqList ops feSelf.env depth
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP
    let (xFvsP, _) ← unwrapOr (openPisAtFvars cnF crestP rP)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
      (.notImplemented s!"rule shape mismatch for {cvName}")
    checkDefEqList ops feSelf.env depth ((fvsP ++ xFvsP).map Expr.fvarTypeD)
      ldoms
    let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
    unless ← ops.isDefEq feSelf.env depth rhsS rhsApplied do
      throw (.notImplemented s!"iota statement mismatch for {cvName}")
    checkIotaSidesTy mode ops feSelf.env depth (targs.getD 0 (.bvar 0)) lhsS
      rhsS (eqHeadLevel tbody.getAppFn) cvName

/-- `nestedRuleShape` through the index. -/
def nestedRuleShapeF (fe' feSelf : FEnv) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP cnP j : Nat) :
    Option (List Level × List Expr) :=
  if (fe'.findCV? ((cvName.str "_model").str s!"iota_{j}")).isSome ∧
      rP ≤ mI then
    match tyA.stripPis mI with
    | some (_, .forallE _ dom _ _) =>
      match dom.getAppFn with
      | .const _D lvls =>
        let args := dom.getAppArgs
        let k := mI - rP
        let pins := (args.take cnP).map (Expr.lowerBVars k 0)
        if args.length = cnP + k ∧
            args.take cnP == pins.map (Expr.liftLooseBVars k 0) ∧
            args.drop cnP ==
              (List.range k).map (fun i => Expr.bvar (k - 1 - i)) ∧
            pins.all (fun p => !p.hasFvar && p.looseBVarsBounded rP &&
              p.constsResolveF feSelf && p.allLevelParamsDefined lps) ∧
            lvls.all (Level.allParamsDefined lps) then
          some (lvls, pins)
        else none
      | _ => none
    | _ => none
  else none

/-- `checkIotaThmN` through the index. -/
def checkIotaThmNF (ops : CheckerOps m) (fe' feSelf : FEnv)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) (cvj : ConstantVal)
    (cnP cnF : Nat) (rhsA : Expr) : m RecRuleFire := do
    match nestedRuleShapeF fe' feSelf cvName lps tyA mI rP cnP j with
    | none => pure .inert
    | some (lvls, pins) => do
    let cvt ← unwrapOr
        (fe'.findCV? ((cvName.str "_model").str s!"iota_{j}"))
        (.notImplemented s!"missing iota theorem for {cvName}")
    unless cvt.levelParams = lps do
      throw (.notImplemented s!"iota theorem level mismatch for {cvName}")
    let depth := rP + cnF
    let (fvs, tbody) ← unwrapOr (openPisAtFvars depth cvt.type 0)
      (.notImplemented s!"iota statement shape mismatch for {cvName}")
    let targs := tbody.getAppArgs
    unless isEqHead tbody.getAppFn do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    unless targs.length = 3 do
      throw (.notImplemented s!"iota statement not an equation for {cvName}")
    let lhsS := targs.getD 1 (.bvar 0)
    let rhsS := targs.getD 2 (.bvar 0)
    let xFvs := fvs.drop rP
    let pinsF := pins.map fun p =>
      Expr.instSpine (fvs.take rP) (rP - 1) (p.renameConsts f)
    let largs := lhsS.getAppArgs
    unless lhsS.getAppFn == Expr.const (f cvName) (lps.map .param) do
      throw (.notImplemented s!"iota statement head mismatch for {cvName}")
    unless largs.length = mI + 1 do
      throw (.notImplemented s!"iota statement arity mismatch for {cvName}")
    unless largs.take rP == fvs.take rP do
      throw (.notImplemented s!"iota statement prefix mismatch for {cvName}")
    let major := largs.getLastD (.bvar 0)
    -- up to display-only binder names, like `checkIotaThmN` (the pins
    -- may contain binders; the artifact contract fixes statements only
    -- up to `Expr.eqv`)
    unless Expr.eqUpToNames major (Expr.mkAppN (.const (f r.ctor) lvls)
        (pinsF ++ xFvs)) do
      throw (.notImplemented s!"iota statement major mismatch for {cvName}")
    let (_, cbody0) ← unwrapOr (cvj.type.stripPis (cnP + cnF))
      (.notImplemented s!"iota constructor telescope for {cvName}")
    unless (match cbody0.getAppFn with
        | .const _ _ => true
        | _ => false) do
      throw (.notImplemented s!"iota constructor residual head for {cvName}")
    let (cdoms, cres) ← unwrapOr
        (Expr.instPisAt (pinsF ++ xFvs)
          ((cvj.type.instantiateLevelParams cvj.levelParams
            lvls).renameConsts f))
        (.notImplemented s!"iota constructor telescope for {cvName}")
    unless cres.getAppArgs.length = cnP + (mI - rP) do
      throw (.notImplemented s!"iota constructor indices for {cvName}")
    checkDefEqList ops feSelf.env depth ((largs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP)
    checkDefEqList ops feSelf.env depth (xFvs.map Expr.fvarTypeD)
      (cdoms.drop cnP)
    let (rdoms, _) ← unwrapOr
        (Expr.instPisAt (fvs.take rP) (tyA.renameConsts f))
        (.notImplemented s!"iota recursor telescope for {cvName}")
    checkDefEqList ops feSelf.env depth
      ((fvs.take rP).map Expr.fvarTypeD) rdoms
    let (fvsP, _) ← unwrapOr (openPisAtFvars rP tyA 0)
      (.notImplemented s!"iota recursor telescope for {cvName}")
    let pinsP := pins.map fun p =>
      Expr.instSpine (fvsP.take rP) (rP - 1) p
    checkAnnotList ops feSelf.env depth pinsP
    let (cdomsP, crestP) ← unwrapOr (Expr.instPisAt pinsP
        (cvj.type.instantiateLevelParams cvj.levelParams lvls))
      (.notImplemented s!"iota constructor telescope for {cvName}")
    checkTypedList ops feSelf.env depth pinsP cdomsP
    let (xFvsP, crest2P) ← unwrapOr (openPisAtFvars cnF crestP rP)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    unless crest2P.getAppArgs.length == cnP + (mI - rP) do
      throw (.notImplemented s!"iota constructor arity for {cvName}")
    let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
      (.notImplemented s!"rule shape mismatch for {cvName}")
    checkDefEqList ops feSelf.env depth ((fvsP ++ xFvsP).map Expr.fvarTypeD)
      ldoms
    let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
    unless ← ops.isDefEq feSelf.env depth rhsS rhsApplied do
      throw (.notImplemented s!"iota statement mismatch for {cvName}")
    checkIotaSidesTy mode ops feSelf.env depth (targs.getD 0 (.bvar 0)) lhsS
      rhsS (eqHeadLevel tbody.getAppFn) cvName
    pure (.nested lvls pins)

/-- `checkIotaRule` through the index. -/
def checkIotaRuleF (ops : CheckerOps m) (fe' feSelf : FEnv)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP j : Nat) (r : RecRule) : m RecRule := do
    let some (.ctorInfo cvj cnP cnF) := fe'.find? r.ctor
      | throw (.invalid s!"iota rule constructor {r.ctor} not stored")
    unless r.nfields = cnF do
      throw (.invalid "rule field count mismatch")
    unless r.rhs.looseBVarsBounded 0 do
      throw (.invalid s!"loose bound variable in rule of {cvName}")
    if r.rhs.hasFvar then
      throw (.invalid s!"free variable in rule of {cvName}")
    let rhsA ← ops.annotate feSelf.env 0 r.rhs
    unless rhsA.allLevelParamsDefined lps do
      throw (.invalid s!"undeclared universe parameter in rule of {cvName}")
    unless rhsA.constsResolveF feSelf do
      throw (.invalid s!"unknown constant in rule of {cvName}")
    unless (rhsA.stripLams (rP + cnF)).isSome do
      throw (.notImplemented s!"rule shape mismatch for {cvName}")
    let _rhsTy ← ops.inferType feSelf.env 0 rhsA
    let fire ← if Expr.recRulePlain tyA mI rP cnP then do
        checkIotaThmF mode ops fe' feSelf f cvName lps tyA mI rP j r
          cvj cnP cnF rhsA
        pure RecRuleFire.plain
      else
        checkIotaThmNF mode ops fe' feSelf f cvName lps tyA mI rP j r
          cvj cnP cnF rhsA
    pure { r with rhs := rhsA, ctorParams := cnP, fire := fire }

/-- `checkIotaRules` through the index. -/
def checkIotaRulesF (ops : CheckerOps m) (fe' feSelf : FEnv)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) : Nat → List RecRule → m (List RecRule)
  | _, [] => pure []
  | j, r :: rest => do
    let r' ← checkIotaRuleF mode ops fe' feSelf f cvName lps tyA mI rP j r
    let rest' ← checkIotaRulesF ops fe' feSelf f cvName lps tyA mI rP
      (j + 1) rest
    pure (r' :: rest')

/-- `checkProjLookups` through the index. -/
def checkProjLookupsF (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : m (ConstantVal × ConstantVal) := do
  let some (.ctorInfo cvj cnP cnF) := fe.find? ctorName
    | throw (.notImplemented "projection constructor not stored")
  unless cnP = nP ∧ cnF = nF do
    throw (.notImplemented "projection constructor arity mismatch")
  let some (.defnInfo mcv _ _) := fe.find? (projModelName T i)
    | throw (.notImplemented "missing projection model")
  unless mcv.levelParams = lps do
    throw (.notImplemented "projection model level mismatch")
  unless (fe.find? (projFnName T i)).isNone do
    throw (.invalid "projection name taken")
  unless (fe.find? T).isSome do
    throw (.notImplemented "projection parent not stored")
  unless fe.find? eqName = some eqA do
    throw (.notImplemented "projection iota requires the pinned Eq basis")
  pure (cvj, mcv)

/-- `checkProjTy` through the index. -/
def checkProjTyF (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (mty : Expr) (nP nF : Nat) : m Expr := do
  let pty := mty.renameConsts (projBack T ctorName nF)
  unless (pty.renameConsts (projFwd T ctorName nF)) == mty do
    throw (.notImplemented "projection type roundtrip")
  unless pty.constsResolveF fe do
    throw (.notImplemented "projection type resolution")
  unless pty.looseBVarsBounded 0 && !pty.hasFvar &&
      pty.allLevelParamsDefined lps do
    throw (.notImplemented "projection type wellformedness")
  unless (pty.stripPis (nP + 1)).isSome do
    throw (.notImplemented "projection type telescope")
  pure pty

/-- `checkProjRule` through the index. -/
def checkProjRuleF (ops : CheckerOps m) (fe : FEnv) (pty : Expr) (cvj : ConstantVal)
    (lps : List Name) (nP nF i : Nat) : m Expr := do
  let some rhs := Expr.pisToLams (nP + nF) cvj.type (.bvar (nF - 1 - i))
    | throw (.notImplemented "projection rule telescope")
  unless !rhs.hasFvar && rhs.looseBVarsBounded 0 do
    throw (.notImplemented "projection rule scoping")
  let rhsA ← ops.annotate fe.env 0 rhs
  unless rhsA.allLevelParamsDefined lps && rhsA.constsResolveF fe &&
      rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
    throw (.notImplemented "projection rule wellformedness")
  let some (rbinders, rrbody) := rhsA.stripLams (nP + nF)
    | throw (.notImplemented "projection rule telescope")
  unless rrbody == Expr.bvar (nF - 1 - i) do
    throw (.notImplemented "projection rule body")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAuxA (fun _ e => e) rbinders.toArray cbindersR.toArray
      0 0 (nP + nF) do
    throw (.notImplemented "projection rule domain mismatch")
  let some (fvsP, _) := openPisAtFvarsF nP pty 0
    | throw (.notImplemented "projection type telescope")
  let some (cdomsP, crestP) := Expr.instPisAtF fvsP cvj.type
    | throw (.notImplemented "projection constructor telescope")
  checkDefEqList ops fe.env (nP + nF) (fvsP.map Expr.fvarTypeD) cdomsP
  let some (xFvs, _) := openPisAtFvarsF nF crestP nP
    | throw (.notImplemented "projection constructor telescope")
  let some (ldoms, _) := Expr.instLamsAtF (fvsP ++ xFvs) rhsA
    | throw (.notImplemented "projection rule telescope")
  checkDefEqList ops fe.env (nP + nF) ((fvsP ++ xFvs).map Expr.fvarTypeD)
    ldoms
  let _rhsTy ← ops.inferType fe.env 0 rhsA
  pure rhsA

/-- `checkProjIota` through the index. -/
def checkProjIotaF (ops : CheckerOps m) (fe : FEnv)
    (T ctorName : Name) (lps : List Name)
    (cvj : ConstantVal) (nP nF i : Nat) : m Unit := do
  let some (.thmInfo tcv _) := fe.find? ((projModelName T i).str "iota")
    | throw (.notImplemented "missing projection iota theorem")
  unless tcv.levelParams = lps do
    throw (.notImplemented "projection iota level mismatch")
  let some (sbinders, sbody) := tcv.type.stripPis (nP + nF)
    | throw (.notImplemented "projection iota telescope")
  let some (cbindersR, _) := cvj.type.stripPis (nP + nF)
    | throw (.notImplemented "projection constructor telescope")
  unless domsMatchAux
      (fun _ e => e.renameConsts (projFwd T ctorName nF))
      sbinders cbindersR 0 0 (nP + nF) do
    throw (.notImplemented "projection iota domain mismatch")
  let depth := nP + nF
  let pArgs := (List.range nP).map fun k => Expr.bvar (depth - 1 - k)
  let xArgs := (List.range nF).map fun k => Expr.bvar (nF - 1 - k)
  let mkSpine := Expr.mkAppN
    (.const (ctorName.str "_model") (cvj.levelParams.map .param))
    (pArgs ++ xArgs)
  let lhsS := Expr.mkAppN
    (.const (projModelName T i) (lps.map .param)) (pArgs ++ [mkSpine])
  match sbody with
  | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
    unless c = eqName do
      throw (.notImplemented "projection iota head")
    unless lhsC == lhsS do
      throw (.notImplemented "projection iota redex mismatch")
    unless rhsC == Expr.bvar (nF - 1 - i) do
      throw (.notImplemented "projection iota field mismatch")
  | _ => throw (.notImplemented "projection iota body shape")
  -- side certificates (task #100 stage 3; see `checkProjIota`)
  let (_, sbodyO) ← unwrapOr (openPisAtFvars depth tcv.type 0)
    (.notImplemented "projection iota telescope")
  let targsO := sbodyO.getAppArgs
  checkIotaSidesTy mode ops fe.env depth (targsO.getD 0 (.bvar 0))
    (targsO.getD 1 (.bvar 0)) (targsO.getD 2 (.bvar 0))
    (eqHeadLevel sbody.getAppFn) (projModelName T i)

/-- `checkDefnVal` through the index, returning the pushed index. -/
def checkDefnValF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) (hint : ReducibilityHint) : m FEnv := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate fe.env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolveF fe do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType fe.env 0 value
  unless ← ops.isDefEq fe.env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in definition {cv.name}")
  pure (fe.push (.defnInfo cv value hint))

/-- `checkThmVal` through the index, returning the pushed index. -/
def checkThmValF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) : m FEnv := do
  let stype ← ops.inferType fe.env 0 cv.type
  let u ← ops.ensureSort fe.env 0 stype
  unless (← liftFueled "level comparison" (Level.isEquiv u .zero)) do
    throw (.invalid s!"type of theorem {cv.name} is not a proposition")
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate fe.env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolveF fe do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType fe.env 0 value
  unless ← ops.isDefEq fe.env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in theorem {cv.name}")
  pure (fe.push (.thmInfo cv value))

/-- `checkOpaqueVal` through the index, returning the pushed index. -/
def checkOpaqueValF (ops : CheckerOps m) (fe : FEnv) (cv : ConstantVal)
    (value : Expr) : m FEnv := do
  unless value.looseBVarsBounded 0 do
    throw (.invalid s!"loose bound variable in value of {cv.name}")
  if value.hasFvar then
    throw (.invalid s!"unexpected free variable in value of {cv.name}")
  let value ← ops.annotate fe.env 0 value
  unless value.allLevelParamsDefined cv.levelParams do
    throw (.invalid s!"undeclared universe parameter in value of {cv.name}")
  unless value.constsResolveF fe do
    throw (.invalid s!"unknown constant in value of {cv.name}")
  let vtype ← ops.inferType fe.env 0 value
  unless ← ops.isDefEq fe.env 0 vtype cv.type do
    throw (.invalid s!"type mismatch in opaque {cv.name}")
  pure (fe.push (.axiomInfo cv))

/-- `installBasisDecl` through the index, returning the pushed index. -/
def installBasisDeclF (fe : FEnv) (ci : ConstantInfo) : m FEnv := do
  unless (fe.find? ci.name).isNone do
    throw (.invalid s!"duplicate declaration {ci.name}")
  pure (fe.push ci)

/-- `checkDivModCerts` through the index. -/
def checkDivModCertsF (ops : CheckerOps m) (fe : FEnv) (c : Name)
    (annVal : Expr) : List (List Expr × Expr) → List Expr → m Bool
  | [], [] => pure true
  | (hyps, eqE) :: srest, proof :: prest => do
    if divModCertGuardF fe c annVal hyps eqE proof then
      let appliedA ← ops.annotate fe.env 4
        (divModCertApplied (Expr.substConstAll c annVal proof)
          (hyps.map (Expr.substConst0 c annVal)))
      let tp ← ops.inferType fe.env 4 appliedA
      if ← ops.isDefEq fe.env 4 tp (Expr.substConst0 c annVal eqE) then
        checkDivModCertsF ops fe c annVal srest prest
      else pure false
    else pure false
  | _, _ => pure false

/-- `checkDivModPin` through the index. -/
def checkDivModPinF (ops : CheckerOps m) (fe fe2 : FEnv) (c : Name) :
    m Unit := do
  if divModEnvGuardF fe2 c then
    match fe2.find? c with
    | some (.defnInfo _ value' _) =>
      if divModPinGuardF fe c && divModCertsGuardF fe c value' then do
        let pinA ← ops.annotate fe.env 0 (divModDeclPin c)
        let okPin ← ops.isDefEq fe.env 0 value' pinA
        if okPin then do
          let ok ← checkDivModCertsF ops fe c value'
            (divModCertStmts c) (divModCertProofs c)
          if ok then pure ()
          else throw (.internal
            s!"pinned Nat.div/mod certificate failed after pin match ({c})")
        else throw (.notImplemented
          s!"unsupported Nat.div/mod spelling ({c})")
      else throw (.notImplemented
        s!"unsupported Nat.div/mod spelling ({c}: pin ground constants absent)")
    | _ => throw (.internal s!"Nat.div/mod operation not stored ({c})")
  else throw (.notImplemented
    s!"unsupported Nat.div/mod environment ({c})")

/-- `checkReducePin` through the index. -/
def checkReducePinF (ops : CheckerOps m) (fe fe2 : FEnv) (c : Name)
    (value : Expr) : m Unit := do
  if reduceStoredOkF fe2 c && reduceElemOkF fe c then
    if reducePinGuardF fe c then do
      let valA ← ops.annotate fe.env 0 value
      let pinA ← ops.annotate fe.env 0 (reduceDeclPin c)
      let okPin ← ops.isDefEq fe.env 0 valA pinA
      if okPin then do
        let x := reduceCertVar c
        let ok ← ops.isDefEq fe.env 1 (.app valA x) x
        if ok then pure ()
        else throw (.internal
          s!"pinned compiler-trust opaque is not the identity ({c})")
      else throw (.notImplemented
        s!"unsupported compiler-trust opaque spelling ({c})")
    else throw (.notImplemented
      s!"unsupported compiler-trust opaque spelling ({c}: pin ground constants absent)")
  else throw (.notImplemented
    s!"unsupported compiler-trust opaque declaration ({c})")

/-! ### The direct simple-structure path, through the index -/

/-- `directNonRec` through the index. -/
def directNonRecF (fe : FEnv) (p : DirectParts) : Bool :=
  match p.cvC.type.stripPis (p.nP + p.nF) with
  | some (cbs, _) => cbs.all fun b => b.2.1.constsResolveF fe
  | none => false

/-- `directNoModel` through the index. -/
def directNoModelF (fe : FEnv) (p : DirectParts) : Bool :=
  (fe.find? (p.cvT.name.str "_model")).isNone &&
  (fe.find? (p.cvC.name.str "_model")).isNone &&
  (fe.find? (p.cvR.name.str "_model")).isNone &&
  (List.range p.nF).all fun j =>
    (fe.find? (projModelName p.cvT.name j)).isNone

/-- `directParts?` through the index. -/
def directPartsF? (fe : FEnv) (block : List ConstantInfo) :
    Option DirectParts :=
  match directPartsCore? block with
  | some p =>
    if directStructsEnabled && directNonRecF fe p && directNoModelF fe p then
      some p
    else none
  | none => none

/-- `checkDirectFieldUniv` through the index. -/
def checkDirectFieldUnivF (ops : CheckerOps m) (fe : FEnv) (s : Level)
    (nP : Nat) (fvs : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct structure: field index")
    let ty ← ops.inferType fe.env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort fe.env (nP + j) ty
    unless ← liftFueled "level comparison" (Level.leq u s) do
      throw (.invalid "direct structure: field universe too large")
    checkDirectFieldUnivF ops fe s nP fvs j

/-- `checkDirectFieldUnivF` over an array (positional list indexing is
linear per access; the callers convert once).  Equal to it at
`List.toArray`: `checkDirectFieldUnivFA_eq`. -/
def checkDirectFieldUnivFA (ops : CheckerOps m) (fe : FEnv) (s : Level)
    (nP : Nat) (fvs : Array Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let fv ← unwrapOr fvs[j]? (.internal "direct structure: field index")
    let ty ← ops.inferType fe.env (nP + j) fv.fvarTypeD
    let u ← ops.ensureSort fe.env (nP + j) ty
    unless ← liftFueled "level comparison" (Level.leq u s) do
      throw (.invalid "direct structure: field universe too large")
    checkDirectFieldUnivFA ops fe s nP fvs j

/-- `checkDirectDomsAt` through the index. -/
def checkDirectDomsAtF (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : List Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkDirectDomsAtF ops fe off fvs doms j

/-- `checkDirectDomsAtF` over arrays (see `checkDirectFieldUnivFA`).
Equal to it at `List.toArray`: `checkDirectDomsAtFA_eq`. -/
def checkDirectDomsAtFA (ops : CheckerOps m) (fe : FEnv) (off : Nat)
    (fvs doms : Array Expr) : Nat → m Unit
  | 0 => pure ()
  | j + 1 => do
    let a ← unwrapOr fvs[j]? (.internal "direct structure: domain index")
    let b ← unwrapOr doms[j]? (.internal "direct structure: domain index")
    unless ← ops.isDefEq fe.env (off + j) a.fvarTypeD b do
      throw (.notImplemented "direct structure: binder domain mismatch")
    checkDirectDomsAtFA ops fe off fvs doms j

/-- `checkDirectInd` through the index. -/
def checkDirectIndF (ops : CheckerOps m) (fe : FEnv) (p : DirectParts) :
    m (FEnv × ConstantVal) := do
  let cvTa ← checkConstantValF ops fe p.cvT
  let (_, tbody) ← unwrapOr (cvTa.type.stripPis p.nP)
    (.notImplemented "direct structure: type former telescope")
  unless tbody == Expr.sort p.resSort do
    throw (.notImplemented "direct structure: type former result sort")
  pure (fe.push (.indInfo cvTa (directCaps p)), cvTa)

/-- `checkDirectCtor` through the index. -/
def checkDirectCtorF (ops : CheckerOps m) (fe₀ fe : FEnv) (p : DirectParts)
    (cvTa : ConstantVal) : m (FEnv × ConstantVal) := do
  let cvCa ← checkConstantValF ops fe p.cvC
  let (_, cbody) ← unwrapOr (cvCa.type.stripPis (p.nP + p.nF))
    (.notImplemented "direct structure: constructor telescope")
  unless cbody == directFam p.cvT.name p.cvT.levelParams p.nP p.nF do
    throw (.notImplemented "direct structure: constructor result")
  let cq ← unwrapOr (openPisAtFvarsF p.nP cvCa.type 0)
    (.notImplemented "direct structure: constructor telescope")
  let tq ← unwrapOr (openPisAtFvarsF p.nP cvTa.type 0)
    (.notImplemented "direct structure: type former telescope")
  checkDirectDomsAtFA ops fe 0 cq.1.toArray
    (tq.1.map Expr.fvarTypeD).toArray p.nP
  let xq ← unwrapOr (openPisAtFvarsF p.nF cq.2 p.nP)
    (.notImplemented "direct structure: constructor field telescope")
  unless xq.2 == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1 do
    throw (.notImplemented "direct structure: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolveF fe₀ do
    throw (.notImplemented "direct structure: field domain after the block")
  checkDirectFieldUnivFA ops fe p.resSort p.nP xq.1.toArray p.nF
  pure (fe.push (.ctorInfo cvCa p.nP p.nF), cvCa)

/-- `checkDirectRecTy` through the index. -/
def checkDirectRecTyF (ops : CheckerOps m) (fe : FEnv) (p : DirectParts)
    (cvTa cvCa cvRa : ConstantVal) : m Unit := do
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  unless directShape T p.cvC.name lps p.elim p.nP p.nF
      cvTa.type cvCa.type cvRa.type do
    throw (.notImplemented "direct structure: annotated recursor shape")
  let (fvsP, rest) ← unwrapOr (openPisAtFvarsF (p.nP + 2) cvRa.type 0)
    (.notImplemented "direct structure: recursor telescope")
  let ps := fvsP.take p.nP
  let famApp := Expr.mkAppN (.const T (lps.map .param)) ps
  let (cdomsP, crest) ← unwrapOr (Expr.instPisAtF ps cvCa.type)
    (.notImplemented "direct structure: constructor telescope")
  checkDirectDomsAtFA ops fe 0 ps.toArray cdomsP.toArray p.nP
  let mfv ← unwrapOr fvsP[p.nP]?
    (.internal "direct structure: motive index")
  let (mbs, mbody) ← unwrapOr (mfv.fvarTypeD.stripPis 1)
    (.notImplemented "direct structure: motive telescope")
  let mdom ← unwrapOr ((mbs[0]?).map (·.2.1))
    (.notImplemented "direct structure: motive telescope")
  unless ← ops.isDefEq fe.env p.nP mdom famApp do
    throw (.notImplemented "direct structure: motive domain")
  unless mbody == Expr.sort (.param p.elim) do
    throw (.notImplemented "direct structure: motive codomain")
  let minfv ← unwrapOr fvsP[p.nP + 1]?
    (.internal "direct structure: minor index")
  let (xFvs, minBody) ← unwrapOr
    (openPisAtFvarsF p.nF minfv.fvarTypeD (p.nP + 2))
    (.notImplemented "direct structure: minor telescope")
  let (cdomsF, crest2) ← unwrapOr (Expr.instPisAtF xFvs crest)
    (.notImplemented "direct structure: constructor field telescope")
  checkDirectDomsAtFA ops fe (p.nP + 2) xFvs.toArray cdomsF.toArray p.nF
  unless crest2 == famApp do
    throw (.notImplemented "direct structure: constructor residual")
  unless minBody == Expr.app mfv
      (Expr.mkAppN (.const p.cvC.name (lps.map .param)) (ps ++ xFvs)) do
    throw (.notImplemented "direct structure: minor conclusion")
  let (jbs, jbody) ← unwrapOr (rest.stripPis 1)
    (.notImplemented "direct structure: major telescope")
  let jdom ← unwrapOr ((jbs[0]?).map (·.2.1))
    (.notImplemented "direct structure: major telescope")
  unless ← ops.isDefEq fe.env (p.nP + 2) jdom famApp do
    throw (.notImplemented "direct structure: major domain")
  unless jbody == Expr.app mfv (.bvar 0) do
    throw (.notImplemented "direct structure: recursor conclusion")

/-- `checkDirectRule` through the index. -/
def checkDirectRuleF (ops : CheckerOps m) (fe : FEnv) (p : DirectParts)
    (cvCa cvRa : ConstantVal) : m Expr := do
  unless !p.rhs.hasFvar && p.rhs.looseBVarsBounded 0 do
    throw (.notImplemented "direct structure: rule scoping")
  let rhsA ← ops.annotate fe.env 0 p.rhs
  unless rhsA.allLevelParamsDefined cvRa.levelParams && rhsA.constsResolveF fe &&
      rhsA.looseBVarsBounded 0 && !rhsA.hasFvar do
    throw (.notImplemented "direct structure: rule wellformedness")
  let (_, rbody) ← unwrapOr (rhsA.stripLams (p.nP + 2 + p.nF))
    (.notImplemented "direct structure: rule telescope")
  unless rbody == directRuleBody p.nF do
    throw (.notImplemented "direct structure: rule body")
  let depth := p.nP + 2 + p.nF
  let (fvsP, _) ← unwrapOr (openPisAtFvarsF (p.nP + 2) cvRa.type 0)
    (.notImplemented "direct structure: recursor telescope")
  let (_, crest) ← unwrapOr (Expr.instPisAtF (fvsP.take p.nP) cvCa.type)
    (.notImplemented "direct structure: constructor telescope")
  let (xFvs, _) ← unwrapOr (openPisAtFvarsF p.nF crest (p.nP + 2))
    (.notImplemented "direct structure: constructor field telescope")
  let (ldoms, _) ← unwrapOr (Expr.instLamsAtF (fvsP ++ xFvs) rhsA)
    (.notImplemented "direct structure: rule telescope")
  checkDefEqList ops fe.env depth ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms
  let _rhsTy ← ops.inferType fe.env 0 rhsA
  pure rhsA


/-- `checkDirectProj` through the index.  `rt?` is the incrementally
threaded constructor residual `directProjResid T lps nP cvCa.type i`
(the caller's invariant — `checkDirectProjsS` maintains it by
construction), so the generated projection type is read off it in one
step instead of redoing the `i` earlier substitutions
(`directProjTy_eq_resid`). -/
def checkDirectProjF (ops : CheckerOps m) (T C : Name) (lps : List Name)
    (nP nF : Nat) (cvTa cvCa : ConstantVal) (rt? : Option Expr)
    (fe : FEnv) (i : Nat) : m FEnv := do
  let pty ← unwrapOr (directProjTyR T lps nP nF i cvTa.type rt?)
    (.notImplemented "direct structure: projection type")
  unless !pty.hasFvar && pty.looseBVarsBounded 0 do
    throw (.notImplemented "direct structure: projection type scoping")
  let ptyA ← ops.annotate fe.env 0 pty
  unless ptyA.allLevelParamsDefined lps && ptyA.constsResolveF fe &&
      ptyA.looseBVarsBounded 0 && !ptyA.hasFvar do
    throw (.notImplemented "direct structure: projection type wellformedness")
  unless (ptyA.stripPis (nP + 1)).isSome do
    throw (.notImplemented "direct structure: projection type telescope")
  let sty ← ops.inferType fe.env 0 ptyA
  let _u ← ops.ensureSort fe.env 0 sty
  unless (fe.find? (projFnName T i)).isNone do
    throw (.invalid "projection name taken")
  checkProjShape (m := m) ptyA cvCa.type nP nF
  let (fvsP, prest) ← unwrapOr (openPisAtFvarsF nP ptyA 0)
    (.notImplemented "direct structure: projection type telescope")
  let famApp := Expr.mkAppN (.const T (lps.map .param)) fvsP
  let (sbs, _) ← unwrapOr (prest.stripPis 1)
    (.notImplemented "direct structure: projection subject telescope")
  let sdom ← unwrapOr ((sbs[0]?).map (·.2.1))
    (.notImplemented "direct structure: projection subject telescope")
  unless ← ops.isDefEq fe.env nP sdom famApp do
    throw (.notImplemented "direct structure: projection subject domain")
  let (tFvs, resid) ← unwrapOr (openPisAtFvars 1 prest nP)
    (.notImplemented "direct structure: projection subject telescope")
  let tfv ← unwrapOr tFvs[0]?
    (.internal "direct structure: projection subject index")
  let projArgs := (List.range i).map fun j =>
    Expr.mkAppN (.const (projFnName T j) (lps.map .param)) (fvsP ++ [tfv])
  let (_, cresid) ← unwrapOr (Expr.instPisAtF (fvsP ++ projArgs) cvCa.type)
    (.notImplemented "direct structure: projection field telescope")
  let fdom ← unwrapOr (match cresid with
      | .forallE _ d _ _ => some d
      | _ => none)
    (.notImplemented "direct structure: projection field telescope")
  unless ← ops.isDefEq fe.env (nP + 1) resid fdom do
    throw (.notImplemented "direct structure: projection residual")
  let rhsA ← checkProjRuleF ops fe ptyA cvCa lps nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, ptyA⟩ nP nP
    [⟨C, nF, nP,
      if Expr.recRulePlain ptyA nP nP nP then .plain else .inert, rhsA⟩]))

end Mirrors

end Setlec
