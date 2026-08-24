import Setlec.Kernel.Checker
import Setlec.Kernel.DeclI

/-!
# The shared-state declaration checker (task #51)

One interned state (`IState`, `Setlec/Kernel/CoreI.lean`) per
*declaration*: all checker operations within one `checkDecl` — the
annotate/infer/defeq/whnf calls of every phase — run in a single
`CheckIM` state, so the arena and the memo caches are shared across
entry calls instead of being rebuilt per call (`cachedOps`).

The environment is not constant within an inductive block
(`checkIndDecl`'s provisional environments), and cache entries are only
valid for the environment they were created under.  The discipline is
**driver-directed**: the thin drivers below mirror `checkDecl`'s
phase structure and call `flushS` at every environment transition —
the memo and lazy-constant caches are dropped, the *arena* (which is
environment-independent: denotations mention no environment) and the
name index survive.  There is no runtime environment comparison; the
adequacy of the flush points is what the bridge proves
(`Setlec/Verify/SimS.lean`, `Setlec/Verify/BridgeS*.lean`,
`Setlec/Model/ConsistencyS.lean`).

The environment *index* (`FEnv`) is built once per declaration and
maintained across the provisional environments by `FEnv.push` — the
index of a cons-extended environment is one `HashMap.insert`
(`mkFEnv_push`), so the per-entry-call `mkFEnv` fold disappears.  The
recursor group keeps the `env₂` snapshot of the index and rebuilds the
final environments from it by pushes (the ruled recursors are installed
on `env₂`, not on the provisional `envSelf`).

Everything here is additive: `Setlec/Kernel/Checker.lean` (the generic
checker and its `cachedOps` instantiation) is untouched, and the
single-environment pieces are the *generic* checker functions
instantiated at `sharedOps` — only the phase structure is mirrored.
-/

namespace Setlec

/-- The index of the cons-extended environment (`mkFEnv_push`:
`FEnv.push (mkFEnv env) ci = mkFEnv ⟨ci :: env.consts⟩`, definitionally). -/
def FEnv.push (fe : FEnv) (ci : ConstantInfo) : FEnv :=
  ⟨⟨ci :: fe.env.consts⟩, fe.idx.insert ci.name ci⟩

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
    | .forallE _ dom body mb =>
      dom == .const natName [] && natOpCodF fe c body && natCod1 mb
    | _ => false
  else
    match ty with
    | .forallE _ dom (.forallE _ dom2 body mb2) mb =>
      dom == .const natName [] && dom2 == .const natName [] &&
      natOpCodF fe c body && natCod1 mb && natCod1 mb2
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
     | some (sbinders, sbody), some (tbindersM, _) =>
       domsMatchAux (fun _ e => e) sbinders tbindersM 0 0 nP &&
       (match sbinders[nP]? with
        | some (_, xdom, _) =>
          xdom == Expr.mkAppN (.const (T.str "_model") (lps.map .param))
            ((List.range nP).map fun k => Expr.bvar (nP - 1 - k))
        | none => false) &&
       (match sbody with
        | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 0 &&
          rhsC == Expr.mkAppN
            (.const (ctorName.str "_model") (lps.map .param))
            (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
             (List.range nF).map fun j => Expr.mkAppN
               (.const (projModelName T j) (lps.map .param))
               (((List.range nP).map fun k => Expr.bvar (nP - k)) ++
                [Expr.bvar 0]))
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
     | some (sbinders, sbody), some (tbindersM, _) =>
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
        | .app (.app (.app (.const c [_ℓ]) _tySlot) lhsC) rhsC =>
          c == eqName && lhsC == Expr.bvar 1 && rhsC == Expr.bvar 0
        | _ => false)
     | _, _ => false)
  | _, _, _ => false

/-- `indBlockCaps` through the index. -/
def indBlockCapsF (fe : FEnv) (cvT cvC : ConstantVal) (nP nF : Nat) :
    IndCaps where
  eta := (cvC.levelParams = cvT.levelParams) &&
    checkEtaThmF fe cvT.name cvC.name cvT.levelParams nP nF
  etaCtor := cvC.name
  etaParams := nP
  etaFields := nF
  unitlike := checkUnitThmF fe cvT.name cvT.levelParams nP
  unitParams := nP
  ruleK := nF == 0 && piResultIsProp cvT.type

/-- Drop the memo and lazy stored-constant caches (an environment
transition).  The environment-independent components survive: the
arena, the interned environment (`ienv`, self-certified by denotation
tags), the loose-bvar-bound cache and the level-operation caches —
none of their invariants mention the environment. -/
def IState.flushed (s : IState) : IState :=
  { s with
      constTyAt := {}, constValAt := {}, ruleRhsAt := {},
      whnfCoreC := {}, whnfC := {}, inferC := {}, defeqC := {},
      annotC := {}, codOfC := {} }

def flushS : CheckIM Unit :=
  modify (·.flushed)

/-- Shared-state unary entry point: intern into the ambient arena, run
the interned knot, read back.  Unlike `runEntryE` the state is the
ambient per-declaration state, not a fresh one. -/
def opE (fe : FEnv) (pick : CoreFnsI → Nat → EIdx → CheckIM EIdx)
    (d : Nat) (e : Expr) : CheckIM Expr := do
  let i ← internExprM e
  let j ← pick (coreKnotI fe checkFuel) d i
  match ← withStore (fun st => st.readbackI j) with
  | some v => pure v
  | none => throw (.internal "interned readback failed")

/-- Shared-state definitional-equality entry point. -/
def opB (fe : FEnv) (d : Nat) (a b : Expr) : CheckIM Bool := do
  let i ← internExprM a
  let j ← internExprM b
  (coreKnotI fe checkFuel).defeq d i j

/-- Shared-state sort-ensuring entry point. -/
def opS (fe : FEnv) (d : Nat) (e : Expr) : CheckIM Level := do
  let i ← internExprM e
  let u ← ensureSortI (coreKnotI fe checkFuel) d i
  readbackLevelM u

/-- The per-declaration shared operations at a fixed environment index.
The methods ignore the per-call environment argument: the drivers
instantiate the record only at `fe.env`, which is what the bridge
walks relate (there is no runtime check — the flush discipline is
proven adequate, not tested). -/
def sharedOps (fe : FEnv) : CheckerOps CheckIM where
  annotate _ d e := opE fe (·.annotate) d e
  inferType _ d e := opE fe (·.infer) d e
  isDefEq _ d a b := opB fe d a b
  ensureSort _ d e := opS fe d e
  whnf _ d e := opE fe (·.whnf) d e

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

/-- `nestedRuleShape` through the index. -/
def nestedRuleShapeF (fe' feSelf : FEnv) (cvName : Name)
    (lps : List Name) (tyA : Expr) (mI rP cnP j : Nat) :
    Option (List Level × List Expr) :=
  if (fe'.findCV? ((cvName.str "_model").str s!"iota_{j}")).isSome ∧
      mI = rP then
    match tyA.stripPis mI with
    | some (_, .forallE _ dom _ _) =>
      match dom.getAppFn with
      | .const _D lvls =>
        let pins := dom.getAppArgs
        if pins.length = cnP ∧
            pins.all (fun p => !p.hasFvar && p.looseBVarsBounded mI &&
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
    unless major == Expr.mkAppN (.const (f r.ctor) lvls)
        (pinsF ++ xFvs) do
      throw (.notImplemented s!"iota statement major mismatch for {cvName}")
    unless (cvj.type.stripPis (cnP + cnF)).isSome do
      throw (.notImplemented s!"iota constructor telescope for {cvName}")
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
    let (cdomsP, crestP) ← unwrapOr (Expr.instPisAt pinsP
        (cvj.type.instantiateLevelParams cvj.levelParams lvls))
      (.notImplemented s!"iota constructor telescope for {cvName}")
    checkTypedList ops feSelf.env depth pinsP cdomsP
    let (xFvsP, crest2P) ← unwrapOr (openPisAtFvars cnF crestP rP)
      (.notImplemented s!"iota constructor telescope for {cvName}")
    unless crest2P.getAppArgs.length == cnP do
      throw (.notImplemented s!"iota constructor arity for {cvName}")
    let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvsP) rhsA)
      (.notImplemented s!"rule shape mismatch for {cvName}")
    checkDefEqList ops feSelf.env depth ((fvsP ++ xFvsP).map Expr.fvarTypeD)
      ldoms
    let rhsApplied := Expr.mkAppN (rhsA.renameConsts f) fvs
    unless ← ops.isDefEq feSelf.env depth rhsS rhsApplied do
      throw (.notImplemented s!"iota statement mismatch for {cvName}")
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
        checkIotaThmF ops fe' feSelf f cvName lps tyA mI rP j r
          cvj cnP cnF rhsA
        pure RecRuleFire.plain
      else
        checkIotaThmNF ops fe' feSelf f cvName lps tyA mI rP j r
          cvj cnP cnF rhsA
    pure { r with rhs := rhsA, ctorParams := cnP, fire := fire }

/-- `checkIotaRules` through the index. -/
def checkIotaRulesF (ops : CheckerOps m) (fe' feSelf : FEnv)
    (f : Name → Name) (cvName : Name) (lps : List Name) (tyA : Expr)
    (mI rP : Nat) : Nat → List RecRule → m (List RecRule)
  | _, [] => pure []
  | j, r :: rest => do
    let r' ← checkIotaRuleF ops fe' feSelf f cvName lps tyA mI rP j r
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
  unless domsMatchAux (fun _ e => e) rbinders cbindersR 0 0 (nP + nF) do
    throw (.notImplemented "projection rule domain mismatch")
  let some (fvsP, _) := openPisAtFvars nP pty 0
    | throw (.notImplemented "projection type telescope")
  let some (cdomsP, crestP) := Expr.instPisAt fvsP cvj.type
    | throw (.notImplemented "projection constructor telescope")
  checkDefEqList ops fe.env (nP + nF) (fvsP.map Expr.fvarTypeD) cdomsP
  let some (xFvs, _) := openPisAtFvars nF crestP nP
    | throw (.notImplemented "projection constructor telescope")
  let some (ldoms, _) := Expr.instLamsAt (fvsP ++ xFvs) rhsA
    | throw (.notImplemented "projection rule telescope")
  checkDefEqList ops fe.env (nP + nF) ((fvsP ++ xFvs).map Expr.fvarTypeD)
    ldoms
  let _rhsTy ← ops.inferType fe.env 0 rhsA
  pure rhsA

/-- `checkProjIota` through the index. -/
def checkProjIotaF (fe : FEnv) (T ctorName : Name) (lps : List Name)
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
    if directNonRecF fe p && directNoModelF fe p then some p else none
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
  let cq ← unwrapOr (openPisAtFvars p.nP cvCa.type 0)
    (.notImplemented "direct structure: constructor telescope")
  let tq ← unwrapOr (openPisAtFvars p.nP cvTa.type 0)
    (.notImplemented "direct structure: type former telescope")
  checkDirectDomsAtF ops fe 0 cq.1 (tq.1.map Expr.fvarTypeD) p.nP
  let xq ← unwrapOr (openPisAtFvars p.nF cq.2 p.nP)
    (.notImplemented "direct structure: constructor field telescope")
  unless xq.2 == Expr.mkAppN
      (.const p.cvT.name (p.cvT.levelParams.map .param)) cq.1 do
    throw (.notImplemented "direct structure: opened constructor residual")
  unless xq.1.all fun x => x.fvarTypeD.constsResolveF fe₀ do
    throw (.notImplemented "direct structure: field domain after the block")
  checkDirectFieldUnivF ops fe p.resSort p.nP xq.1 p.nF
  pure (fe.push (.ctorInfo cvCa p.nP p.nF), cvCa)

/-- `checkDirectRecTy` through the index. -/
def checkDirectRecTyF (ops : CheckerOps m) (fe : FEnv) (p : DirectParts)
    (cvTa cvCa cvRa : ConstantVal) : m Unit := do
  let T := p.cvT.name
  let lps := p.cvT.levelParams
  unless directShape T p.cvC.name lps p.elim p.nP p.nF
      cvTa.type cvCa.type cvRa.type do
    throw (.notImplemented "direct structure: annotated recursor shape")
  let (fvsP, rest) ← unwrapOr (openPisAtFvars (p.nP + 2) cvRa.type 0)
    (.notImplemented "direct structure: recursor telescope")
  let ps := fvsP.take p.nP
  let famApp := Expr.mkAppN (.const T (lps.map .param)) ps
  let (cdomsP, crest) ← unwrapOr (Expr.instPisAt ps cvCa.type)
    (.notImplemented "direct structure: constructor telescope")
  checkDirectDomsAtF ops fe 0 ps cdomsP p.nP
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
    (openPisAtFvars p.nF minfv.fvarTypeD (p.nP + 2))
    (.notImplemented "direct structure: minor telescope")
  let (cdomsF, crest2) ← unwrapOr (Expr.instPisAt xFvs crest)
    (.notImplemented "direct structure: constructor field telescope")
  checkDirectDomsAtF ops fe (p.nP + 2) xFvs cdomsF p.nF
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
  let (fvsP, _) ← unwrapOr (openPisAtFvars (p.nP + 2) cvRa.type 0)
    (.notImplemented "direct structure: recursor telescope")
  let (_, crest) ← unwrapOr (Expr.instPisAt (fvsP.take p.nP) cvCa.type)
    (.notImplemented "direct structure: constructor telescope")
  let (xFvs, _) ← unwrapOr (openPisAtFvars p.nF crest (p.nP + 2))
    (.notImplemented "direct structure: constructor field telescope")
  let (ldoms, _) ← unwrapOr (Expr.instLamsAt (fvsP ++ xFvs) rhsA)
    (.notImplemented "direct structure: rule telescope")
  checkDefEqList ops fe.env depth ((fvsP ++ xFvs).map Expr.fvarTypeD) ldoms
  let _rhsTy ← ops.inferType fe.env 0 rhsA
  pure rhsA


/-- `checkDirectProj` through the index. -/
def checkDirectProjF (ops : CheckerOps m) (T C : Name) (lps : List Name)
    (nP nF : Nat) (cvTa cvCa : ConstantVal) (fe : FEnv) (i : Nat) :
    m FEnv := do
  let pty ← unwrapOr (directProjTy T lps nP nF i cvTa.type cvCa.type)
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
  let (fvsP, prest) ← unwrapOr (openPisAtFvars nP ptyA 0)
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
  let (_, cresid) ← unwrapOr (Expr.instPisAt (fvsP ++ projArgs) cvCa.type)
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



/-! ## Thin phase drivers (one interned state per declaration)

Each mirrors its `Setlec/Kernel/Checker.lean` counterpart clause by
clause; the differences are exactly: `flushS` at environment
transitions, `FEnv.push` maintaining the index, and *every*
environment lookup routed through the index (task #63). -/

/-- One non-recursor member (mirrors `checkIndMember`). -/
def checkIndMemberS (blockNames : List Name) (caps : IndCaps)
    (fe : FEnv) (ci : ConstantInfo) : CheckIM FEnv := do
  flushS
  let cvA ← checkMemberValF (sharedOps fe) blockNames fe ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group (mirrors `provisionRecs`). -/
def provisionRecsS (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckIM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      flushS
      let cvA ← checkMemberValF (sharedOps feAcc) blockNames feAcc
        ci.toConstantVal
      let (feSelf, others) ← provisionRecsS blockNames
        (feAcc.push (.recInfo cvA mI rP [])) rest
      pure (feSelf, (cvA, mI, rP, rules) :: others)
    | _ => throw (.notImplemented "recursor before other block members")

/-- The recursor group (mirrors `checkIndRecs`).  All iota-rule checks
run at `envSelf` — one flush entering the phase, none inside the fold
(the fold's accumulator environments are never passed to the
operations).  The ruled recursors are installed on the `env₂` snapshot
of the index. -/
def checkIndRecsS (blockNames : List Name) (fe₂ : FEnv)
    (recs : List ConstantInfo) : CheckIM FEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    unless fe₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecsS blockNames fe₂ recs
    flushS
    checked.foldlM (fun (acc : FEnv) c => do
        let rules' ← checkIotaRulesF (sharedOps feSelf) fe₂ feSelf
          f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
      fe₂

/-- The public projection function for field `i` (mirrors
`checkProjFn`; the single-environment stages are the generic ones). -/
def checkProjFnS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckIM FEnv := do
  let (cvj, mcv) ← checkProjLookupsF (m := CheckIM) fe T ctorName lps
    nP nF i
  let pty ← checkProjTyF (m := CheckIM) fe T ctorName lps mcv.type nP nF
  checkProjShape (m := CheckIM) pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRuleF (sharedOps fe) fe pty cvj lps nP nF i
  checkProjIotaF (m := CheckIM) fe T ctorName lps cvj nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert, rhsA⟩]))

/-- One projection-function install step (mirrors `installProjFnStep`;
the artifact lookup goes through the index). -/
def installProjFnStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckIM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushS
    checkProjFnS fe T ctorName lps nP nF i
  else pure fe

/-- The Prop-fallback elimination-template entry (mirrors
`installProjTemplate`; operation-free, lookups through the index). -/
def installProjTemplateS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckIM FEnv := do
  match fe.find? (T.str "rec") with
  | some (.recInfo cvR mI rP [rule]) =>
    if (fe.find? (projFnName T i)).isNone ∧
        mI = rP ∧ rP = nP + 2 ∧ rule.ctor = ctorName ∧ i < nF then
      pure (fe.push (.projInfo ⟨T, i, lps, nP, ctorName, nF, .sort .zero,
        .zero, .zero, false,
        cvR.levelParams.length = lps.length + 1⟩))
    else pure fe
  | _ => pure fe

/-- One elimination-template install step (mirrors
`installProjTemplateStep`). -/
def installProjTemplateStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckIM FEnv :=
  if (fe.find? (projFnName T i)).isNone then
    installProjTemplateS fe T ctorName lps nP nF i
  else pure fe

/-- `checkDirectStruct` through the index. -/
def checkDirectStructS (fe : FEnv) (p : DirectParts) : CheckIM FEnv := do
  -- one `flushS` per environment transition, as everywhere else in this
  -- file: the memo caches are only valid for the environment that
  -- created them, and this driver walks five of them (the block's
  -- provisional environments plus one per projection).
  flushS
  let (fe₁, cvTa) ← checkDirectIndF (sharedOps fe) fe p
  flushS
  let (fe₂, cvCa) ← checkDirectCtorF (sharedOps fe₁) fe fe₁ p cvTa
  flushS
  let cvRa ← checkConstantValF (sharedOps fe₂) fe₂ p.cvR
  checkDirectRecTyF (sharedOps fe₂) fe₂ p cvTa cvCa cvRa
  let rhsA ← checkDirectRuleF (sharedOps fe₂) fe₂ p cvCa cvRa
  let fe₃ := fe₂.push (.recInfo cvRa (p.nP + 2) (p.nP + 2)
    [⟨p.cvC.name, p.nF, p.nP,
      if Expr.recRulePlain cvRa.type (p.nP + 2) (p.nP + 2) p.nP then
        .plain else .inert,
      rhsA⟩])
  unless (List.range p.nF).all
      (fun j => (fe₃.find? (projFnName p.cvT.name j)).isNone) do
    throw (.invalid "projection name family taken")
  (List.range p.nF).foldlM
    (fun e j => do
      flushS
      checkDirectProjF (sharedOps e) p.cvT.name p.cvC.name
        p.cvT.levelParams p.nP p.nF cvTa cvCa e j) fe₃

/-- The modeled inductive block (mirrors `checkIndDecl`), returning
the extended index. -/
def checkIndDeclSF (fe : FEnv) (block : List ConstantInfo) :
    CheckIM FEnv := do
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  unless block = nonrecs ++ recs do
    throw (.notImplemented "recursor before other block members")
  let blockNames := block.map (·.name)
  match block.filter (fun ci => match ci with
      | .indInfo _ _ => true | _ => false),
    block.filter (fun ci => match ci with
      | .ctorInfo _ _ _ => true | _ => false) with
  | [.indInfo cvT _], [.ctorInfo cvC nP nF] =>
    let caps ← pure (indBlockCapsF fe cvT cvC nP nF)
    let fe₂ ← nonrecs.foldlM (checkIndMemberS blockNames caps) fe
    let fe₃ ← checkIndRecsS blockNames fe₂ recs
    unless (List.range nF).all
        (fun j => (fe₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    let fe₄ ← (List.range nF).foldlM
      (installProjFnStepS cvT.name cvC.name cvT.levelParams nP nF) fe₃
    (List.range nF).foldlM
      (installProjTemplateStepS cvT.name cvC.name cvT.levelParams nP nF) fe₄
  | _, _ => do
    let fe₂ ← nonrecs.foldlM (checkIndMemberS blockNames {}) fe
    checkIndRecsS blockNames fe₂ recs

/-- One declaration in the shared state, index in and out (mirrors
`checkDecl` branch by branch; every lookup through the index). -/
def checkDeclSF (fe : FEnv) (d : Declaration) : CheckIM FEnv :=
  match d with
  | .defnDecl cv value hint => do
    let cv ← checkConstantValF (sharedOps fe) fe cv
    -- Rare Nat-op branch decided before the value check, so the common
    -- path does not retain `fe` across it (see `checkDeclSP`).
    if natOpNames.contains cv.name || natDivModNames.contains cv.name then
      let fe2 ← checkDefnValF (sharedOps fe) fe cv value hint
      if natOpNames.contains cv.name then
        unless natOpGuardF fe2 cv.name &&
            (natOpDeps cv.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cv.name})")
        match fe2.find? cv.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOps fe) fe.env
            ((natOpEquations 0 cv.name).map fun eq =>
              (Expr.substConst0 cv.name value' eq.1,
               Expr.substConst0 cv.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cv.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cv.name})")
      if natDivModNames.contains cv.name then
        checkDivModPinF (sharedOps fe) fe fe2 cv.name
      pure fe2
    else
      checkDefnValF (sharedOps fe) fe cv value hint
  | .thmDecl cv value => do
    let cv ← checkConstantValF (sharedOps fe) fe cv
    checkThmValF (sharedOps fe) fe cv value
  | .opaqueDecl cv value => do
    let cv ← checkConstantValF (sharedOps fe) fe cv
    let fe2 ← checkOpaqueValF (sharedOps fe) fe cv value
    if reduceOpNames.contains cv.name then
      checkReducePinF (sharedOps fe) fe fe2 cv.name value
    pure fe2
  | .axiomDecl cv => do
    let cvA ← checkConstantValF (sharedOps fe) fe cv
    if stdAxiomOkF fe cvA then
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = trustCompilerName then
      if trustCompilerOkF fe cvA then
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      if ofReduceAxOkF fe cvA then
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported compiler-trust axiom environment ({cv.name})")
    else if cvA.name = propextName ∨ cvA.name = choiceName then
      throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
    else if toleratedAxiomNames.contains cvA.name then
      pure fe
    else
      throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => do
    if kind = .quotK then
      unless fe.find? eqName = some eqA do
        throw (.notImplemented "quotient basis requires the pinned Eq basis")
    kind.declsA.foldlM installBasisDeclF fe
  | .indDecl block =>
    match directPartsF? fe block with
    | some p => checkDirectStructS fe p
    | none => checkIndDeclSF fe block

/-- The shared-state checker step the binary runs: the index is
threaded *across* declarations (built once for the whole stream; each
accepted constant is one `FEnv.push`), the interned state lives for
exactly one declaration. -/
def checkDeclSharedF (fe : FEnv) (d : Declaration) : CheckM FEnv :=
  (checkDeclSF fe d).run' {}

/-- The declaration fold of the shared-state checker. -/
def checkDeclsShared (ds : List Declaration) : CheckM Env := do
  let fe ← ds.foldlM checkDeclSharedF (mkFEnv Env.empty)
  pure fe.env

/-! ## The parsed-index drivers (task #78)

The frontend parses expression-table entries directly into the arena
(`Setlec/Frontend/Export.lean`); declarations arrive as `DeclP` — arena
indices instead of `Expr` trees — over the parse store, which seeds the
run's single `IState`.  The drivers below mirror the non-inductive
branches of `checkDeclSF` clause by clause, with

* the raw syntactic checks (`looseBVarsBounded`/`hasFvar`) and the
  post-annotate checks (`allLevelParamsDefined`/`constsResolveF`) run
  DAG-memoized on the arena,
* the entry operations called on indices (no per-entry tree interning),
* the accepted constant's annotated type/value *indices* recorded in
  the interned environment (`IState.ienv`), so later delta-unfoldings
  instantiate on the arena instead of re-interning read-back trees.

Inductive and basis blocks reuse the `Expr`-level drivers verbatim
(their inputs are read back at parse under the tree-size budget).
The state persists across declarations: `checkDeclsSP` runs the whole
fold in one `IState` seeded from the parse store, flushing the
environment-dependent caches at each declaration boundary. -/

/-- Parsed-index `ensureSort`: the interned entry plus the level
readback (the `opS` tail without the per-call tree interning). -/
def opSIx (fe : FEnv) (d : Nat) (i : EIdx) : CheckIM Level := do
  let u ← ensureSortI (coreKnotI fe checkFuel) d i
  readbackLevelM u

/-- Read back an interned expression (internal error on a dangling
index — never on the bridge invariant). -/
def readbackEM (i : EIdx) : CheckIM Expr := do
  match ← withStore (fun st => st.readbackI i) with
  | some v => pure v
  | none => throw (.internal "interned readback failed")

/-- Record an accepted constant's interned type/value in the interned
environment.  The tags (`tyE`, the value tag) must be the very objects
pushed into the environment, so the pointer validation in
`constTyAtM`/`constValAtM` succeeds. -/
def recordIConst (n : Name) (tyE : Expr) (ty : EIdx)
    (val : Option (Expr × EIdx)) : CheckIM Unit :=
  modify fun s =>
    let m := s.ienv
    let s := { s with ienv := {} }
    { s with ienv := m.insert n ⟨tyE, ty, val⟩ }

/-- `checkConstantVal` on a parsed index: the checks of
`checkConstantValF` with the syntactic passes memoized on the arena and
the operations on indices.  Returns the annotated `ConstantVal` (type
read back once, for the environment) and the annotated type's index. -/
def checkConstantValP (fe : FEnv) (cv : ConstantValP) :
    CheckIM (ConstantVal × EIdx) := do
  if (fe.find? cv.name).isSome then
    throw (.invalid s!"duplicate declaration {cv.name}")
  if reservedBasisNames.contains cv.name then
    throw (.invalid s!"reserved basis name {cv.name}")
  if cv.name.isProjFnShape then
    throw (.invalid s!"reserved projection name {cv.name}")
  unless Name.nodup cv.levelParams do
    throw (.invalid s!"duplicate universe parameters in {cv.name}")
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 cv.type) do
    throw (.invalid s!"loose bound variable in type of {cv.name}")
  if ← withStore (fun st => st.hasFvarI cv.type) then
    throw (.invalid s!"unexpected free variable in type of {cv.name}")
  let jty ← (coreKnotI fe checkFuel).annotate 0 cv.type
  unless ← withStore (fun st => st.allLevelParamsDefinedI cv.levelParams jty) do
    throw (.invalid s!"undeclared universe parameter in type of {cv.name}")
  unless ← withStore (fun st => constsResolveFI st fe jty) do
    throw (.invalid s!"unknown constant in type of {cv.name}")
  let jsty ← (coreKnotI fe checkFuel).infer 0 jty
  let _u ← opSIx fe 0 jsty
  let tyE ← readbackEM jty
  pure (⟨cv.name, cv.levelParams, tyE⟩, jty)

/-- `checkDefnValF` on parsed indices, recording the interned entry
(the value sequence is inlined flat so the simulation walk mirrors it
clause by clause). -/
def checkDefnValP (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) (hint : ReducibilityHint) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let jvt ← (coreKnotI fe checkFuel).infer 0 jv
  unless ← (coreKnotI fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in definition {cvA.name}")
  let vE ← readbackEM jv
  recordIConst cvA.name cvA.type jty (some (vE, jv))
  pure (fe.push (.defnInfo cvA vE hint))

/-- `checkThmValF` on parsed indices. -/
def checkThmValP (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  let jsty ← (coreKnotI fe checkFuel).infer 0 jty
  let ul ← opSIx fe 0 jsty
  unless (← liftFueled "level comparison" (Level.isEquiv ul .zero)) do
    throw (.invalid s!"type of theorem {cvA.name} is not a proposition")
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let jvt ← (coreKnotI fe checkFuel).infer 0 jv
  unless ← (coreKnotI fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in theorem {cvA.name}")
  let vE ← readbackEM jv
  recordIConst cvA.name cvA.type jty (some (vE, jv))
  pure (fe.push (.thmInfo cvA vE))

/-- `checkOpaqueValF` on parsed indices (stored as an `axiomInfo`,
exactly as the `Expr`-level driver does — the checked value is a
discarded realizability witness, so no value index is recorded). -/
def checkOpaqueValP (fe : FEnv) (cvA : ConstantVal) (jty : EIdx)
    (value : EIdx) : CheckIM FEnv := do
  unless ← withStore (fun st => st.looseBVarsBoundedI 0 value) do
    throw (.invalid s!"loose bound variable in value of {cvA.name}")
  if ← withStore (fun st => st.hasFvarI value) then
    throw (.invalid s!"unexpected free variable in value of {cvA.name}")
  let jv ← (coreKnotI fe checkFuel).annotate 0 value
  unless ← withStore
      (fun st => st.allLevelParamsDefinedI cvA.levelParams jv) do
    throw (.invalid s!"undeclared universe parameter in value of {cvA.name}")
  unless ← withStore (fun st => constsResolveFI st fe jv) do
    throw (.invalid s!"unknown constant in value of {cvA.name}")
  let jvt ← (coreKnotI fe checkFuel).infer 0 jv
  unless ← (coreKnotI fe checkFuel).defeq 0 jvt jty do
    throw (.invalid s!"type mismatch in opaque {cvA.name}")
  recordIConst cvA.name cvA.type jty none
  pure (fe.push (.axiomInfo cvA))

/-- One parsed declaration (mirrors `checkDeclSF` branch by branch;
inductive/basis blocks reuse the `Expr`-level drivers). -/
def checkDeclSP (fe : FEnv) (pd : DeclP) : CheckIM FEnv :=
  match pd with
  | .defnDecl cv value hint => do
    let (cvA, jty) ← checkConstantValP fe cv
    -- The Nat-op certification branch is decided *before* checking the
    -- value: the pinned certifications intentionally run against the
    -- pre-push `fe`, so the rare branch must retain `fe` across
    -- `checkDefnValP` — but on the common path that retention would
    -- force the final `fe.push` to copy the whole index bucket array
    -- (a hidden quadratic cost, one copy per definition).  The common
    -- path is therefore a tail call with `fe` consumed.
    if natOpNames.contains cvA.name || natDivModNames.contains cvA.name then
      let fe2 ← checkDefnValP fe cvA jty value hint
      if natOpNames.contains cvA.name then
        unless natOpGuardF fe2 cvA.name &&
            (natOpDeps cvA.name).all (natOpStoredOkF fe2) do
          throw (.notImplemented
            s!"nonstandard structural Nat operation environment ({cvA.name})")
        match fe2.find? cvA.name with
        | some (.defnInfo _ value' _) =>
          let ok ← certifyNatEqs (sharedOps fe) fe.env
            ((natOpEquations 0 cvA.name).map fun eq =>
              (Expr.substConst0 cvA.name value' eq.1,
               Expr.substConst0 cvA.name value' eq.2))
          unless ok do
            throw (.notImplemented
              s!"nonstandard structural Nat operation ({cvA.name})")
        | _ => throw (.internal
            s!"structural Nat operation not stored ({cvA.name})")
      if natDivModNames.contains cvA.name then
        checkDivModPinF (sharedOps fe) fe fe2 cvA.name
      pure fe2
    else
      checkDefnValP fe cvA jty value hint
  | .thmDecl cv value => do
    let (cvA, jty) ← checkConstantValP fe cv
    checkThmValP fe cvA jty value
  | .opaqueDecl cv value => do
    let (cvA, jty) ← checkConstantValP fe cv
    let fe2 ← checkOpaqueValP fe cvA jty value
    if reduceOpNames.contains cvA.name then do
      let vE ← readbackEM value
      checkReducePinF (sharedOps fe) fe fe2 cvA.name vE
    pure fe2
  | .axiomDecl cv => do
    let (cvA, jty) ← checkConstantValP fe cv
    if stdAxiomOkF fe cvA then do
      recordIConst cvA.name cvA.type jty none
      pure (fe.push (.axiomInfo cvA))
    else if cvA.name = trustCompilerName then
      if trustCompilerOkF fe cvA then do
        recordIConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported Lean.trustCompiler shape ({cv.name})")
    else if cvA.name = ofReduceNatName ∨ cvA.name = ofReduceBoolName then
      if ofReduceAxOkF fe cvA then do
        recordIConst cvA.name cvA.type jty none
        pure (fe.push (.axiomInfo cvA))
      else throw (.notImplemented
        s!"unsupported compiler-trust axiom environment ({cv.name})")
    else if cvA.name = propextName ∨ cvA.name = choiceName then
      throw (.notImplemented s!"standard axiom shape mismatch ({cv.name})")
    else if toleratedAxiomNames.contains cvA.name then
      pure fe
    else
      throw (.notImplemented s!"non-standard axiom ({cv.name})")
  | .basisDecl kind => do
    if kind = .quotK then
      unless fe.find? eqName = some eqA do
        throw (.notImplemented "quotient basis requires the pinned Eq basis")
    kind.declsA.foldlM installBasisDeclF fe
  | .indDecl block =>
    match directPartsF? fe block with
    | some p => checkDirectStructS fe p
    | none => checkIndDeclSF fe block

/-- One step of the parsed-declaration fold: validate the indices
against the parse store's range (`O(1)`; in-range indices denote under
the store invariant), flush the environment-dependent caches, check. -/
def checkDeclSPStep (n0 : Nat) (fe : FEnv) (pd : DeclP) : CheckIM FEnv := do
  unless pd.inRangeB n0 do
    throw (.internal "parsed declaration index out of range")
  flushS
  checkDeclSP fe pd

/-- The parsed-declaration checker the binary runs: the parse store is
validated once (`wfB` — the invariant every interned operation
preserves), seeds the run's single interned state, and the whole fold
shares it (the arena, the interned environment and the
environment-independent caches persist; the environment-dependent
caches are flushed per declaration). -/
def checkDeclsSP (st : EStore) (pds : List DeclP) : CheckM Env := do
  unless st.wfB do
    throw (.internal "parse store not canonical")
  let fe ← (pds.foldlM (checkDeclSPStep st.nodes.size)
    (mkFEnv Env.empty)).run' { store := st }
  pure fe.env

end Setlec
