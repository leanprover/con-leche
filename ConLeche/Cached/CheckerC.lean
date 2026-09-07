import ConLeche.Kernel.Direct.SumInstallF
import ConLeche.Kernel.Direct.RecInstallF
import ConLeche.Cached.CoreC

/-!
# The cached declaration driver

The declaration checker *above* `CheckerOps` is shared verbatim with
the generic one: only the core is replaced.  What lives here is the
thin per-declaration phase-driver layer at `CheckCM`, plus the
entry-point record over the cached core.

What the layer is *for*: the per-declaration phase driver that the
parsed-declaration driver (`ConLeche/Cached/ParsedC.lean`) and its bridges
consume — at a `CheckMode` (the trusted twin `ParsedT`/`CoreT` retired
2026-09-06, the configuration record that briefly stood in for the mode
retired at task #185; see `ParsedC.lean`'s header).  The `Expr`-typed
shared fold `checkDeclsShared` went at task #172 with the interned
checker it existed to compare against.
-/

namespace ConLeche.Cached

open ConLeche

/-! ### The direct installers' walkers (task #214) -/

/-- `Expr.instPisAtLift` at the memoised substitution. -/
def instPisAtLiftC : List Expr → Expr → Option Expr
  | [], e => some e
  | a :: as, .forallE _ body _ => instPisAtLiftC as (ExprC.instantiate1Lift body a)
  | _ :: _, _ => none

/-- `directProjBodiesGo` at the memoised substitution. -/
def directProjBodiesGoC (T : Name) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body _ =>
    (directProjBodiesGoC T k (i + 1) (ExprC.instantiate1Lift body (directProjArgP T i))).map
      (fdom :: ·)
  | _ + 1, _, _ => none

/-- `directProjBodies` at the memoised substitution
(`directProjBodiesC_eq`). -/
def directProjBodiesC (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match instPisAtLiftC (directProjPs nP) cty with
  | some r => (directProjBodiesGoC T nF 0 r).map List.toArray
  | none => none

/-- **The cached driver's walkers**: the memoised constant-resolution
gate (`constsResolveFC`, verified at `constsResolveFC_spec`) and the
memoised projection-body builder; equal to `DirectWalkers.plain`
(`directWalkersC_eq_plain`). -/
def directWalkersC : DirectWalkers := ⟨constsResolveFC, directProjBodiesC⟩

variable (mode : CheckMode)

/-! ## The entry-point record over the cached core

`opE`/`opB`/`opS` used to convert their `Expr` arguments in and their
results out.  Since task #172 B3a there is one expression type, so they
pass their arguments through — measured at −3.5 % / −3.8 % instructions
on `init-prelude` / `app-lam`, which is where that batch's win came
from. -/

/-- Shared-state unary entry point: run the cached knot. -/
def opE (fe : FEnv) (pick : CoreFnsI → Nat → ExprC → CheckCM ExprC)
    (d : Nat) (e : Expr) : CheckCM Expr := do
  pick (coreKnotI mode fe checkFuel) d e

/-- Shared-state definitional-equality entry point. -/
def opB (fe : FEnv) (d : Nat) (a b : Expr) : CheckCM Bool :=
  (coreKnotI mode fe checkFuel).defeq d a b

/-- Shared-state sort-ensuring entry point. -/
def opS (fe : FEnv) (d : Nat) (e : Expr) : CheckCM Level :=
  ensureSortI (coreKnotI mode fe checkFuel) d e

/-- The per-declaration shared operations at a fixed environment
index. -/
def sharedOpsC (fe : FEnv) : CheckerOps CheckCM where
  annotate _ d e := opE mode fe (·.annotate) d e
  inferType _ d e := opE mode fe (·.infer) d e
  isDefEq _ d a b := opB mode fe d a b
  ensureSort _ d e := opS mode fe d e
  whnf _ d e := opE mode fe (·.whnf) d e

/-! ## Thin phase drivers (one `CState` per declaration)

Each mirrors its `ConLeche/Kernel/Checker.lean` counterpart clause by
clause; the differences are exactly: `flushC` at environment
transitions, `FEnv.push` maintaining the index, and *every*
environment lookup routed through the index (task #63). -/

/-- One non-recursor member (mirrors `checkIndMember`). -/
def checkIndMemberS (blockNames : List Name) (caps : IndCaps)
    (fe : FEnv) (ci : ConstantInfo) : CheckCM FEnv := do
  flushC
  let cvA ← checkMemberValF (sharedOpsC mode fe) blockNames fe ci.toConstantVal
  match ci with
  | .indInfo _ _ => pure (fe.push (.indInfo cvA caps))
  | .ctorInfo _ nP nF => pure (fe.push (.ctorInfo cvA nP nF))
  | _ => throw (.invalid s!"non-inductive member {cvA.name} in block")

/-- Phase 0 of the recursor group (mirrors `provisionRecs`). -/
def provisionRecsS (blockNames : List Name) :
    FEnv → List ConstantInfo →
    CheckCM (FEnv × List (ConstantVal × Nat × Nat × List RecRule))
  | feAcc, [] => pure (feAcc, [])
  | feAcc, ci :: rest =>
    match ci with
    | .recInfo _ mI rP rules => do
      flushC
      let cvA ← checkMemberValF (sharedOpsC mode feAcc) blockNames feAcc
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
    (recs : List ConstantInfo) : CheckCM FEnv := do
  if recs.isEmpty then
    pure fe₂
  else do
    let f : Name → Name := fun n =>
      if blockNames.contains n then n.str "_model" else n
    unless fe₂.find? eqName = some eqA do
      throw (.notImplemented "modeled recursor requires the pinned Eq basis")
    let (feSelf, checked) ← provisionRecsS mode blockNames fe₂ recs
    flushC
    checked.foldlM (fun (acc : FEnv) c => do
        let rules' ← checkIotaRulesF mode (sharedOpsC mode feSelf) fe₂ feSelf
          f c.1.name c.1.levelParams c.1.type c.2.1 c.2.2.1 0 c.2.2.2
        pure (acc.push (.recInfo c.1 c.2.1 c.2.2.1 rules')))
      fe₂

/-- The public projection function for field `i` (mirrors
`checkProjFn`; the single-environment stages are the generic ones). -/
def checkProjFnS (fe : FEnv) (T ctorName : Name) (lps : List Name)
    (nP nF i : Nat) : CheckCM FEnv := do
  let (cvj, mcv) ← checkProjLookupsF (m := CheckCM) fe T ctorName lps
    nP nF i
  let pty ← checkProjTyF (m := CheckCM) fe T ctorName lps mcv.type nP nF
  checkProjShape (m := CheckCM) pty cvj.type nP nF
  unless i < nF do
    throw (.invalid "projection index out of range")
  let rhsA ← checkProjRuleF (sharedOpsC mode fe) fe pty cvj lps nP nF i
  checkProjIotaF mode (sharedOpsC mode fe) fe T ctorName lps cvj nP nF i
  pure (fe.push (.recInfo ⟨projFnName T i, lps, pty⟩ nP nP
    [⟨ctorName, nF, nP,
      if Expr.recRulePlain pty nP nP nP then .plain else .inert, rhsA⟩]))

/-- One projection-function install step (mirrors `installProjFnStep`;
the artifact lookup goes through the index). -/
def installProjFnStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckCM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushC
    checkProjFnS mode fe T ctorName lps nP nF i
  else pure fe

/-- `checkDirectFix` through the index (task #188).  The former's and
the constructors' stages are the sum route's mirrors, the resolution
guard pointed at the former's environment; one flush per environment
transition. -/
def checkDirectFixS (fe : FEnv) (p₀ : DirectFixParts) : CheckCM FEnv := do
  if p₀.kinds.any (fun ks => ks.any (· == .negative)) then
    throw (.invalid "direct rec: non positive occurrence of the inductive type")
  unless (p₀.ctors.map (·.1.name)).Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  flushC
  let (fe₁, cvTa, p₁) ← checkDirectSumIndF (sharedOpsC mode fe) fe p₀.toDirectSumParts
    (fun p₁ => directFixCaps (p₀.complete p₁))
  let p := p₀.complete p₁
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  flushC
  let tq ← unwrapOr (openPisAtFvars (p.nP + p.nIdx) cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← checkDirectFieldSortsIF (sharedOpsC mode fe₁) fe₁ true false p.resSort p.nP
    (tq.1.drop p.nP) [] p.nIdx
  let (ctorsA, sortss) ← checkDirectSumCtorsF (sharedOpsC mode fe₁) fe₁ fe₁ p.cvT.name
    p.cvT.levelParams p.nP p.nIdx p.resSort p.isProp p.large cvTa p.ctors
  unless directFixFieldsOkF directWalkersC fe p.cvT.name p.cvT.levelParams p.nP p.nIdx ctorsA
      p.kinds do
    throw (.internal "direct rec: field kinds")
  let fe₂ := consSumCtorsF p.nP ctorsA fe₁
  flushC
  let (cvRa, rhss) ← checkDirectFixRecF (sharedOpsC mode fe₂) directWalkersC fe₂ p cvTa ctorsA
  -- the projection table at a structure-like block (task #210 Part A)
  checkDirectFixTableF (m := CheckCM) directWalkersC p ctorsA sortss (fe₂.push (.recInfo cvRa p.majorIdx
    p.rulePrefix (directSumRules p.nP p.majorIdx p.rulePrefix cvRa.type ctorsA rhss)))

/-- The modeled inductive block (mirrors `checkIndDecl`), returning
the extended index. -/
def checkIndDeclSF (fe : FEnv) (block : List ConstantInfo) :
    CheckCM FEnv := do
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
    let caps ← pure (indBlockCapsF mode fe cvT cvC nP nF)
    let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames caps) fe
    let fe₃ ← checkIndRecsS mode blockNames fe₂ recs
    unless ctorResidualOkF mode fe₃ cvT.name cvC.name cvT.levelParams nP nF
        caps.eta do
      throw (.notImplemented "modeled structure: eta constructor residual")
    unless (List.range nF).all
        (fun j => (fe₃.find? (projFnName cvT.name j)).isNone) do
      throw (.invalid "projection name family taken")
    if ctorTargetsFam cvC.type cvT.name cvT.levelParams nP nF then
      (List.range nF).foldlM
        (installProjFnStepS mode cvT.name cvC.name cvT.levelParams nP nF)
        fe₃
    else pure fe₃
  | _, _ => do
    let fe₂ ← nonrecs.foldlM (checkIndMemberS mode blockNames {}) fe
    checkIndRecsS mode blockNames fe₂ recs

end ConLeche.Cached
