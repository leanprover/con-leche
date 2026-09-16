module

public import ConLeche.Kernel.Inductives.MutualInstallF
public import ConLeche.Kernel.Inductives.NestedInstallF
public import ConLeche.Cached.CoreC

@[expose] public section

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
  | a :: as, .forallE _ body _ => instPisAtLiftC as (Expr.instantiate1LiftC body a)
  | _ :: _, _ => none

/-- `structProjBodiesGo` at the memoised substitution. -/
def structProjBodiesGoC (T : Name) : Nat → Nat → Expr → Option (List Expr)
  | 0, _, _ => some []
  | k + 1, i, .forallE fdom body _ =>
    (structProjBodiesGoC T k (i + 1) (Expr.instantiate1LiftC body (structProjArgP T i))).map
      (fdom :: ·)
  | _ + 1, _, _ => none

/-- `structProjBodies` at the memoised substitution
(`structProjBodiesC_eq`). -/
def structProjBodiesC (T : Name) (nP nF : Nat) (cty : Expr) : Option (Array Expr) :=
  match instPisAtLiftC (structProjPs nP) cty with
  | some r => (structProjBodiesGoC T nF 0 r).map List.toArray
  | none => none

/-- **The cached driver's walkers**: the memoised constant-resolution
gate (`constsResolveFC`, verified at `constsResolveFC_spec`) and the
memoised projection-body builder; equal to `StructWalkers.plain`
(`structWalkersC_eq_plain`). -/
def structWalkersC : StructWalkers := ⟨constsResolveFC, structProjBodiesC⟩

variable (mode : CheckMode)

/-! ## The entry-point record over the cached core

`opE`/`opB`/`opS` used to convert their `Expr` arguments in and their
results out.  Since task #172 B3a there is one expression type, so they
pass their arguments through — measured at −3.5 % / −3.8 % instructions
on `init-prelude` / `app-lam`, which is where that batch's win came
from. -/

/-- Shared-state unary entry point: run the cached knot. -/
def opE (fe : FEnv) (pick : CoreFnsI → Nat → Expr → CheckCM Expr)
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
  -- the executable's instantiation delivers the attempt's outcome to
  -- the continuation (the decline message names what each pin variant
  -- failed on); after an error the state is the PRE-attempt one — the
  -- memo entries the failed attempt wrote are discarded with it
  orElse x k := fun s => match x s with
    | .ok (true, s') => .ok ((), s')
    | .ok (false, s') => k none s'
    | .error e => k (some e) s

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
    [projFnRule fe.find? T ctorName pty nP nF i rhsA]))

/-- One projection-function install step (mirrors `installProjFnStep`;
the artifact lookup goes through the index). -/
def installProjFnStepS (T ctorName : Name) (lps : List Name)
    (nP nF : Nat) (fe : FEnv) (i : Nat) : CheckCM FEnv := do
  if (fe.find? (projModelName T i)).isSome then do
    flushC
    checkProjFnS mode fe T ctorName lps nP nF i
  else pure fe

/-- `checkNativePass` through the index (task #268): one flush per
environment transition. -/
def checkNativePassS (fe : FEnv) (p₀ : NativeParts) (isRec : Bool) :
    CheckCM (NativePass FEnv × Bool) := do
  let (fe₁, cvTa, p₁) ← checkSumIndF (sharedOpsC mode fe) fe p₀.toInductiveShape
    (fun p₁ => nativeCapsAt p₁ isRec)
  let pC := p₀.complete p₁
  flushC
  let (ctorsA, sortss) ← checkSumCtorsF (sharedOpsC mode fe₁) fe₁ fe₁ pC.cvT.name
    pC.cvT.levelParams pC.nP pC.nIdx pC.resSort pC.isProp pC.large cvTa pC.ctors
  let kinds ← classifyFixKinds (m := CheckCM) pC.cvT.name pC.cvT.levelParams pC.nP pC.nIdx
    ctorsA
  let p := pC.withKinds kinds
  pure (⟨fe₁, cvTa, p, ctorsA, sortss⟩, nativeCaps p == nativeCapsAt p₁ isRec)

/-- `checkNativeTail` through the index: one flush entering the
recursor's environment. -/
def checkNativeTailS (fe : FEnv) (q : NativePass FEnv) : CheckCM FEnv := do
  let p := q.p
  if p.large && !p.resSort.isNeverZero && decide (2 ≤ p.ctors.length) then
    throw (.invalid "direct rec: large eliminator on a multi-constructor inductive \
      whose sort may be Prop")
  let tq ← unwrapOr (openPisAtFvars (p.nP + p.nIdx) q.cvTa.type 0)
    (.internal "direct rec: type former telescope")
  let _isorts ← checkStructFieldSortsIF (sharedOpsC mode q.env₁) q.env₁ true false p.resSort
    p.nP (tq.1.drop p.nP) [] p.nIdx
  unless nativeFieldsOkF structWalkersC fe p.cvT.name p.cvT.levelParams p.nP p.nIdx q.ctorsA
      p.kinds do
    throw (.internal "direct rec: field kinds")
  unless nativeRulesOk p.cvR.name (p.cvR.levelParams.map .param) .never p.nP p.ctors.length
      q.ctorsA p.kinds p.rhss p.cvR.type do
    throw (.invalid "direct rec: recursor rules are not the generated ones")
  let fe₂ := consSumCtorsF p.nP q.ctorsA q.env₁
  flushC
  let (cvRa, rhss) ← checkNativeRecF (sharedOpsC mode fe₂) structWalkersC fe₂ p q.cvTa q.ctorsA
  -- the projection table at a structure-like block (task #210 Part A)
  checkNativeTableF (m := CheckCM) structWalkersC p q.ctorsA q.sortss (fe₂.push (.recInfo cvRa
    p.majorIdx p.rulePrefix (sumRules fe₂.find? cvRa.name p.nP p.majorIdx p.rulePrefix
      cvRa.type q.ctorsA rhss)))

/-- `checkNative` through the index (task #188): the pass at the
syntactic `is_rec` reading, again at the classified verdict where the
reading overshot (task #268), and the install after it. -/
def checkNativeS (fe : FEnv) (p₀ : NativeParts) : CheckCM FEnv := do
  unless (p₀.ctors.map (·.1.name)).Nodup do
    throw (.invalid "direct rec: duplicate constructor")
  flushC
  let (q, settled) ← checkNativePassS mode fe p₀ (nativeRawRec p₀)
  if settled then checkNativeTailS mode fe q
  else do
    flushC
    let (q', settled') ← checkNativePassS mode fe p₀ (nativeIsRec q.p.kinds)
    unless settled' do
      throw (.internal "direct rec: the capability record did not settle")
    checkNativeTailS mode fe q'

/-- `mutualFormerChecks` through the index: EVERY member's former is
checked at the block's starting index, so the whole stage runs at ONE
environment and needs no flush of its own (`mutualFormersS` flushes
once before it).  The pure comparand is `mutualFormerChecks`. -/
def mutualFormerChecksS (fe : FEnv) (nP : Nat) (auxRoute : Bool := false) :
    List (ConstantVal × Nat) → CheckCM (List MutualFormerA)
  | [] => pure []
  | (cv, nIdx) :: rest => do
    -- the grade (task #279 K.10/K.12, through the index): at `auxRoute`
    -- the caller built every member of this block out of annotated
    -- pieces, so the walk is skipped and the stored type is the given one
    let cvTa₀ ←
      if auxRoute then checkConstantValPreF (sharedOpsC mode fe) fe cv
      else checkConstantValF (sharedOpsC mode fe) fe cv
    let (cvTa, s) ← checkSumTeleF (sharedOpsC mode fe) fe cv (nP + nIdx) cvTa₀
    let (_, tbody) ← unwrapOr (cvTa.type.stripPis (nP + nIdx))
      (.internal "mutual: type former telescope")
    unless tbody == Expr.sort s do
      throw (.internal "mutual: type former result sort")
    let fs ← mutualFormerChecksS fe nP auxRoute rest
    pure (⟨cvTa, nIdx, s⟩ :: fs)

/-- `mutualFormers` through the index: ONE flush entering the stage
(the driver's environment changed before it), the checks at that one
index, the conses afterwards — no operation runs between an
environment change and a flush. -/
def mutualFormersS (nP : Nat) (formers : List (ConstantVal × Nat)) (auxRoute : Bool)
    (fe : FEnv) : CheckCM (FEnv × List MutualFormerA) := do
  flushC
  let fms ← mutualFormerChecksS mode fe nP auxRoute formers
  pure (consMutualFormersF fms fe, fms)

/-- `checkMutualCore` through the index (task #278): the stages at the
index's environment, one flush per environment transition. -/
def checkMutualCoreS (fe : FEnv) (b : MutualBlock)
    (streamRecs : Option (List (ConstantVal × List RecRule)))
    (auxRoute : Bool) : CheckCM FEnv := do
  let nP := b.nP
  mutualShapeOk (m := CheckCM) b
  let (fe₁, fms) ← mutualFormersS mode nP b.formers auxRoute fe
  let f₀ ← unwrapOr fms[0]? (.internal "mutual: no member")
  flushC
  let tq₀ ← unwrapOr (openPisAtFvars nP f₀.cvTa.type 0) (.internal "mutual: former telescope")
  mutualCrossChecks (sharedOpsC mode fe₁) fe₁.env nP f₀ (tq₀.1.map Expr.fvarTypeD) fms
  unless b.large == f₀.s.isNeverZero do
    throw (.invalid "mutual: the recursors' level parameters are not the generated ones")
  let isProp := Level.isEquiv f₀.s .zero == some true
  let (ctorsA, sortss) ← checkMutualCtorsF (sharedOpsC mode fe₁) structWalkersC fe₁ b fms isProp
    auxRoute b.ctors
  let kinds ← classifyMutualKinds (m := CheckCM) b.members3 b.lps nP ctorsA
  unless mutualFieldsOkF structWalkersC fe b.members3 b.lps nP ctorsA kinds do
    throw (.internal "mutual: field kinds")
  let fe₂ := consMutualCtorsF nP ctorsA fe₁
  flushC
  let (formers4, ctors4) := mutualGenData b fms ctorsA kinds
  let cvRas ← checkMutualRecTysF (sharedOpsC mode fe₂) structWalkersC fe₂ b formers4 ctors4
    streamRecs b.k
  let feR := provisionMutualRecsF b fms cvRas.zipIdx fe₂
  let rulesOf ← checkMutualAllRulesF (m := CheckCM) structWalkersC feR b formers4 ctors4
    streamRecs b.k
  let fe₃ := storeMutualRecsF fe₂ b fms rulesOf cvRas.zipIdx fe₂
  flushC
  mutualTablesF (m := CheckCM) structWalkersC b ctorsA sortss fms.zipIdx fe₃

/-- `checkMutual` through the index. -/
def checkMutualS (fe : FEnv) (p : MutualParts) : CheckCM FEnv := do
  unless p.recPinned do
    throw (.invalid "mutual: a recursor record is not the generated recursor")
  checkMutualCoreS mode fe p.toBlock (some (p.members.map fun mb => (mb.cvR, mb.rules)))
    false

/-- **`checkNested` through the index** (task #279 K.20): the nested
route's stages at the cached driver's `FEnv`, one flush per environment
transition.  The pure readers — the elimination, the container
recovery, the read-back, the restore table and the fire shape — take
`fe.env`, which is that index's own environment (the mutual mirror does
the same for `mutualCrossChecks`); every front door and every cons goes
through the index.

The scratch install is `checkMutualCoreS … true`: the grade K.12 gave
the whole auxiliary block, here through the index. -/
def checkNestedS (fe : FEnv) (p : NestedParts) : CheckCM FEnv := do
  let ctorTypes := p.ctors.map (fun c => c.cv.type)
  unless p.formers.all (fun f => !f.1.type.mentionsNestedAux) &&
      ctorTypes.all (fun t => !t.mentionsNestedAux) do
    throw (.invalid "invalid declaration, it uses the reserved prefix '_nested'")
  unless uniformIndOccsOk p.memberNames (p.lps.map Level.param) p.nP ctorTypes do
    throw (.invalid "invalid occurrence of datatype being declared: it must be applied \
      to the parameters and universe levels of the mutual declaration")
  flushC
  let fmsA ← nestedAnnotFormersF (sharedOpsC mode fe) fe p.nP p.formers
  let feF := nestedFormerEnvF fmsA fe
  flushC
  let ctorsA ← nestedAnnotCtorsF (sharedOpsC mode feF) feF p.ctors
  let st ← nestedLift (m := CheckCM)
    (elimNested fe.env p.nP p.lps (nestedTypes0 p fmsA ctorsA))
  unless st.pins.length == p.numNested do
    throw (.invalid s!"the block carries {p.numNested} recursor records past its \
      {p.k} type formers; the elimination finds {st.pins.length} nested occurrences")
  unless copiesFresh fe.env p.k st do
    throw (.invalid "nested: an auxiliary type generated by the elimination names a \
      constant the environment already carries")
  unless nestedContainersOk fe.env st.pins do
    throw (.internal "nested: a container the elimination pinned fails a fact its own \
      install established")
  let b ← unwrapOr (auxBlock p st)
    (.invalid "invalid nested inductive datatype, ill-formed declaration")
  let feAux ← checkMutualCoreS mode fe b none true
  let stored ← unwrapOr (auxStoredAll feAux.env b b.k)
    (.internal "nested: the auxiliary block's stored records")
  let R := restoreTbl p st
  let members := stored.take p.k
  let mimics := stored.drop p.k
  unless pinsClosed p.nP st.pins do
    throw (.invalid "nested: a pin is not closed at the block's parameter telescope")
  flushC
  nestedPinsOk (sharedOpsC mode feAux) feAux.env p.nP st.pins
  unless members.all (fun a => !a.caps.eta && (fe.find? a.cvTa.name).isNone) do
    throw (.internal "nested: a restored former is not a fresh non-eta family")
  -- the copies' sources (K.28), as in the pure route
  unless nestedCopySrcOk fe.env p st do
    throw (.internal "nested: a minted auxiliary type is not the copy of the container \
      it records")
  -- the pins' mint groups (K.29), as in the pure route
  unless nestedGroupsOk fe.env p st do
    throw (.internal "nested: a pin's mint group is not the container's group as minted")
  -- the pins' scope (K.30), as in the pure route
  unless pinsScoped p.nP st do
    throw (.internal "nested: a pin's free variables are not the block's parameter openers")
  -- the field kinds at the pins (§U.1 (c) fact 6), as in the pure route
  unless nestedPinKindsOk p b st stored do
    throw (.internal "nested: a stored field at a pin is not classified ordinary, \
      recursive or reflexive into the block")
  -- the RESTORED block is built on the PRE-BLOCK index, not the scratch
  -- one: only the restored constants are stored
  let fe₁ := consNestedFormersF members fe
  -- post-check (a) a third time (K.30), at the restored formers' index
  flushC
  nestedPinsOk (sharedOpsC mode fe₁) fe₁.env p.nP st.pins
  flushC
  let ctorsR ← members.mapM fun a =>
    restoreCtorsF (sharedOpsC mode fe₁) fe₁ R p.lps a.ctors
  let fe₂ := consNestedCtorsF ctorsR.flatten fe₁
  flushC
  let memberNames := (List.range p.k).map fun mIdx =>
    ((p.formers.getD mIdx default).1.name.str "rec")
  let mimicNames := (List.range p.numNested).map p.mimicRecName
  let cvRms ← restoreRecTysF (sharedOpsC mode fe₂) fe₂ R p.lps memberNames members
  let cvRns ← restoreRecTysF (sharedOpsC mode fe₂) fe₂ R p.lps mimicNames mimics
  let provisions := (cvRms.zip (members.map fun a => (a.mI, a.rP)))
    ++ (cvRns.zip (mimics.map fun a => (a.mI, a.rP)))
  let feR := provisionNestedRecsF provisions fe₂
  flushC
  let rulesM ← (cvRms.zip members).mapM fun (cvRa, a) =>
    restoreRulesF (sharedOpsC mode feR) feR R cvRa.levelParams cvRa.name false cvRa.type
      a.mI a.rP a.rules
  let rulesN ← (cvRns.zip mimics).mapM fun (cvRa, a) =>
    restoreRulesF (sharedOpsC mode feR) feR R cvRa.levelParams cvRa.name true cvRa.type
      a.mI a.rP a.rules
  let fe₃ := storeNestedRecsF
    ((cvRms.zip (members.zip rulesM)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))
      ++ (cvRns.zip (mimics.zip rulesN)).map (fun (cv, a, rs) => (cv, a.mI, a.rP, rs))) fe₂
  flushC
  let fe₄ ← nestedTablesF (m := CheckCM) structWalkersC
    ((members.zip ctorsR).zipIdx.map fun ((a, cs), mIdx) =>
      ((p.formers.getD mIdx default).1.name, a.tbl, cs)) fe₃
  flushC
  nestedPinsOk (sharedOpsC mode fe₄) fe₄.env p.nP st.pins
  unless p.memberRecs.length == cvRms.length && p.mimicRecs.length == cvRns.length do
    throw (.invalid "nested: the block's recursor records are not the generated ones")
  let ownOf : Nat → List (Nat × Nat) := fun mIdx =>
    (b.ownCtors mIdx).map fun (J, c) => (J, c.nF)
  let mRows := ((p.memberRecs.zip cvRms).zip rulesM).zipIdx.map
    (fun (((sr, cv), rs), mIdx) => (sr, ownOf mIdx, cv, rs))
  let nRows := ((p.mimicRecs.zip cvRns).zip rulesN).zipIdx.map
    (fun (((sr, cv), rs), j) => (sr, ownOf (p.k + j), cv, rs))
  nestedRecsOkF (sharedOpsC mode fe₂) fe₂ p.nP b.k b.n (mRows ++ nRows)
  pure fe₄

/-- The modeled inductive block (mirrors `checkModeled`), returning
the extended index. -/
def checkIndDeclSF (fe : FEnv) (block : List ConstantInfo) :
    CheckCM FEnv := do
  let recs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => true | _ => false)
  let nonrecs := block.filter (fun ci => match ci with
    | .recInfo _ _ _ _ => false | _ => true)
  -- the tag pass, not the derived structural equality on the members'
  -- types (`ConLeche/Kernel/Env.lean`): the STATEMENT is unchanged, the
  -- decision is `recsFormSuffix`
  unless @decide _ (blockRecSuffixDec block) do
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
