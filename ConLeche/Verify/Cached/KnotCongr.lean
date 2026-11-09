module

public import ConLeche.Cached.IndPass

public section

/-!
# The knot reads the index only through `find?` and `findTable?`

The cached core only ever asks an `FEnv` questions through
`FEnv.find?` and, at a `.proj` node, `FEnv.findTable?`: every guard,
every stored-constant read and every rule lookup below goes through
those two functions.  This
file proves it, one congruence lemma per `fe`-taking function of
`ConLeche/Kernel/FEnv.lean` and `ConLeche/Cached/*` reachable from the
knot's bodies, bottom-up, landing on `coreKnotI_congr`.

The consumer is the record's job (`ConLeche/Verify/Cached/ViewCongr.lean`): a job checks a record
at a view of the stream's index whose lookups are the fold's index's, so `coreKnotI_congr` says they
run the *same* core.

**Why this is `Verify/Cached`, not `Cached`.**  The driver (`ConLeche/Driver/*`) carries the proof
that the jobs passing is an accept of the fold, and that proof rests on this congruence; the driver
may import `Verify/*` (maintainer's ruling, 2026-10-08), so the file sits where a proof about kernel
functions that needs no model belongs.  It imports only the cached checker — nothing from the theory — and opens a plain
`public section` (it defines nothing for anyone to unfold).
-/

namespace ConLeche.Cached

variable {mode : CheckMode} {eager : Bool} {fe₁ fe₂ : FEnv}

/-! ## The table component (task #362)

A table push touches the table map alone, a constant push the
constant index alone: what the congruences below read off a push. -/

/-- A table push leaves the constant lookups alone. -/
theorem FEnv.find?_pushTable (fe : FEnv) (t : ProjTable) :
    (fe.pushTable t).find? = fe.find? := rfl

theorem FEnv.find?_pushTables :
    ∀ (Q : List ProjTable) (fe : FEnv), (FEnv.pushTables Q fe).find? = fe.find?
  | [], _ => rfl
  | t :: Q, fe => (FEnv.find?_pushTables Q (fe.pushTable t)).trans (FEnv.find?_pushTable fe t)

/-- A table install answers its structure's name in the raw table
lookup, and leaves every other raw lookup alone. -/
theorem FEnv.rawTable?_pushTable (fe : FEnv) (t : ProjTable) (T : Name) :
    (fe.pushTable t).rawTable? T = if t.structName = T then some t else fe.rawTable? T := by
  simp only [FEnv.rawTable?, FEnv.pushTable, Std.HashMap.getElem?_insert, beq_iff_eq]
  by_cases hT : t.structName = T <;> simp [hT]
theorem FEnv.rawTable?_push (fe : FEnv) (ci : ConstantInfo) :
    (fe.push ci).rawTable? = fe.rawTable? := rfl

theorem FEnv.rawTable?_pushAll :
    ∀ (L : List ConstantInfo) (fe : FEnv), (FEnv.pushAll L fe).rawTable? = fe.rawTable?
  | [], _ => rfl
  | ci :: L, fe => (FEnv.rawTable?_pushAll L (fe.push ci)).trans (FEnv.rawTable?_push fe ci)

/-! ## The environment-index guards (`ConLeche/Kernel/FEnv.lean`) -/

/-- `FEnv.findProj?` reads `fe` only through `findTable?`. -/
theorem findProj?_congr (_hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) :
    fe₁.findProj? = fe₂.findProj? := by
  funext T i; unfold FEnv.findProj?; simp only [htb]

/-- `FEnv.towerSlotsAllF` reads `fe` only through `find?` and `findTable?`. -/
theorem towerSlotsAllF_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) :
    fe₁.towerSlotsAllF = fe₂.towerSlotsAllF := by
  funext T nF; unfold FEnv.towerSlotsAllF; simp only [findProj?_congr hfe htb]

/-- `FEnv.andRescueSlotsF` reads `fe` only through `find?` and `findTable?`. -/
theorem andRescueSlotsF_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) :
    fe₁.andRescueSlotsF = fe₂.andRescueSlotsF := by
  funext ctor nP; unfold FEnv.andRescueSlotsF
  simp only [findProj?_congr hfe htb]

/-- `natLitStoredF` reads `fe` only through `find?`. -/
theorem natLitStoredF_congr (hfe : fe₁.find? = fe₂.find?) :
    natLitStoredF fe₁ = natLitStoredF fe₂ := by
  unfold natLitStoredF; simp only [hfe]

/-- `strLitStoredF` reads `fe` only through `find?`. -/
theorem strLitStoredF_congr (hfe : fe₁.find? = fe₂.find?) :
    strLitStoredF fe₁ = strLitStoredF fe₂ := by
  unfold strLitStoredF; simp only [hfe, natLitStoredF_congr hfe]

/-! ## The cached guards and stored-constant reads
(`ConLeche/Cached/StateC.lean`) -/

/-- `isCtorAppC` reads `fe` only through `find?`. -/
theorem isCtorAppC_congr (hfe : fe₁.find? = fe₂.find?) :
    isCtorAppC fe₁ = isCtorAppC fe₂ := by
  funext e; unfold isCtorAppC; simp only [hfe]

/-- `headHintC` reads `fe` only through `find?`. -/
theorem headHintC_congr (hfe : fe₁.find? = fe₂.find?) :
    headHintC fe₁ = headHintC fe₂ := by
  funext e; unfold headHintC; simp only [hfe]

/-- `unfoldableHeadC` reads `fe` only through `find?`. -/
theorem unfoldableHeadC_congr (hfe : fe₁.find? = fe₂.find?) :
    unfoldableHeadC fe₁ = unfoldableHeadC fe₂ := by
  funext e; unfold unfoldableHeadC; simp only [hfe]

/-- `etaCtorShapeC` reads `fe` only through `find?`. -/
theorem etaCtorShapeC_congr (hfe : fe₁.find? = fe₂.find?) :
    etaCtorShapeC fe₁ = etaCtorShapeC fe₂ := by
  funext e; unfold etaCtorShapeC; simp only [hfe]

/-- `constTyAtM` reads `fe` only through `find?`. -/
theorem constTyAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    constTyAtM fe₁ = constTyAtM fe₂ := by
  funext nI n us; unfold constTyAtM; simp only [hfe]

/-- `constValAtM` reads `fe` only through `find?`. -/
theorem constValAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    constValAtM fe₁ = constValAtM fe₂ := by
  funext nI n us; unfold constValAtM; simp only [hfe]

/-- `ruleRhsAtM` reads `fe` only through `find?`. -/
theorem ruleRhsAtM_congr (hfe : fe₁.find? = fe₂.find?) :
    ruleRhsAtM fe₁ = ruleRhsAtM fe₂ := by
  funext cI jI c j us; unfold ruleRhsAtM; simp only [hfe]

/-- The walk's plain descent reads `fe` only through `find?`. -/
theorem constsResolveFP_congr (hfe : fe₁.find? = fe₂.find?) : ∀ e : Expr,
    constsResolveFP fe₁ e = constsResolveFP fe₂ e := by
  intro e
  induction e with
  | bvar i => rw [constsResolveFP, constsResolveFP]
  | sort u => rw [constsResolveFP, constsResolveFP]
  | lit l => cases l <;> simp only [constsResolveFP, hfe]
  | const n us => simp only [constsResolveFP, hfe]
  | fvar idx ty iht => simp only [constsResolveFP, iht]
  | app f a ihf iha => simp only [constsResolveFP, ihf, iha]
  | lam ty body iht ihb => simp only [constsResolveFP, iht, ihb]
  | forallE ty body iht ihb => simp only [constsResolveFP, iht, ihb]
  | letE ty val body iht ihv ihb => simp only [constsResolveFP, iht, ihv, ihb]
  | proj sn i sub ih => simp only [constsResolveFP, hfe, ih]

/-- `constsResolveFC` reads `fe` only through `find?`. -/
theorem constsResolveFC_congr (hfe : fe₁.find? = fe₂.find?) :
    constsResolveFC fe₁ = constsResolveFC fe₂ := by
  funext e
  unfold constsResolveFC
  rw [Expr.resBool_eq, Expr.resBool_eq]
  exact constsResolveFP_congr hfe e

/-! ## The core's readers (`ConLeche/Cached/CoreC.lean`)

Each lemma equates the two partial applications at everything up to
and including `fe`, so `simp only [f_congr hfe]` rewrites a call site
inside a larger body.  A few of these functions only *thread* `fe`;
their hypothesis is still taken, because it is what pins the two
indices when the lemma is used as a rewrite rule.
-/

/-- `unfoldDefinitionI` reads `fe` only through `find?`. -/
theorem unfoldDefinitionI_congr (hfe : fe₁.find? = fe₂.find?) :
    unfoldDefinitionI fe₁ = unfoldDefinitionI fe₂ := by
  funext e; unfold unfoldDefinitionI; simp only [hfe, constValAtM_congr hfe]

/-- `litToCtorIfNatI` reads `fe` only through `find?`. -/
theorem litToCtorIfNatI_congr (hfe : fe₁.find? = fe₂.find?) :
    litToCtorIfNatI fe₁ = litToCtorIfNatI fe₂ := by
  funext e; unfold litToCtorIfNatI; simp only [natLitStoredF_congr hfe]

/-- `reduceNatI` reads `fe` only through `find?`. -/
theorem reduceNatI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    reduceNatI r fe₁ = reduceNatI r fe₂ := by
  funext depth e; unfold reduceNatI
  simp only [natLitStoredF_congr hfe]

/-- `iotaCertsFullIAux` only threads `fe`. -/
theorem iotaCertsFullIAux_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaCertsFullIAux r fe₁ = iotaCertsFullIAux r fe₂ := by
  funext depth ty acc args
  induction ty, acc, args using iotaCertsFullIAux.induct with
  | case1 ty acc => rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
  | case2 acc arg rest dom body ih =>
    rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]; simp only [ih]
  | case3 arg rest i => rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
  | case4 arg rest i head tail ih =>
    rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]; simp only [ih]
  | case5 ty acc arg rest h₁ h₂ =>
    rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
    cases ty with
    | forallE d b => exact (h₁ _ _ rfl).elim
    | bvar i => exact (h₂ _ rfl).elim
    | _ => rfl

/-- `iotaCertsFullI` only threads `fe`. -/
theorem iotaCertsFullI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaCertsFullI r fe₁ = iotaCertsFullI r fe₂ := by
  funext depth ty args; unfold iotaCertsFullI
  simp only [iotaCertsFullIAux_congr hfe]

/-- `projCertAtF` reads `fe` only through `find?`. -/
theorem projCertAtF_congr (hfe : fe₁.find? = fe₂.find?) :
    projCertAtF fe₁ = projCertAtF fe₂ := by
  funext verified c args; unfold projCertAtF projCertF
  simp only [hfe]

/-- `defEqListI` only threads `fe`. -/
theorem defEqListI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defEqListI r fe₁ = defEqListI r fe₂ := by
  funext depth as bs
  induction as generalizing bs with
  | nil => cases bs <;> rfl
  | cons a as ih =>
    cases bs with
    | nil => rfl
    | cons b bs => simp only [defEqListI, ih]

/-- `iotaIndexOkI` only threads `fe`. -/
theorem iotaIndexOkI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    iotaIndexOkI r fe₁ = iotaIndexOkI r fe₂ := by
  funext depth mI rP cnP tyCtor margs idx; unfold iotaIndexOkI
  simp only [defEqListI_congr hfe]

/-- `defeqSpineI` only threads `fe`. -/
theorem defeqSpineI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    defeqSpineI r fe₁ = defeqSpineI r fe₂ := by
  funext depth a b; unfold defeqSpineI; simp only [defEqListI_congr hfe]

/-- `propIrrelI` reads `fe` only through `find?` and `findTable?`. -/
theorem propIrrelI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    propIrrelI r fe₁ = propIrrelI r fe₂ := by
  funext depth a b; unfold propIrrelI; simp only [hfe, htb]

/-- `structEtaCertWithI` reads `fe` only through `find?` and `findTable?`. -/
theorem structEtaCertWithI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    structEtaCertWithI r fe₁ = structEtaCertWithI r fe₂ := by
  funext depth a b wtb; unfold structEtaCertWithI
  simp only [hfe, towerSlotsAllF_congr hfe htb, defEqListI_congr hfe]

/-- `etaCtorPartialC` reads `fe` only through `find?`. -/
theorem etaCtorPartialC_congr (hfe : fe₁.find? = fe₂.find?) :
    etaCtorPartialC fe₁ = etaCtorPartialC fe₂ := by
  funext e; unfold etaCtorPartialC; simp only [hfe]

/-- `structEtaFullI` reads `fe` only through `find?` and `findTable?`. -/
theorem structEtaFullI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    structEtaFullI r fe₁ = structEtaFullI r fe₂ := by
  funext depth a b; unfold structEtaFullI
  simp only [etaCtorShapeC_congr hfe, structEtaCertWithI_congr hfe htb]

/-- `structEtaExpandI` reads `fe` only through `find?` and `findTable?`. -/
theorem structEtaExpandI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    structEtaExpandI r fe₁ = structEtaExpandI r fe₂ := by
  funext k
  induction k with
  | zero => funext depth a b t; simp only [structEtaExpandI, structEtaFullI_congr hfe htb]
  | succ k ih =>
    funext depth a b t
    cases t <;> simp only [structEtaExpandI, ih]

/-- `structEtaCertI` reads `fe` only through `find?` and `findTable?`. -/
theorem structEtaCertI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    structEtaCertI r fe₁ = structEtaCertI r fe₂ := by
  funext depth a b; unfold structEtaCertI
  simp only [etaCtorShapeC_congr hfe, etaCtorPartialC_congr hfe,
    structEtaFullI_congr hfe htb, structEtaExpandI_congr hfe htb]

/-- `unitLikeStructI` reads `fe` only through `find?` and `findTable?`. -/
theorem unitLikeStructI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI)
    (ul : Nat → Expr → CheckCM Bool) :
    unitLikeStructI r ul fe₁ = unitLikeStructI r ul fe₂ := by
  have hsh : unitLikeShapeF fe₁ = unitLikeShapeF fe₂ := by
    funext w; unfold unitLikeShapeF
    simp only [hfe, towerSlotsAllF_congr hfe htb, findProj?_congr hfe htb]
  funext depth w; unfold unitLikeStructI
  simp only [hsh]

/-- `unitLikeLoopI` reads `fe` only through `find?` and `findTable?`. -/
theorem unitLikeLoopI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    unitLikeLoopI r fe₁ = unitLikeLoopI r fe₂ := by
  funext fuel
  induction fuel with
  | zero => funext depth t; simp only [unitLikeLoopI]
  | succ fuel ih =>
    funext depth t
    simp only [unitLikeLoopI, ih, unitLikeStructI_congr hfe htb]

/-- `structUnitCertI` reads `fe` only through `find?` and `findTable?`. -/
theorem structUnitCertI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    structUnitCertI r fe₁ = structUnitCertI r fe₂ := by
  funext depth a b; unfold structUnitCertI
  simp only [unitLikeLoopI_congr hfe htb]

/-- `etaCertI` does not read `fe` at all. -/
theorem etaCertI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    etaCertI mode r fe₁ = etaCertI mode r fe₂ := rfl

/-- `stuckIrrelI` reads `fe` only through `find?` and `findTable?`. -/
theorem stuckIrrelI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    stuckIrrelI r fe₁ = stuckIrrelI r fe₂ := by
  funext depth a b; unfold stuckIrrelI
  simp only [structEtaCertI_congr hfe htb, structUnitCertI_congr hfe htb]

/-- `majorToCtorI` reads `fe` only through `find?` and `findTable?`. -/
theorem majorToCtorI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    majorToCtorI mode r fe₁ = majorToCtorI mode r fe₂ := by
  funext depth recName rules major; unfold majorToCtorI
  simp only [isCtorAppC_congr hfe, hfe,
    towerSlotsAllF_congr hfe htb, andRescueSlotsF_congr hfe htb]

/-- `litMajorToCtorI` reads `fe` only through `find?`. -/
theorem litMajorToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    litMajorToCtorI r fe₁ = litMajorToCtorI r fe₂ := by
  funext depth e; unfold litMajorToCtorI
  simp only [strLitStoredF_congr hfe, litToCtorIfNatI_congr hfe]

/-- `projLitToCtorI` reads `fe` only through `find?`. -/
theorem projLitToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    projLitToCtorI r fe₁ = projLitToCtorI r fe₂ := by
  funext depth e; unfold projLitToCtorI; simp only [strLitStoredF_congr hfe]

/-- `prepareMajorI` reads `fe` only through `find?` and `findTable?`. -/
theorem prepareMajorI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    prepareMajorI mode r fe₁ = prepareMajorI mode r fe₂ := by
  funext depth recName rules major; unfold prepareMajorI
  simp only [majorToCtorI_congr hfe htb, litMajorToCtorI_congr hfe, isCtorAppC_congr hfe]

/-- `iotaArityOk` reads `fe` only through `find?`. -/
theorem iotaArityOk_congr (hfe : fe₁.find? = fe₂.find?) :
    iotaArityOk fe₁ = iotaArityOk fe₂ := by
  funext e; unfold iotaArityOk; simp only [hfe]

/-- `iotaRecI` reads `fe` only through `find?` and `findTable?`. -/
theorem iotaRecI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    iotaRecI mode r fe₁ = iotaRecI mode r fe₂ := by
  funext depth e; unfold iotaRecI
  simp only [hfe, prepareMajorI_congr hfe htb, defEqListI_congr hfe,
    constTyAtM_congr hfe, iotaCertsFullI_congr hfe,
    iotaIndexOkI_congr hfe, ruleRhsAtM_congr hfe]

/-- The peel loop only threads `fe`: it reads none of it. -/
theorem betaPeelI_congr (r : CoreFnsI) (depth : Nat) :
    betaPeelI r fe₁ depth = betaPeelI r fe₂ depth := by
  funext t acc args
  induction args generalizing t acc with
  | nil => rw [betaPeelI.eq_def, betaPeelI.eq_def]
  | cons a rest ih =>
    rw [betaPeelI.eq_def, betaPeelI.eq_def]
    cases t <;> simp only [ih]

/-- `whnfAppI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfAppI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI)
    (depth : Nat) :
    whnfAppI mode r fe₁ depth = whnfAppI mode r fe₂ depth := by
  funext v args
  induction args generalizing v with
  | nil => rw [whnfAppI.eq_def, whnfAppI.eq_def]
  | cons a rest ih =>
    rw [whnfAppI.eq_def, whnfAppI.eq_def]
    cases v <;> simp only [betaPeelI_congr (fe₁ := fe₁) (fe₂ := fe₂), iotaArityOk_congr hfe,
      iotaRecI_congr hfe htb, ih]

/-- `reduceProjCoreI` reads `fe` only through `find?` and `findTable?`. -/
theorem reduceProjCoreI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    reduceProjCoreI mode r fe₁ = reduceProjCoreI mode r fe₂ := by
  funext depth sn i c; unfold reduceProjCoreI
  simp only [projLitToCtorI_congr hfe, findProj?_congr hfe htb, projCertAtF_congr hfe]

/-- `whnfCoreStepI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfCoreStepI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    whnfCoreStepI mode r fe₁ = whnfCoreStepI mode r fe₂ := by
  funext cheap depth e; unfold whnfCoreStepI
  simp only [whnfAppI_congr hfe htb, reduceProjCoreI_congr hfe htb]

/-- `whnfCoreLoopI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfCoreLoopI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    whnfCoreLoopI mode r fe₁ = whnfCoreLoopI mode r fe₂ := by
  funext cheap depth n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext e; unfold whnfCoreLoopI; rw [ih, whnfCoreStepI_congr hfe htb]

/-- `whnfCoreBodyI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfCoreBodyI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    whnfCoreBodyI mode r fe₁ = whnfCoreBodyI mode r fe₂ := by
  funext cheap depth e; unfold whnfCoreBodyI; rw [whnfCoreLoopI_congr hfe htb]

/-- `inferSpineI` only threads `fe`. -/
theorem inferSpineI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferSpineI r fe₁ = inferSpineI r fe₂ := by
  funext depth ty acc args
  induction args generalizing ty acc with
  | nil => rfl
  | cons a as ih => simp only [inferSpineI, ih]

/-- `inferSpineIOI` only threads `fe`. -/
theorem inferSpineIOI_congr (_hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    inferSpineIOI r fe₁ = inferSpineIOI r fe₂ := by
  funext depth ty acc args
  induction args generalizing ty acc with
  | nil => rfl
  | cons a as ih => simp only [inferSpineIOI, ih]

/-- `whnfStepI` reads `fe` only through `find?`. -/
theorem whnfStepI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfStepI r fe₁ = whnfStepI r fe₂ := by
  funext depth k e; unfold whnfStepI
  simp only [reduceNatI_congr hfe, unfoldDefinitionI_congr hfe]

/-- `whnfLoopI` reads `fe` only through `find?`. -/
theorem whnfLoopI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfLoopI r fe₁ = whnfLoopI r fe₂ := by
  funext depth n
  induction n with
  | zero => rfl
  | succ n ih => funext e; unfold whnfLoopI; rw [ih, whnfStepI_congr hfe]

/-- `whnfBodyI` reads `fe` only through `find?`. -/
theorem whnfBodyI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    whnfBodyI r fe₁ = whnfBodyI r fe₂ := by
  funext depth e; unfold whnfBodyI; rw [whnfLoopI_congr hfe]

/-- `checkProjGuardI` reads `fe` only through `find?`. -/
theorem checkProjGuardI_congr (hfe : fe₁.find? = fe₂.find?)
    (inf wh : Nat → Expr → CheckCM Expr) :
    checkProjGuardI inf wh fe₁ = checkProjGuardI inf wh fe₂ := by
  funext entry us; unfold checkProjGuardI checkProjRowsI
  simp only [hfe, constTyAtM_congr hfe]

/-- `inferBodyI` reads `fe` only through `find?` and `findTable?`. -/
theorem inferBodyI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    inferBodyI r fe₁ = inferBodyI r fe₂ := by
  funext depth e; unfold inferBodyI
  simp only [hfe, natLitStoredF_congr hfe, strLitStoredF_congr hfe,
    constTyAtM_congr hfe, inferSpineI_congr hfe, findProj?_congr hfe htb, htb,
    checkProjGuardI_congr hfe]

/-- `inferBodyIOI` reads `fe` only through `find?` and `findTable?`. -/
theorem inferBodyIOI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    inferBodyIOI r fe₁ = inferBodyIOI r fe₂ := by
  funext depth e; unfold inferBodyIOI
  simp only [inferSpineIOI_congr hfe, inferBodyI_congr hfe htb]

/-- `lazyDeltaStepI` reads `fe` only through `find?`. -/
theorem lazyDeltaStepI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    lazyDeltaStepI mode r fe₁ = lazyDeltaStepI mode r fe₂ := by
  funext depth a b; unfold lazyDeltaStepI
  simp only [unfoldableHeadC_congr hfe, unfoldDefinitionI_congr hfe,
    headHintC_congr hfe, defeqSpineI_congr hfe]

/-- `lazyDeltaReductionI` reads `fe` only through `find?`. -/
theorem lazyDeltaReductionI_congr (hfe : fe₁.find? = fe₂.find?) (r : CoreFnsI) :
    lazyDeltaReductionI mode eager r fe₁ = lazyDeltaReductionI mode eager r fe₂ := by
  funext depth n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext a b; unfold lazyDeltaReductionI
    simp only [ih, reduceNatI_congr hfe, lazyDeltaStepI_congr hfe]

/-- `lazyDeltaProjReductionI` reads `fe` only through `find?` and `findTable?`. -/
theorem lazyDeltaProjReductionI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    lazyDeltaProjReductionI mode r fe₁ = lazyDeltaProjReductionI mode r fe₂ := by
  funext depth sn i n
  induction n with
  | zero => rfl
  | succ n ih =>
    funext a b; unfold lazyDeltaProjReductionI
    simp only [ih, lazyDeltaStepI_congr hfe, reduceProjCoreI_congr hfe htb]

/-- `defeqProjPairI` reads `fe` only through `find?` and `findTable?`. -/
theorem defeqProjPairI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    defeqProjPairI mode r fe₁ = defeqProjPairI mode r fe₂ := by
  funext depth a b; unfold defeqProjPairI
  simp only [lazyDeltaProjReductionI_congr hfe htb]

/-- `defeqStuckI` reads `fe` only through `find?` and `findTable?`. -/
theorem defeqStuckI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    defeqStuckI mode r fe₁ = defeqStuckI mode r fe₂ := by
  funext depth a b; unfold defeqStuckI
  simp only [stuckIrrelI_congr hfe htb, strLitStoredF_congr hfe,
    defEqListI_congr hfe, etaCertI_congr hfe]

/-- `defeqBodyI` reads `fe` only through `find?` and `findTable?`. -/
theorem defeqBodyI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (r : CoreFnsI) :
    defeqBodyI mode eager r fe₁ = defeqBodyI mode eager r fe₂ := by
  funext depth a b; unfold defeqBodyI
  simp only [propIrrelI_congr hfe htb, lazyDeltaReductionI_congr hfe,
    defeqProjPairI_congr hfe htb, defeqStuckI_congr hfe htb]

/-! ## The knot, and the operation records built on it -/

/-- One level of the knot, at either flag. -/
theorem coreKnotI_succ (fe : FEnv) (F : Nat) :
    coreKnotI mode eager fe (F + 1) = knotLevelI mode eager fe
      (fun _ => coreKnotI mode eager fe F) (fun _ => coreKnotI mode true fe F) := by
  cases eager <;> rfl

/-- **The knot reads the index only through `find?` and `findTable?`.**  `ensureSortI`
needs no lemma of its own: it takes the tied record, not the index. -/
theorem coreKnotI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) :
    ∀ F, coreKnotI mode eager fe₁ F = coreKnotI mode eager fe₂ F := by
  intro F
  -- the eager slot ties the knot at `eager := true` (task #353): the
  -- induction is over both flags at once
  induction F generalizing eager with
  | zero => cases eager <;> rfl
  | succ F ih =>
    rw [coreKnotI_succ, coreKnotI_succ]; unfold knotLevelI
    simp only [ih, whnfCoreBodyI_congr hfe htb, whnfBodyI_congr hfe,
      inferBodyI_congr hfe htb, defeqBodyI_congr hfe htb, inferBodyIOI_congr hfe htb]

/-- `opSIxC` reads `fe` only through `find?` and `findTable?`. -/
theorem opSIxC_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) :
    opSIxC mode fe₁ = opSIxC mode fe₂ := by
  funext d i; unfold opSIxC; rw [coreKnotI_congr hfe htb]

end ConLeche.Cached
