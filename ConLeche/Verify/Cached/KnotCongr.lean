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
knot's bodies, bottom-up, landing on `knotI_congr`.

The consumer is the record's job (`ConLeche/Verify/Cached/ViewCongr.lean`): a job checks a record
at a view of the stream's index whose lookups are the fold's index's, so `knotI_congr` says they
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

The knot's functions are one mutual block, so their congruences are
taken level by level: at a knot level `lv`, given that the five entry
points agree there on the two indices (`SlotsEq`), every helper and body
of the block agrees at `lv`; the bodies at `lv` make the entry points
agree at `lv + 1` (`slotsEq`).  Each lemma equates the two partial
applications at everything up to and including the level, so
`simp only [f_congr hfe htb h]` rewrites a call site inside a larger
body.  A few of these functions only *thread* `fe`; their hypothesis is
still taken, because it is what pins the two indices when the lemma is
used as a rewrite rule.
-/

/-- `unfoldDefinitionI` reads `fe` only through `find?`. -/
theorem unfoldDefinitionI_congr (hfe : fe₁.find? = fe₂.find?) :
    unfoldDefinitionI fe₁ = unfoldDefinitionI fe₂ := by
  funext e; unfold unfoldDefinitionI; simp only [hfe, constValAtM_congr hfe]

/-- `litToCtorIfNatI` reads `fe` only through `find?`. -/
theorem litToCtorIfNatI_congr (hfe : fe₁.find? = fe₂.find?) :
    litToCtorIfNatI fe₁ = litToCtorIfNatI fe₂ := by
  funext e; unfold litToCtorIfNatI; simp only [natLitStoredF_congr hfe]

/-- `projCertAtF` reads `fe` only through `find?`. -/
theorem projCertAtF_congr (hfe : fe₁.find? = fe₂.find?) :
    projCertAtF fe₁ = projCertAtF fe₂ := by
  funext verified c args; unfold projCertAtF projCertF
  simp only [hfe]

/-- `etaCtorPartialC` reads `fe` only through `find?` and `findTable?`. -/
theorem etaCtorPartialC_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) :
    etaCtorPartialC fe₁ = etaCtorPartialC fe₂ := by
  funext e; unfold etaCtorPartialC; simp only [hfe, htb]

/-- `unitLikeShapeF` reads `fe` only through `find?` and `findTable?`. -/
theorem unitLikeShapeF_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) :
    unitLikeShapeF fe₁ = unitLikeShapeF fe₂ := by
  funext w; unfold unitLikeShapeF; simp only [hfe, htb]

/-- `iotaArityOk` reads `fe` only through `find?`. -/
theorem iotaArityOk_congr (hfe : fe₁.find? = fe₂.find?) :
    iotaArityOk fe₁ = iotaArityOk fe₂ := by
  funext e; unfold iotaArityOk; simp only [hfe]

/-- `iotaTargetF` reads `fe` only through `find?`. -/
theorem iotaTargetF_congr (hfe : fe₁.find? = fe₂.find?) :
    iotaTargetF fe₁ = iotaTargetF fe₂ := by
  funext h; unfold iotaTargetF; simp only [hfe]

/-- The five entry points of the knot agree at level `lv` on the two
indices, in both towers. -/
abbrev SlotsEq (mode : CheckMode) (fe₁ fe₂ : FEnv) (lv : Nat) : Prop :=
  (∀ eager, whnfCoreI mode fe₁ eager lv = whnfCoreI mode fe₂ eager lv) ∧
  (∀ eager, whnfI mode fe₁ eager lv = whnfI mode fe₂ eager lv) ∧
  (∀ eager, inferI mode fe₁ eager lv = inferI mode fe₂ eager lv) ∧
  (∀ eager, defeqI mode fe₁ eager lv = defeqI mode fe₂ eager lv) ∧
  (∀ eager, defeqEI mode fe₁ eager lv = defeqEI mode fe₂ eager lv)

section Level

variable {lv : Nat}

/-- `reduceNatI` reads `fe` only through `find?`. -/
theorem reduceNatI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    reduceNatI mode fe₁ eager lv = reduceNatI mode fe₂ eager lv := by
  funext depth e; rw [reduceNatI.eq_def, reduceNatI.eq_def]
  simp only [natLitStoredF_congr hfe, h]

/-- `iotaCertsFullIAux` only threads `fe`.  By induction on the
arguments; at each, first at the empty accumulator (where a `bvar`
telescope stops), then at any. -/
theorem iotaCertsFullIAux_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv)
    (depth : Nat) : ∀ (args : List Expr) (ty : Expr) (acc : List Expr),
    iotaCertsFullIAux mode fe₁ eager lv depth ty acc args =
      iotaCertsFullIAux mode fe₂ eager lv depth ty acc args := by
  intro args
  induction args with
  | nil => intro ty acc; rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
  | cons arg rest ih =>
    have h₀ : ∀ ty, iotaCertsFullIAux mode fe₁ eager lv depth ty [] (arg :: rest) =
        iotaCertsFullIAux mode fe₂ eager lv depth ty [] (arg :: rest) := by
      intro ty
      rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
      cases ty <;> simp only [h, ih]
    intro ty acc
    rw [iotaCertsFullIAux.eq_def, iotaCertsFullIAux.eq_def]
    cases ty <;> cases acc <;> simp only [h, ih, h₀]

/-- `iotaCertsFullI` only threads `fe`. -/
theorem iotaCertsFullI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    iotaCertsFullI mode fe₁ eager lv = iotaCertsFullI mode fe₂ eager lv := by
  funext depth ty args; rw [iotaCertsFullI.eq_def, iotaCertsFullI.eq_def]
  exact iotaCertsFullIAux_congr hfe h depth args ty []

/-- `defEqListI` only threads `fe`. -/
theorem defEqListI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    defEqListI mode fe₁ eager lv = defEqListI mode fe₂ eager lv := by
  funext depth as bs
  induction as generalizing bs with
  | nil => rw [defEqListI.eq_def, defEqListI.eq_def]; cases bs <;> rfl
  | cons a as ih =>
    rw [defEqListI.eq_def, defEqListI.eq_def]
    cases bs <;> simp only [h, ih]

/-- `iotaIndexOkI` only threads `fe`. -/
theorem iotaIndexOkI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    iotaIndexOkI mode fe₁ eager lv = iotaIndexOkI mode fe₂ eager lv := by
  funext depth mI rP cnP tyCtor margs idx; rw [iotaIndexOkI.eq_def, iotaIndexOkI.eq_def]
  simp only [defEqListI_congr hfe h]

/-- `defeqSpineI` only threads `fe`. -/
theorem defeqSpineI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    defeqSpineI mode fe₁ eager lv = defeqSpineI mode fe₂ eager lv := by
  funext depth a b; rw [defeqSpineI.eq_def, defeqSpineI.eq_def]
  simp only [defEqListI_congr hfe h]

/-- `proofIrrelI` only threads `fe`. -/
theorem proofIrrelI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    proofIrrelI mode fe₁ eager lv = proofIrrelI mode fe₂ eager lv := by
  funext depth a b; rw [proofIrrelI.eq_def, proofIrrelI.eq_def]
  simp only [h]

/-- `propIrrelI` reads `fe` only through `find?` and `findTable?`. -/
theorem propIrrelI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    propIrrelI mode fe₁ eager lv = propIrrelI mode fe₂ eager lv := by
  funext depth a b; rw [propIrrelI.eq_def, propIrrelI.eq_def]; simp only [hfe, htb, h]

/-- `structEtaCertWithI` reads `fe` only through `find?` and `findTable?`. -/
theorem structEtaCertWithI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    structEtaCertWithI mode fe₁ eager lv = structEtaCertWithI mode fe₂ eager lv := by
  funext depth a b wtb; rw [structEtaCertWithI.eq_def, structEtaCertWithI.eq_def]
  simp only [hfe, htb, defEqListI_congr hfe h]

/-- `structEtaFullI` reads `fe` only through `find?` and `findTable?`. -/
theorem structEtaFullI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    structEtaFullI mode fe₁ eager lv = structEtaFullI mode fe₂ eager lv := by
  funext depth a b; rw [structEtaFullI.eq_def, structEtaFullI.eq_def]
  simp only [etaCtorShapeC_congr hfe, structEtaCertWithI_congr hfe htb h, h]

/-- `structEtaExpandI` reads `fe` only through `find?` and `findTable?`. -/
theorem structEtaExpandI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    structEtaExpandI mode fe₁ eager lv = structEtaExpandI mode fe₂ eager lv := by
  funext k
  induction k with
  | zero =>
    funext depth a b t; rw [structEtaExpandI.eq_def, structEtaExpandI.eq_def]
    simp only [structEtaFullI_congr hfe htb h]
  | succ k ih =>
    funext depth a b t; rw [structEtaExpandI.eq_def, structEtaExpandI.eq_def]
    cases t <;> simp only [ih]

/-- `structEtaCertI` reads `fe` only through `find?` and `findTable?`. -/
theorem structEtaCertI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    structEtaCertI mode fe₁ eager lv = structEtaCertI mode fe₂ eager lv := by
  funext depth a b; rw [structEtaCertI.eq_def, structEtaCertI.eq_def]
  simp only [etaCtorShapeC_congr hfe, etaCtorPartialC_congr hfe htb,
    structEtaFullI_congr hfe htb h, structEtaExpandI_congr hfe htb h, h]

/-- `isPropTypeI` only threads `fe`. -/
theorem isPropTypeI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    isPropTypeI mode fe₁ eager lv = isPropTypeI mode fe₂ eager lv := by
  funext depth t; rw [isPropTypeI.eq_def, isPropTypeI.eq_def]; simp only [h]

/-- `unitLikeLoopI` reads `fe` only through `find?` and `findTable?`: by
induction on the loop's fuel, through the structure test and its field
loop at the fuel below. -/
theorem unitLikeLoopI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    unitLikeLoopI mode fe₁ eager lv = unitLikeLoopI mode fe₂ eager lv := by
  funext f
  induction f with
  | zero => funext depth t; rw [unitLikeLoopI.eq_def, unitLikeLoopI.eq_def]
  | succ f ih =>
    have hF : unitLikeFieldsI mode fe₁ eager lv f = unitLikeFieldsI mode fe₂ eager lv f := by
      funext n
      induction n with
      | zero => funext depth t; rw [unitLikeFieldsI.eq_def, unitLikeFieldsI.eq_def]
      | succ n ihn =>
        funext depth t; rw [unitLikeFieldsI.eq_def, unitLikeFieldsI.eq_def]
        cases t <;> simp only [isPropTypeI_congr hfe h, ih, ihn]
    have hS : unitLikeStructI mode fe₁ eager lv f = unitLikeStructI mode fe₂ eager lv f := by
      funext depth w; rw [unitLikeStructI.eq_def, unitLikeStructI.eq_def]
      simp only [unitLikeShapeF_congr hfe htb, hF]
    funext depth t; rw [unitLikeLoopI.eq_def, unitLikeLoopI.eq_def]
    simp only [h, ih, hS]

/-- `structUnitCertI` reads `fe` only through `find?` and `findTable?`. -/
theorem structUnitCertI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    structUnitCertI mode fe₁ eager lv = structUnitCertI mode fe₂ eager lv := by
  funext depth a b; rw [structUnitCertI.eq_def, structUnitCertI.eq_def]
  simp only [unitLikeLoopI_congr hfe htb h, h]

/-- `etaCertI` only threads `fe`. -/
theorem etaCertI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    etaCertI mode fe₁ eager lv = etaCertI mode fe₂ eager lv := by
  funext depth ty₁ body₁ b; rw [etaCertI.eq_def, etaCertI.eq_def]; simp only [h]

/-- `stuckIrrelI` reads `fe` only through `find?` and `findTable?`. -/
theorem stuckIrrelI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    stuckIrrelI mode fe₁ eager lv = stuckIrrelI mode fe₂ eager lv := by
  funext depth a b; rw [stuckIrrelI.eq_def, stuckIrrelI.eq_def]
  simp only [structEtaCertI_congr hfe htb h, structUnitCertI_congr hfe htb h,
    proofIrrelI_congr hfe h]

/-- `formerSortLoopI` only threads `fe`. -/
theorem formerSortLoopI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    formerSortLoopI mode fe₁ eager lv = formerSortLoopI mode fe₂ eager lv := by
  funext d n
  induction n generalizing d with
  | zero => funext e; rw [formerSortLoopI.eq_def, formerSortLoopI.eq_def]; simp only [h]
  | succ n ih => funext e; rw [formerSortLoopI.eq_def, formerSortLoopI.eq_def]; simp only [h, ih]

/-- `formerNeverZeroI` only threads `fe`. -/
theorem formerNeverZeroI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    formerNeverZeroI mode fe₁ eager lv = formerNeverZeroI mode fe₂ eager lv := by
  funext cvT caps us; rw [formerNeverZeroI.eq_def, formerNeverZeroI.eq_def]
  simp only [formerSortLoopI_congr hfe h]

/-- `iotaCase3I` only threads `fe` (the lookups come as an argument). -/
theorem iotaCase3I_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    iotaCase3I mode fe₁ eager lv = iotaCase3I mode fe₂ eager lv := by
  funext find? isK cvj us; rw [iotaCase3I.eq_def, iotaCase3I.eq_def]
  simp only [formerNeverZeroI_congr hfe h]

/-- `majorToCtorI` reads `fe` only through `find?` and `findTable?`. -/
theorem majorToCtorI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    majorToCtorI mode fe₁ eager lv = majorToCtorI mode fe₂ eager lv := by
  funext depth recName isK rules major; rw [majorToCtorI.eq_def, majorToCtorI.eq_def]
  simp only [isCtorAppC_congr hfe, hfe, htb, andRescueSlotsF_congr hfe htb,
    formerNeverZeroI_congr hfe h, proofIrrelI_congr hfe h, h]

/-- `litMajorToCtorI` reads `fe` only through `find?`. -/
theorem litMajorToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    litMajorToCtorI mode fe₁ eager lv = litMajorToCtorI mode fe₂ eager lv := by
  funext depth e; rw [litMajorToCtorI.eq_def, litMajorToCtorI.eq_def]
  simp only [strLitStoredF_congr hfe, litToCtorIfNatI_congr hfe, h]

/-- `projLitToCtorI` reads `fe` only through `find?`. -/
theorem projLitToCtorI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    projLitToCtorI mode fe₁ eager lv = projLitToCtorI mode fe₂ eager lv := by
  funext depth e; rw [projLitToCtorI.eq_def, projLitToCtorI.eq_def]
  simp only [strLitStoredF_congr hfe, h]

/-- `prepareMajorI` reads `fe` only through `find?` and `findTable?`. -/
theorem prepareMajorI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    prepareMajorI mode fe₁ eager lv = prepareMajorI mode fe₂ eager lv := by
  funext depth recName isK rules major; rw [prepareMajorI.eq_def, prepareMajorI.eq_def]
  simp only [majorToCtorI_congr hfe htb h, litMajorToCtorI_congr hfe h, isCtorAppC_congr hfe, h]

/-- `iotaRecI` reads `fe` only through `find?` and `findTable?`. -/
theorem iotaRecI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    iotaRecI mode fe₁ eager lv = iotaRecI mode fe₂ eager lv := by
  funext depth hd args k; rw [iotaRecI.eq_def, iotaRecI.eq_def]
  simp only [hfe, prepareMajorI_congr hfe htb h, defEqListI_congr hfe h,
    constTyAtM_congr hfe, iotaCertsFullI_congr hfe h, iotaCase3I_congr hfe h,
    iotaIndexOkI_congr hfe h, ruleRhsAtM_congr hfe]

/-- `reduceProjCoreI` reads `fe` only through `find?` and `findTable?`. -/
theorem reduceProjCoreI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    reduceProjCoreI mode fe₁ eager lv = reduceProjCoreI mode fe₂ eager lv := by
  funext depth sn i c; rw [reduceProjCoreI.eq_def, reduceProjCoreI.eq_def]
  simp only [projLitToCtorI_congr hfe h, findProj?_congr hfe htb, projCertAtF_congr hfe]

/-- The peel loop only threads `fe`: it reads none of it. -/
theorem betaPeelI_congr (_hfe : fe₁.find? = fe₂.find?) (depth : Nat) :
    betaPeelI mode fe₁ eager lv depth = betaPeelI mode fe₂ eager lv depth := by
  funext t acc args i
  obtain ⟨n, hn⟩ : ∃ n, n = args.size - i := ⟨_, rfl⟩
  induction n generalizing t acc i with
  | zero =>
    rw [betaPeelI.eq_def, betaPeelI.eq_def, dite_eq_right (by omega), dite_eq_right (by omega)]
  | succ n ih =>
    rw [betaPeelI.eq_def, betaPeelI.eq_def]
    by_cases hi : i < args.size
    · rw [dite_eq_left hi, dite_eq_left hi]
      cases t <;> simp only [ih _ _ (i + 1) (by omega)]
    · rw [dite_eq_right hi, dite_eq_right hi]

/-- `whnfAppI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfAppI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv)
    (depth : Nat) :
    whnfAppI mode fe₁ eager lv depth = whnfAppI mode fe₂ eager lv depth := by
  funext v args i
  obtain ⟨n, hn⟩ : ∃ n, n = args.size - i := ⟨_, rfl⟩
  induction n generalizing v i with
  | zero =>
    rw [whnfAppI.eq_def, whnfAppI.eq_def, dite_eq_right (by omega), dite_eq_right (by omega)]
  | succ n ih =>
    rw [whnfAppI.eq_def, whnfAppI.eq_def]
    by_cases hi : i < args.size
    · rw [dite_eq_left hi, dite_eq_left hi]
      cases v <;> simp only [betaPeelI_congr hfe, iotaArityOk_congr hfe,
        iotaRecI_congr hfe htb h, ih _ (i + 1) (by omega)]
    · rw [dite_eq_right hi, dite_eq_right hi]

/-- `whnfStuckI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfStuckI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    whnfStuckI mode fe₁ eager lv = whnfStuckI mode fe₂ eager lv := by
  funext depth hd e; rw [whnfStuckI.eq_def, whnfStuckI.eq_def]
  simp only [iotaTargetF_congr hfe, iotaRecI_congr hfe htb h]

/-- `whnfCoreStepI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfCoreStepI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    whnfCoreStepI mode fe₁ eager lv = whnfCoreStepI mode fe₂ eager lv := by
  funext cheap depth hd e; rw [whnfCoreStepI.eq_def, whnfCoreStepI.eq_def]
  simp only [whnfAppI_congr hfe htb h, whnfStuckI_congr hfe htb h,
    reduceProjCoreI_congr hfe htb h, h]

/-- `whnfCoreLoopI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfCoreLoopI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    whnfCoreLoopI mode fe₁ eager lv = whnfCoreLoopI mode fe₂ eager lv := by
  funext cheap depth n
  induction n with
  | zero => funext pend pendC e; rw [whnfCoreLoopI.eq_def, whnfCoreLoopI.eq_def]
  | succ n ih =>
    funext pend pendC e; rw [whnfCoreLoopI.eq_def, whnfCoreLoopI.eq_def]
    simp only [ih, whnfCoreStepI_congr hfe htb h]

/-- `whnfCoreBodyI` reads `fe` only through `find?` and `findTable?`. -/
theorem whnfCoreBodyI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    whnfCoreBodyI mode fe₁ eager lv = whnfCoreBodyI mode fe₂ eager lv := by
  funext cheap depth e; rw [whnfCoreBodyI.eq_def, whnfCoreBodyI.eq_def]
  simp only [whnfCoreLoopI_congr hfe htb h]

/-- `defeqArgI` only threads `fe`. -/
theorem defeqArgI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    defeqArgI mode fe₁ eager lv = defeqArgI mode fe₂ eager lv := by
  funext depth a ta ty; rw [defeqArgI.eq_def, defeqArgI.eq_def]; simp only [h]

/-- `inferSpineI` only threads `fe`. -/
theorem inferSpineI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    inferSpineI mode fe₁ eager lv = inferSpineI mode fe₂ eager lv := by
  funext io depth ty acc args
  induction args generalizing ty acc with
  | nil => rw [inferSpineI.eq_def, inferSpineI.eq_def]
  | cons a as ih =>
    rw [inferSpineI.eq_def, inferSpineI.eq_def]
    simp only [h, defeqArgI_congr hfe h, ih]

/-- `inferSpineIOI` only threads `fe`. -/
theorem inferSpineIOI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    inferSpineIOI mode fe₁ eager lv = inferSpineIOI mode fe₂ eager lv := by
  funext depth ty acc args
  induction args generalizing ty acc with
  | nil => rw [inferSpineIOI.eq_def, inferSpineIOI.eq_def]
  | cons a as ih =>
    rw [inferSpineIOI.eq_def, inferSpineIOI.eq_def]
    simp only [h, ih]

/-- `whnfLoopI` reads `fe` only through `find?`. -/
theorem whnfLoopI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    whnfLoopI mode fe₁ eager lv = whnfLoopI mode fe₂ eager lv := by
  funext depth n
  induction n with
  | zero => funext e; rw [whnfLoopI.eq_def, whnfLoopI.eq_def]
  | succ n ih =>
    funext e; rw [whnfLoopI.eq_def, whnfLoopI.eq_def]
    simp only [ih, h, reduceNatI_congr hfe h, unfoldDefinitionI_congr hfe]

/-- `whnfBodyI` reads `fe` only through `find?`. -/
theorem whnfBodyI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    whnfBodyI mode fe₁ eager lv = whnfBodyI mode fe₂ eager lv := by
  funext depth e; rw [whnfBodyI.eq_def, whnfBodyI.eq_def]; simp only [whnfLoopI_congr hfe h]

/-- `ensureSortI` only threads `fe`. -/
theorem ensureSortI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    ensureSortI mode fe₁ eager lv = ensureSortI mode fe₂ eager lv := by
  funext depth e; rw [ensureSortI.eq_def, ensureSortI.eq_def]; simp only [h]

/-- `checkProjGuardI` reads `fe` only through `find?`. -/
theorem checkProjGuardI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    checkProjGuardI mode fe₁ eager lv = checkProjGuardI mode fe₂ eager lv := by
  have hrows : checkGuardRowsI mode fe₁ eager lv = checkGuardRowsI mode fe₂ eager lv := by
    funext guardSort rows
    induction rows with
    | nil => rw [checkGuardRowsI.eq_def, checkGuardRowsI.eq_def]
    | cons row rest ih =>
      rw [checkGuardRowsI.eq_def, checkGuardRowsI.eq_def]; simp only [h, ih]
  have hsort : projGuardSortI mode fe₁ eager lv = projGuardSortI mode fe₂ eager lv := by
    funext cvT caps us; rw [projGuardSortI.eq_def, projGuardSortI.eq_def]
    simp only [formerSortLoopI_congr hfe h]
  have hprows : checkProjRowsI mode fe₁ eager lv = checkProjRowsI mode fe₂ eager lv := by
    funext entry us guardSort; rw [checkProjRowsI.eq_def, checkProjRowsI.eq_def]
    simp only [hfe, constTyAtM_congr hfe, hrows]
  funext entry us; rw [checkProjGuardI.eq_def, checkProjGuardI.eq_def]
  simp only [hfe, hprows, hsort]

/-- `inferLamsI` only threads `fe`. -/
theorem inferLamsI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    inferLamsI mode fe₁ eager lv = inferLamsI mode fe₂ eager lv := by
  have hleaf : inferLamsLeafI mode fe₁ eager lv = inferLamsLeafI mode fe₂ eager lv := by
    funext io d t k fvs stk; rw [inferLamsLeafI.eq_def, inferLamsLeafI.eq_def]; simp only [h]
  funext io d f
  induction f with
  | zero => funext t k fvs stk; rw [inferLamsI.eq_def, inferLamsI.eq_def]; simp only [hleaf]
  | succ f ih =>
    funext t k fvs stk; rw [inferLamsI.eq_def, inferLamsI.eq_def]
    simp only [h, hleaf, ih]

/-- `inferPisI` only threads `fe`. -/
theorem inferPisI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    inferPisI mode fe₁ eager lv = inferPisI mode fe₂ eager lv := by
  have hleaf : inferPisLeafI mode fe₁ eager lv = inferPisLeafI mode fe₂ eager lv := by
    funext io d t k fvs stk; rw [inferPisLeafI.eq_def, inferPisLeafI.eq_def]; simp only [h]
  funext io d f
  induction f with
  | zero => funext t k fvs stk; rw [inferPisI.eq_def, inferPisI.eq_def]; simp only [hleaf]
  | succ f ih =>
    funext t k fvs stk; rw [inferPisI.eq_def, inferPisI.eq_def]
    simp only [h, hleaf, ih]

/-- `inferBodyI` reads `fe` only through `find?` and `findTable?`. -/
theorem inferBodyI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    inferBodyI mode fe₁ eager lv = inferBodyI mode fe₂ eager lv := by
  funext io depth e; rw [inferBodyI.eq_def, inferBodyI.eq_def]
  simp only [hfe, natLitStoredF_congr hfe, strLitStoredF_congr hfe,
    constTyAtM_congr hfe, inferSpineI_congr hfe h, findProj?_congr hfe htb, htb,
    checkProjGuardI_congr hfe h, inferPisI_congr hfe h, inferLamsI_congr hfe h,
    ensureSortI_congr hfe h, h]

/-- `inferBodyIOI` reads `fe` only through `find?` and `findTable?`. -/
theorem inferBodyIOI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    inferBodyIOI mode fe₁ eager lv = inferBodyIOI mode fe₂ eager lv := by
  funext depth e; rw [inferBodyIOI.eq_def, inferBodyIOI.eq_def]
  simp only [inferSpineIOI_congr hfe h, inferBodyI_congr hfe htb h, ensureSortI_congr hfe h, h]

/-- `quickDefEqI` only threads `fe`. -/
theorem quickDefEqI_congr (_hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    quickDefEqI mode fe₁ eager lv = quickDefEqI mode fe₂ eager lv := by
  have hin : defeqBindersInnerI mode fe₁ eager lv = defeqBindersInnerI mode fe₂ eager lv := by
    funext lam depth b₁ b₂; rw [defeqBindersInnerI.eq_def, defeqBindersInnerI.eq_def]
    simp only [h]
  have hdom : defeqDomainI mode fe₁ eager lv = defeqDomainI mode fe₂ eager lv := by
    funext depth fvs ty₁ ty₂ dom₂; rw [defeqDomainI.eq_def, defeqDomainI.eq_def]; simp only [h]
  have hb : defeqBindersI mode fe₁ eager lv = defeqBindersI mode fe₂ eager lv := by
    funext lam f
    induction f with
    | zero =>
      funext depth fvs ty₁ body₁ ty₂ body₂; rw [defeqBindersI.eq_def, defeqBindersI.eq_def]
      simp only [hin, hdom]
    | succ f ih =>
      funext depth fvs ty₁ body₁ ty₂ body₂; rw [defeqBindersI.eq_def, defeqBindersI.eq_def]
      rcases hp : Expr.binderPair? lam body₁ body₂ with _ | ⟨_, _, _, _⟩ <;>
        simp only [hp, hin, hdom, ih]
  funext depth a b; rw [quickDefEqI.eq_def, quickDefEqI.eq_def]; simp only [hb]

/-- `lazyDeltaStepI` reads `fe` only through `find?`. -/
theorem lazyDeltaStepI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    lazyDeltaStepI mode fe₁ eager lv = lazyDeltaStepI mode fe₂ eager lv := by
  have htry : tryUnfoldProjAppI mode fe₁ eager lv = tryUnfoldProjAppI mode fe₂ eager lv := by
    funext depth e; rw [tryUnfoldProjAppI.eq_def, tryUnfoldProjAppI.eq_def]; simp only [h]
  have hq : deltaQuickI mode fe₁ eager lv = deltaQuickI mode fe₂ eager lv := by
    funext depth a b; rw [deltaQuickI.eq_def, deltaQuickI.eq_def]
    simp only [quickDefEqI_congr hfe h]
  funext depth a b; rw [lazyDeltaStepI.eq_def, lazyDeltaStepI.eq_def]
  simp only [unfoldableHeadC_congr hfe, unfoldDefinitionI_congr hfe,
    headHintC_congr hfe, defeqSpineI_congr hfe h, htry, hq, h]

/-- `lazyDeltaReductionI` reads `fe` only through `find?`. -/
theorem lazyDeltaReductionI_congr (hfe : fe₁.find? = fe₂.find?) (h : SlotsEq mode fe₁ fe₂ lv) :
    lazyDeltaReductionI mode fe₁ eager lv = lazyDeltaReductionI mode fe₂ eager lv := by
  have hoff : defeqOffsetI mode fe₁ eager lv = defeqOffsetI mode fe₂ eager lv := by
    funext depth a b; rw [defeqOffsetI.eq_def, defeqOffsetI.eq_def]; simp only [h]
  funext depth n
  induction n with
  | zero => funext a b; rw [lazyDeltaReductionI.eq_def, lazyDeltaReductionI.eq_def]
  | succ n ih =>
    funext a b; rw [lazyDeltaReductionI.eq_def, lazyDeltaReductionI.eq_def]
    simp only [ih, hoff, reduceNatI_congr hfe h, lazyDeltaStepI_congr hfe h, h]

/-- `lazyDeltaProjReductionI` reads `fe` only through `find?` and `findTable?`. -/
theorem lazyDeltaProjReductionI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    lazyDeltaProjReductionI mode fe₁ eager lv = lazyDeltaProjReductionI mode fe₂ eager lv := by
  funext depth sn i n
  induction n with
  | zero => funext a b; rw [lazyDeltaProjReductionI.eq_def, lazyDeltaProjReductionI.eq_def]
  | succ n ih =>
    funext a b; rw [lazyDeltaProjReductionI.eq_def, lazyDeltaProjReductionI.eq_def]
    simp only [ih, lazyDeltaStepI_congr hfe h, reduceProjCoreI_congr hfe htb h, h]

/-- `defeqStuckI` reads `fe` only through `find?` and `findTable?`. -/
theorem defeqStuckI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    defeqStuckI mode fe₁ eager lv = defeqStuckI mode fe₂ eager lv := by
  funext depth a b; rw [defeqStuckI.eq_def, defeqStuckI.eq_def]
  simp only [stuckIrrelI_congr hfe htb h, strLitStoredF_congr hfe,
    defEqListI_congr hfe h, etaCertI_congr hfe h, h]

/-- `defeqBodyI` reads `fe` only through `find?` and `findTable?`. -/
theorem defeqBodyI_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) (h : SlotsEq mode fe₁ fe₂ lv) :
    defeqBodyI mode fe₁ eager lv = defeqBodyI mode fe₂ eager lv := by
  have hbt : boolTrueShortcutI mode fe₁ eager lv = boolTrueShortcutI mode fe₂ eager lv := by
    funext depth a; rw [boolTrueShortcutI.eq_def, boolTrueShortcutI.eq_def]; simp only [h]
  have hpp : defeqProjPairI mode fe₁ eager lv = defeqProjPairI mode fe₂ eager lv := by
    funext depth a b; rw [defeqProjPairI.eq_def, defeqProjPairI.eq_def]
    simp only [lazyDeltaProjReductionI_congr hfe htb h]
  funext depth a b; rw [defeqBodyI.eq_def, defeqBodyI.eq_def]
  simp only [hbt, quickDefEqI_congr hfe h, propIrrelI_congr hfe htb h,
    lazyDeltaReductionI_congr hfe h, hpp, defeqStuckI_congr hfe htb h, h]

end Level

/-! ## The knot, and the operation records built on it -/

/-- The entry points agree at every level, by induction on it (both
towers at once: the eager entry point runs the eager tower's bodies). -/
theorem slotsEq (hfe : fe₁.find? = fe₂.find?) (htb : fe₁.findTable? = fe₂.findTable?) :
    ∀ lv, SlotsEq mode fe₁ fe₂ lv := by
  intro lv
  induction lv with
  | zero =>
    refine ⟨fun eager => ?_, fun eager => ?_, fun eager => ?_, fun eager => ?_, fun eager => ?_⟩
    · funext c d e; rw [whnfCoreI.eq_def, whnfCoreI.eq_def]
    · funext d e; rw [whnfI.eq_def, whnfI.eq_def]
    · funext io d e; rw [inferI.eq_def, inferI.eq_def]
    · funext d a b; rw [defeqI.eq_def, defeqI.eq_def]
    · funext d a b; rw [defeqEI.eq_def, defeqEI.eq_def]
  | succ lv ih =>
    refine ⟨fun eager => ?_, fun eager => ?_, fun eager => ?_, fun eager => ?_, fun eager => ?_⟩
    · funext c d e; rw [whnfCoreI.eq_def, whnfCoreI.eq_def]
      simp only [whnfCoreBodyI_congr hfe htb ih]
    · funext d e; rw [whnfI.eq_def, whnfI.eq_def]; simp only [whnfBodyI_congr hfe ih]
    · funext io d e; rw [inferI.eq_def, inferI.eq_def]
      simp only [inferBodyI_congr hfe htb ih, inferBodyIOI_congr hfe htb ih]
    · funext d a b; rw [defeqI.eq_def, defeqI.eq_def]; simp only [defeqBodyI_congr hfe htb ih]
    · funext d a b; rw [defeqEI.eq_def, defeqEI.eq_def]; simp only [defeqBodyI_congr hfe htb ih]

/-- **The knot reads the index only through `find?` and `findTable?`**:
its entry points, and `ensureSortI` on them, at every tower and level. -/
theorem knotI_congr (hfe : fe₁.find? = fe₂.find?) (htb : fe₁.findTable? = fe₂.findTable?) :
    whnfCoreI mode fe₁ = whnfCoreI mode fe₂ ∧ whnfI mode fe₁ = whnfI mode fe₂ ∧
      inferI mode fe₁ = inferI mode fe₂ ∧ defeqI mode fe₁ = defeqI mode fe₂ ∧
      defeqEI mode fe₁ = defeqEI mode fe₂ ∧ ensureSortI mode fe₁ = ensureSortI mode fe₂ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> funext eager lv
  · exact (slotsEq hfe htb lv).1 eager
  · exact (slotsEq hfe htb lv).2.1 eager
  · exact (slotsEq hfe htb lv).2.2.1 eager
  · exact (slotsEq hfe htb lv).2.2.2.1 eager
  · exact (slotsEq hfe htb lv).2.2.2.2 eager
  · exact ensureSortI_congr hfe (slotsEq hfe htb lv)

/-- `opSIxC` reads `fe` only through `find?` and `findTable?`. -/
theorem opSIxC_congr (hfe : fe₁.find? = fe₂.find?)
    (htb : fe₁.findTable? = fe₂.findTable?) :
    opSIxC mode fe₁ = opSIxC mode fe₂ := by
  funext d i; unfold opSIxC; simp only [knotI_congr hfe htb]

end ConLeche.Cached
