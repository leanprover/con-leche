import Setlec.Model.TypeChecker
import Setlec.Model.IotaWalk
import Setlec.Model.RuleFold

/-!
# Fold facts for a modeled recursor

`modeled_rule_fold` derives one recursor rule's `RecRulesOk` fold
obligation from the checked `R._model.iota_j` theorem, via the
defeq-based install checks: the fold's value spines are relocated onto
the theorem's own opening variables (`interp_instSeq_fvarFrames` — the
interpretations of instantiated telescope domains are determined by
the argument *values*), the theorem's telescope is walked with
memberships transferred along the kernel's per-binder `isDefEqCore`
facts (`pi_walk`), the theorem's inhabitant is eliminated into the
interpreted equation, the `Eq` collapse turns it into the value
equality between the recursor's spine fold and the interpreted
right-hand side of the checked statement, and the latter is the rule's
own interpretation applied along the spine (the statement's right side
is definitionally the *applied* rule, so no β-fold is needed — the
rule's λ-tower is walked only for the reduct's typing slots,
`lam_walk`).
-/

set_option linter.unusedSimpArgs false

namespace Setlec

variable {V : Type u} [SetTheory V] {cval : ConstVal V} {env : Env}
  {φ : Name → Nat}

open SetTheory Expr

/-- A fit's argument spine interprets pointwise to its value spine. -/
theorem TeleFitI.toInterpSpine {V : Type u} [SetTheory V]
    {cval : ConstVal V} {env : Env} {φ : Name → Nat} {d : Nat}
    {ρ : Nat → V} :
    ∀ {ty : Expr} {args : List Expr} {vs : List V} {rest : Expr},
      TeleFitI V cval env φ d ρ ty args vs rest →
      InterpSpine cval env φ d ρ args vs := by
  intro ty args vs rest h
  induction h with
  | nil => trivial
  | cons hity hiarg hx hfb hwa hba hAa _ ih => exact ⟨hiarg, ih⟩

set_option maxHeartbeats 3200000 in
theorem modeled_rule_fold
    {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat) {φ' : Name → Nat}
    {f : Name → Name}
    (hro : RenameOk m₀.val env₀ f)
    (hcvp : ConstValParams m₀.val env₀)
    -- the recursor and its model
    {R : Name} {lps : List Name} {tyA : Expr}
    {mI rP : Nat}
    {cim : ConstantInfo}
    (hfRm : env₀.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    -- the constructor and its model
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    (hfj : env₀.find? ctor = some (.ctorInfo cvj cnP cnF))
    {cimC : ConstantInfo}
    (hfCm : env₀.find? (f ctor) = some cimC)
    (hCmlps : cimC.toConstantVal.levelParams = cvj.levelParams)
    -- the pinned equality former
    (heqfind : env₀.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'')
    -- the iota theorem's semantic facts
    {cvt : ConstantVal} {thmName : Name}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ P,
      interpClosed V m₀.val env₀ ψ'' cvt.type = some P ∧
      m₀.val thmName ψ'' ∈ˢ P)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSb : cvt.type.looseBVarsBounded 0 = true)
    -- kernel kit (`PlainChecked` components)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    {cdoms : List Expr} {cres : Expr} {rdoms : List Expr} {rrest : Expr}
    {rhsA : Expr}
    {rbinders : List (Name × Expr × BinderMeta)} {rbody : Expr}
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvsP : List Expr} {crest2 : Expr}
    {ldoms : List Expr} {lrest : Expr}
    (htyStrip : (tyA.stripPis (mI)).isSome = true)
    -- the rule prefix fits under the major's position (from the
    -- canonical-rule computation at install)
    (hrPmI : rP ≤ mI)
    (hopen : openPisAtFvars (rP + cnF) cvt.type 0 =
      some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f R) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take (rP) =
      fvs.take (rP))
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop (rP)))
    (hcstrip : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop (rP))
      (cvj.type.renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hdeIdx : DefEqListOk F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop (rP)).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop (rP)).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hrinst : Expr.instPisAt (fvs.take (rP))
      (tyA.renameConsts f) = some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take (rP)).map Expr.fvarTypeD) rdoms)
    (hopenP : openPisAtFvars (rP) tyA 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hopenX : openPisAtFvars cnF crestP (rP) =
      some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hdeRhs : isDefEqCore env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    -- rule right-hand-side facts
    (_hstripR : rhsA.stripLams (rP + cnF) =
      some (rbinders, rbody))
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) rhsA)
    (hIrhs : ∀ ψ'' : Name → Nat, ∃ L,
      interpClosed V m₀.val env₀ ψ'' rhsA = some L)
    -- member type wf
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (_htyps : tyA.allLevelParamsDefined lps = true)
    (hAty : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) tyA)
    (hIty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ'' tyA = some T)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hCps : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (hACty : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvj.type)
    (hICty : ∀ ψ'' : Name → Nat, ∃ T,
      interpClosed V m₀.val env₀ ψ'' cvj.type = some T)
    -- fold clause inputs
    {us usj : List Level} {args margs : List V} {tv : V}
    (hplainLe : cnP ≤ rP)
    (hlena : args.length = mI)
    (hlenm : margs.length = cnP + cnF)
    (htv : tv = SpineFold V (m₀.val ctor
      (Level.substFn φ' cvj.levelParams usj)) margs)
    (hparameq : margs.take cnP = (args ++ [tv]).take cnP)
    (hleveq : ∀ p ∈ cvj.levelParams,
      Level.substFn φ' cvj.levelParams usj p = Level.substFn φ' lps us p)
    {d : Nat} {ρ : Nat → V} {d₁ : Nat} {ρ₁ : Nat → V} {rest₁ : Expr}
    {d₂ : Nat} {ρ₂ : Nat → V} {rest₂ : Expr}
    (hfit1 : TeleFit V m₀.val env₀ φ' d ρ
      (tyA.instantiateLevelParams lps us) (args ++ [tv]) d₁ ρ₁ rest₁)
    (hfit2 : TeleFit V m₀.val env₀ φ' d₁ ρ₁
      (cvj.type.instantiateLevelParams cvj.levelParams usj) margs
      d₂ ρ₂ rest₂)
    (hidx : (rest₂.getAppArgs.drop cnP).mapM
      (interpExpr V m₀.val env₀ φ' d₂ ρ₂) =
      some (args.drop (rP))) :
    ∃ Rv, interpClosed V m₀.val env₀ (Level.substFn φ' lps us) rhsA =
        some Rv ∧
      SpineFold V (m₀.val R (Level.substFn φ' lps us)) (args ++ [tv]) =
        SpineFold V Rv (args.take (rP) ++ margs.drop cnP) ∧
      ChainSlots V Rv (args.take (rP) ++ margs.drop cnP) := by
  -- ===== S0: the master frame =====
  obtain ⟨hfvsInst, hfvsLen, hfvsShape⟩ :=
    openPisAtFvars_spec (rP + cnF) 0 hopen
  have hpreLen : (args.take (rP)).length = rP := by
    rw [List.length_take, hlena]; omega
  have hwsLen : (args.take (rP) ++ margs.drop cnP).length =
      rP + cnF := by
    simp only [List.length_append, List.length_drop, hpreLen, hlenm]
    omega
  have hρWval : ∀ (k : Nat) (v : V),
      (args.take (rP) ++ margs.drop cnP)[k]? = some v →
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) (0 + k) = v := by
    intro k v hv
    show (args.take (rP) ++ margs.drop cnP).getD (0 + k)
      SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD, Nat.zero_add, hv]
    rfl
  have hspW : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) fvs
      (args.take (rP) ++ margs.drop cnP) :=
    FvarSpine_of_open hopen hwsLen (by omega) hρWval
  obtain ⟨hfvsWf, htbodyWf⟩ :=
    openPisAtFvars_wf (rP + cnF) 0 hopen
      (WScoped.of_not_hasFvar hSw) hSb
      (Expr.LeavesBounded.of_not_hasFvar hSw)
  have hfvsW : ∀ a ∈ fvs, WScoped (rP + cnF) a := by
    intro a ha
    have := (hfvsWf a ha).1
    simpa using this
  have hfvsShapes : ∀ a ∈ fvs, ∃ i n t, a = .fvar i n t := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨nm', ha'⟩ := hfvsShape k a hk
    exact ⟨0 + k, nm', _, ha'⟩
  -- ===== S1a: relocate the recursor fit =====
  have hTw : ∀ Dx : Nat, WScoped Dx (tyA.instantiateLevelParams lps us) :=
    fun Dx => WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact htyw)
  obtain ⟨hdd₁, hagr₁, argsR0, hfitL1, hfvR0⟩ :=
    TeleFit.toTeleFitI hfit1 (hTw d)
  have hlenR0 : argsR0.length = mI + 1 := by
    have h1 := TeleFitI.vs_length hfitL1
    simp only [List.length_append, List.length_cons, List.length_nil,
      hlena] at h1
    omega
  -- prefix restriction
  have hfitL1' : TeleFitI V m₀.val env₀ φ' d₁ ρ₁
      (tyA.instantiateLevelParams lps us)
      (argsR0.take (rP) ++ argsR0.drop (rP))
      (args ++ [tv]) rest₁ := by
    rw [List.take_append_drop]
    exact hfitL1
  obtain ⟨midR, hpreR0⟩ := TeleFitI.take_prefix hfitL1'
  have hpreR0len : (argsR0.take (rP)).length = rP := by
    rw [List.length_take, hlenR0]; omega
  have hpreRvals : (args ++ [tv]).take
      ((argsR0.take (rP)).length) = args.take (rP) := by
    rw [hpreR0len, List.take_append_of_le_length (by omega)]
  rw [hpreRvals] at hpreR0
  -- the raw prefix telescope strips
  obtain ⟨⟨bsTy, restTy⟩, htyStripSome⟩ :=
    Option.isSome_iff_exists.mp htyStrip
  obtain ⟨restTyPre, htyPreStrip⟩ :=
    Expr.stripPis_prefix rP (mI - rP)
      (by rw [show rP + (mI - rP) = mI from by omega]; exact htyStripSome)
  -- sanitize and uninstantiate the levels
  obtain ⟨midR2, hpreRS⟩ := TeleFitI.sanitize hpreR0
    (by
      rw [hpreR0len]
      exact Expr.stripPis_instantiateLevelParams_isSome _ _ _
        (by rw [htyPreStrip]; rfl))
    (fun a ha => hfvR0 a (List.mem_of_mem_take ha))
  have hshR : ∀ a ∈ (argsR0.take (rP)).map sanitizeArg,
      ∃ i n, a = Expr.fvar i n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, n, t, rfl⟩ := hfvR0 a₀ (List.mem_of_mem_take ha₀)
    exact ⟨i, n, rfl⟩
  obtain ⟨midR3, hfitRawR⟩ := TeleFitI.instLev_down hcvp hpreRS hshR
    (WScoped.of_not_hasFvar htyw (d := d₁)).fvarsBelow
  have hshR' : ∀ a ∈ (argsR0.take (rP)).map sanitizeArg,
      ∃ i n t, a = Expr.fvar i n t := by
    intro a ha
    obtain ⟨i, n, rfl⟩ := hshR a ha
    exact ⟨i, n, _, rfl⟩
  have hspR : FvarSpine d₁ ρ₁
      ((argsR0.take (rP)).map sanitizeArg)
      (args.take (rP)) :=
    FvarSpine_of_fit hfitRawR hshR'
  -- the public prefix walk of the recursor's type
  obtain ⟨⟨dsPubT, restPubT⟩, hpubT⟩ := Option.isSome_iff_exists.mp
    (instPisAt_isSome_of_stripPis (fvs.take (rP))
      (by
        rw [List.length_take, hfvsLen,
          Nat.min_eq_left (by omega), htyPreStrip]
        rfl))
  have hwsTake : (args.take (rP) ++ margs.drop cnP).take
      (rP) = args.take (rP) := by
    rw [List.take_append_of_le_length (by rw [hpreLen]; exact Nat.le_refl _),
      List.take_take, Nat.min_self]

  have hspWpre : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvs.take (rP)) (args.take (rP)) := by
    have h0 := FvarSpine.take (rP) hspW
    rwa [hwsTake] at h0
  -- pointwise packages for the public prefix domains, at the master
  -- frame
  have hmemPubT := fit_mem_transfer (φ := Level.substFn φ' lps us)
    htyw htyb htyPreStrip hpubT
    (by rw [List.length_take, hfvsLen]; omega)
    hspWpre hspR hfitRawR
  -- packages for the renamed prefix domains (`rdoms`)
  have htyPreRen : (tyA.renameConsts f).stripPis (rP) =
      some ((bsTy.take (rP)).map
        (fun b => (b.1, b.2.1.renameConsts f, b.2.2)),
        restTyPre.renameConsts f) :=
    stripPis_renameConsts (rP) htyPreStrip
  have hfvsPreLen : (fvs.take (rP)).length = rP := by
    rw [List.length_take, hfvsLen]; omega
  obtain ⟨-, hrdomsPt⟩ := instPisAt_stripPis _ hrinst
    (by rw [hfvsPreLen]; exact htyPreRen)
  obtain ⟨-, hpubTPt⟩ := instPisAt_stripPis _ hpubT
    (by rw [hfvsPreLen]; exact htyPreStrip)
  have hfvsPreShapes : ∀ a ∈ fvs.take (rP),
      ∃ i n t, a = .fvar i n t :=
    fun a ha => hfvsShapes a (List.mem_of_mem_take ha)
  have hbsTyLen : bsTy.length = mI :=
    Expr.stripPis_length _ htyStripSome
  have hmemR : ∀ (k : Nat) (a : Expr) (v : V), rdoms[k]? = some a →
      (args.take (rP))[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a = some B ∧
        v ∈ˢ B := by
    intro k a v ha hv
    have hk : k < rP := by
      have hl := instPisAt_length _ hrinst
      rcases Nat.lt_or_ge k (rP) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by rw [hl, hfvsPreLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨b, hb⟩ : ∃ b, (bsTy.take (rP))[k]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by rw [List.length_take]; omega)⟩
    have hbren : ((bsTy.take (rP)).map
        (fun b => (b.1, b.2.1.renameConsts f, b.2.2)))[k]? =
        some (b.1, b.2.1.renameConsts f, b.2.2) := by
      rw [List.getElem?_map, hb]
      rfl
    have ha' := hrdomsPt k _ hbren
    rw [ha] at ha'
    obtain rfl := Option.some.inj ha'
    obtain ⟨dp, hdp⟩ : ∃ dp, dsPubT[k]? = some dp := by
      have hl := instPisAt_length _ hpubT
      exact ⟨_, List.getElem?_eq_getElem (by rw [hl, hfvsPreLen]; omega)⟩
    obtain ⟨B, hBi, hvB⟩ := hmemPubT k dp v hdp hv
    have hdp' := hpubTPt k b hb
    rw [hdp] at hdp'
    obtain rfl := Option.some.inj hdp'
    refine ⟨B, ?_, hvB⟩
    show interpExpr V m₀.val env₀ (Level.substFn φ' lps us) _ _
      (instSeq ((fvs.take (rP)).take k) (k - 1)
        ((b.1, b.2.1.renameConsts f, b.2.2) :
          Name × Expr × BinderMeta).2.1) = some B
    rw [show ((b.1, b.2.1.renameConsts f, b.2.2) :
      Name × Expr × BinderMeta).2.1 = b.2.1.renameConsts f from rfl]
    rw [interp_instSeq_ren hro (fun a ha =>
      hfvsPreShapes a (List.mem_of_mem_take ha))]
    exact hBi
  -- ===== S1b: relocate the constructor fit =====
  have hCwI : ∀ Dx : Nat, WScoped Dx
      (cvj.type.instantiateLevelParams cvj.levelParams usj) :=
    fun Dx => WScoped.of_not_hasFvar
      (by rw [hasFvar_instantiateLevelParams]; exact hCw)
  obtain ⟨hdd₂, hagr₂, argsC0, hfitL2, hfvC0⟩ :=
    TeleFit.toTeleFitI hfit2 (hCwI d₁)
  have hlenC0 : argsC0.length = cnP + cnF := by
    have h1 := TeleFitI.vs_length hfitL2
    rw [hlenm] at h1
    omega
  obtain ⟨midC2, hfitC2⟩ := TeleFitI.sanitize hfitL2
    (by
      rw [hlenC0]
      exact Expr.stripPis_instantiateLevelParams_isSome _ _ _ hcstrip)
    hfvC0
  have hshC : ∀ a ∈ argsC0.map sanitizeArg,
      ∃ i n, a = Expr.fvar i n (.sort .zero) := by
    intro a ha
    obtain ⟨a₀, ha₀, rfl⟩ := List.mem_map.mp ha
    obtain ⟨i, n, t, rfl⟩ := hfvC0 a₀ ha₀
    exact ⟨i, n, rfl⟩
  obtain ⟨midC3, hfitC3⟩ := TeleFitI.instLev_down hcvp hfitC2 hshC
    (WScoped.of_not_hasFvar hCw (d := d₂)).fvarsBelow
  obtain ⟨midC4, hfitC4⟩ := TeleFitI.params_ext hleveq hcvp hfitC3
    hCps hshC
  have hshC' : ∀ a ∈ argsC0.map sanitizeArg,
      ∃ i n t, a = Expr.fvar i n t := by
    intro a ha
    obtain ⟨i, n, rfl⟩ := hshC a ha
    exact ⟨i, n, _, rfl⟩
  have hspC : FvarSpine d₂ ρ₂ (argsC0.map sanitizeArg) margs :=
    FvarSpine_of_fit hfitC4 hshC'
  -- value identifications
  have hparam' : margs.take cnP = args.take cnP := by
    rw [hparameq, List.take_append_of_le_length (by omega)]
  have hmargsSplit : margs = args.take cnP ++ margs.drop cnP := by
    rw [← hparam']
    exact (List.take_append_drop cnP margs).symm
  -- the theorem-side constructor spine (`fvs`-based)
  have hfvsCLen : (fvs.take cnP ++ fvs.drop (rP)).length =
      cnP + cnF := by
    simp only [List.length_append, List.length_take, List.length_drop,
      hfvsLen]
    omega
  have hspWctor : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvs.take cnP ++ fvs.drop (rP)) margs := by
    have hA : FvarSpine (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty)
        (fvs.take cnP) (args.take cnP) := by
      have h0 := FvarSpine.take cnP hspWpre
      rw [List.take_take, Nat.min_eq_left hplainLe] at h0
      rwa [List.take_take, Nat.min_eq_left (by omega)] at h0
    have hB : FvarSpine (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty)
        (fvs.drop (rP)) (margs.drop cnP) := by
      have h0 := FvarSpine.drop (rP) hspW
      have h1 := List.drop_left (l₁ := args.take (rP))
        (l₂ := margs.drop cnP)
      rw [hpreLen] at h1
      rwa [h1] at h0
    have h2 := FvarSpine.append hA hB
    rwa [← hmargsSplit] at h2
  -- public constructor walk at the theorem's variables
  obtain ⟨⟨dsPubC, restPubC⟩, hpubC⟩ := Option.isSome_iff_exists.mp
    (instPisAt_isSome_of_stripPis (fvs.take cnP ++ fvs.drop (rP))
      (by rw [hfvsCLen]; exact hcstrip))
  obtain ⟨⟨bsC, cbody⟩, hCstripSome⟩ := Option.isSome_iff_exists.mp hcstrip
  have hmemPubC := fit_mem_transfer (φ := Level.substFn φ' lps us)
    hCw hCb hCstripSome hpubC hfvsCLen hspWctor hspC hfitC4
  -- packages for the renamed constructor domains (`cdoms`)
  have hCRen : (cvj.type.renameConsts f).stripPis (cnP + cnF) =
      some (bsC.map (fun b => (b.1, b.2.1.renameConsts f, b.2.2)),
        cbody.renameConsts f) :=
    stripPis_renameConsts (cnP + cnF) hCstripSome
  obtain ⟨hcresEq, hcdomsPt⟩ := instPisAt_stripPis _ hcinst
    (by rw [hfvsCLen]; exact hCRen)
  obtain ⟨hrestPubCEq, hpubCPt⟩ := instPisAt_stripPis _ hpubC
    (by rw [hfvsCLen]; exact hCstripSome)
  have hbsCLen : bsC.length = cnP + cnF :=
    Expr.stripPis_length _ hCstripSome
  have hfvsCShapes : ∀ a ∈ fvs.take cnP ++ fvs.drop (rP),
      ∃ i n t, a = .fvar i n t := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfvsShapes a (List.mem_of_mem_take ha)
    · exact hfvsShapes a (List.mem_of_mem_drop ha)
  have hmemC : ∀ (k : Nat) (a : Expr) (v : V), cdoms[k]? = some a →
      margs[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a = some B ∧
        v ∈ˢ B := by
    intro k a v ha hv
    have hk : k < cnP + cnF := by
      have hl := instPisAt_length _ hcinst
      rcases Nat.lt_or_ge k (cnP + cnF) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by rw [hl, hfvsCLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨b, hb⟩ : ∃ b, bsC[k]? = some b :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hbren : (bsC.map
        (fun b => (b.1, b.2.1.renameConsts f, b.2.2)))[k]? =
        some (b.1, b.2.1.renameConsts f, b.2.2) := by
      rw [List.getElem?_map, hb]
      rfl
    have ha' := hcdomsPt k _ hbren
    rw [ha] at ha'
    obtain rfl := Option.some.inj ha'
    obtain ⟨dp, hdp⟩ : ∃ dp, dsPubC[k]? = some dp := by
      have hl := instPisAt_length _ hpubC
      exact ⟨_, List.getElem?_eq_getElem (by rw [hl, hfvsCLen]; omega)⟩
    obtain ⟨B, hBi, hvB⟩ := hmemPubC k dp v hdp hv
    have hdp' := hpubCPt k b hb
    rw [hdp] at hdp'
    obtain rfl := Option.some.inj hdp'
    refine ⟨B, ?_, hvB⟩
    show interpExpr V m₀.val env₀ (Level.substFn φ' lps us) _ _
      (instSeq ((fvs.take cnP ++ fvs.drop (rP)).take k) (k - 1)
        ((b.1, b.2.1.renameConsts f, b.2.2) :
          Name × Expr × BinderMeta).2.1) = some B
    rw [show ((b.1, b.2.1.renameConsts f, b.2.2) :
      Name × Expr × BinderMeta).2.1 = b.2.1.renameConsts f from rfl]
    rw [interp_instSeq_ren hro (fun a ha =>
      hfvsCShapes a (List.mem_of_mem_take ha))]
    exact hBi
  -- ===== S2: the theorem walk =====
  -- split the theorem's opening at the prefix/field boundary
  have hfvsInst' : Expr.instPisAt
      (fvs.take (rP) ++ fvs.drop (rP)) cvt.type =
      some (fvs.map Expr.fvarTypeD, tbody) := by
    rw [List.take_append_drop]
    exact hfvsInst
  obtain ⟨dsS1, midS, dsS2, hopS1, hopS2, hdsSplit⟩ :=
    instPisAt_append _ _ hfvsInst'
  have hdsS1len : dsS1.length = rP := by
    rw [instPisAt_length _ hopS1, hfvsPreLen]
  obtain ⟨hdsS1eq, hdsS2eq⟩ : dsS1 = (fvs.take (rP)).map
      Expr.fvarTypeD ∧ dsS2 = (fvs.drop (rP)).map
      Expr.fvarTypeD := by
    have hmap : fvs.map Expr.fvarTypeD =
        (fvs.take (rP)).map Expr.fvarTypeD ++
        (fvs.drop (rP)).map Expr.fvarTypeD := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap] at hdsSplit
    exact List.append_inj hdsSplit.symm (by
      rw [hdsS1len, List.length_map, hfvsPreLen])
  subst hdsS1eq hdsS2eq
  -- the master frame's theorem-side invariants
  have hWS : WScoped (rP + cnF) cvt.type :=
    WScoped.of_not_hasFvar hSw
  have hLS : Expr.LeavesBounded cvt.type :=
    Expr.LeavesBounded.of_not_hasFvar hSw
  have hFS : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) cvt.type :=
    FvarsOk.of_not_hasFvar hSw
  have hAS : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) cvt.type :=
    AnnotOk.closed_invariant hSw _ _
      (hthm_annot (Level.substFn φ' lps us))
  obtain ⟨P, hPc, hPmem⟩ := hthm_mem (Level.substFn φ' lps us)
  have hPI : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) cvt.type = some P := by
    rw [interp_closed_invariant hSw _ _]
    exact hPc
  -- the renamed recursor type's invariants
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  have hAtyR : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) (tyA.renameConsts f) :=
    AnnotOk.closed_invariant htyRw _ _
      (AnnotOk.renameConsts hro tyA 0 (rho0 V)
        (hAty (Level.substFn φ' lps us)))
  obtain ⟨Tty, hTtyc⟩ := hIty (Level.substFn φ' lps us)
  have hItyR : ∃ TR, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) (tyA.renameConsts f) =
      some TR := by
    refine ⟨Tty, ?_⟩
    rw [interp_closed_invariant htyRw _ _]
    show interpClosed V m₀.val env₀ _ (tyA.renameConsts f) = some Tty
    unfold interpClosed
    rw [interp_renameConsts hro tyA 0 (rho0 V)]
    exact hTtyc
  -- stage 1: the prefix walk
  obtain ⟨hfitS1, hfitR1, hΘpre⟩ := pi_walk m₀ F hopS1 hrinst hdePre
    hspWpre (fun a ha => hfvsW a (List.mem_of_mem_take ha))
    hWS hSb hLS hFS hAS
    (WScoped.of_not_hasFvar htyRw) htyRb
    (Expr.LeavesBounded.of_not_hasFvar htyRw)
    (FvarsOk.of_not_hasFvar htyRw) hAtyR
    ⟨P, hPI⟩ hItyR hmemR
  -- the mid residual's facts and the partial elimination
  obtain ⟨Qmid, hQmidI, hQmidMem, hAmidS⟩ :=
    TeleFitI.elim hfitS1 hAS hPI hPmem
  obtain ⟨hWmidS, hbmidS, -, hleavesMidS⟩ :=
    TeleFitI.rest_wf hfitS1 hWS hSb hAS
  have hFmidS : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact hΘpre a ha l hla
  have hLmidS : Expr.LeavesBounded midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
  -- the constructor's parameter walk to its mid residual
  obtain ⟨cdomsA, midC, cdomsB, hopC1, hopC2, hcdomsSplit⟩ :=
    instPisAt_append _ _ hcinst
  have hcdomsAlen : cdomsA.length = cnP := by
    rw [instPisAt_length _ hopC1, List.length_take, hfvsLen]
    omega
  have hcdomsBeq : cdoms.drop cnP = cdomsB := by
    rw [hcdomsSplit, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  have hACtyR : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (cvj.type.renameConsts f) := by
    have hCRw : (cvj.type.renameConsts f).hasFvar = false := by
      rw [hasFvar_renameConsts]; exact hCw
    exact AnnotOk.closed_invariant hCRw _ _
      (AnnotOk.renameConsts hro cvj.type 0 (rho0 V)
        (hACty (Level.substFn φ' lps us)))
  have hCRw : (cvj.type.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]; exact hCw
  have hCRb : (cvj.type.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]; exact hCb
  have hICtyR : ∃ TR, interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (cvj.type.renameConsts f) = some TR := by
    obtain ⟨TC, hTCc⟩ := hICty (Level.substFn φ' lps us)
    refine ⟨TC, ?_⟩
    rw [interp_closed_invariant hCRw _ _]
    show interpClosed V m₀.val env₀ _ (cvj.type.renameConsts f) = some TC
    unfold interpClosed
    rw [interp_renameConsts hro cvj.type 0 (rho0 V)]
    exact hTCc
  have hspWctorPre : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvs.take cnP) (margs.take cnP) := by
    have h0 := FvarSpine.take cnP hspWctor
    rwa [List.take_append_of_le_length (by
      rw [List.length_take, hfvsLen]; omega), List.take_take,
      Nat.min_self] at h0
  obtain ⟨hfitC1, hImidC⟩ := peel_walk hopC1 hspWctorPre
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
    (WScoped.of_not_hasFvar hCRw) hACtyR hICtyR
    (fun k a v ha hv => by
      have hkA : k < cnP := by
        rcases Nat.lt_or_ge k cnP with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at ha
          exact nomatch ha
      refine hmemC k a v ?_ ?_
      · rw [hcdomsSplit, List.getElem?_append_left (by omega)]
        exact ha
      · have hv' : (margs.take cnP)[k]? = some v := hv
        rwa [List.getElem?_take_of_lt hkA] at hv')
  -- the mid constructor residual's facts
  obtain ⟨hWmidC, hbmidC, hAmidC, hleavesMidC⟩ :=
    TeleFitI.rest_wf hfitC1 (WScoped.of_not_hasFvar hCRw) hCRb hACtyR
  have hFmidC : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · refine hΘpre a ?_ l hla
      have heq : fvs.take cnP = (fvs.take (rP)).take cnP := by
        rw [List.take_take, Nat.min_eq_left hplainLe]
      rw [heq] at ha
      exact List.mem_of_mem_take ha
  have hLmidC : Expr.LeavesBounded midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
  -- stage 2: the field walk
  have hspWdrop : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvs.drop (rP)) (margs.drop cnP) := by
    have h0 := FvarSpine.drop (rP) hspW
    have h1 := List.drop_left (l₁ := args.take (rP))
      (l₂ := margs.drop cnP)
    rw [hpreLen] at h1
    rwa [h1] at h0
  obtain ⟨hfitS2, hfitR2, hΘx⟩ := pi_walk m₀ F hopS2
    (by rw [← hcdomsBeq] at hopC2; exact hopC2)
    hdeFld
    hspWdrop (fun a ha => hfvsW a (List.mem_of_mem_drop ha))
    hWmidS hbmidS hLmidS hFmidS hAmidS
    hWmidC hbmidC hLmidC hFmidC hAmidC
    ⟨Qmid, hQmidI⟩ hImidC
    (fun k a v ha hv => by
      refine hmemC (cnP + k) a v ?_ ?_
      · rw [List.getElem?_drop] at ha
        exact ha
      · have hv' : (margs.drop cnP)[k]? = some v := hv
        rwa [List.getElem?_drop] at hv')
  -- combine and finish the elimination
  obtain ⟨Q, hQI, hQmem0, hAtbody⟩ :=
    TeleFitI.elim hfitS2 hAmidS hQmidI hQmidMem
  have hQmem : SpineFold V (m₀.val thmName (Level.substFn φ' lps us))
      (args.take (rP) ++ margs.drop cnP) ∈ˢ Q := by
    rw [SpineFold_append]
    exact hQmem0
  -- ===== S3: the Eq collapse =====
  have htbodyEq : tbody = Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS] := by
    have h0 := Expr.mkAppN_getApp tbody
    rw [hheadEq, hargs3] at h0
    exact h0.symm
  rw [htbodyEq] at hQI hAtbody
  obtain ⟨-, hcompsA, veq, vsE, hveqi, hspE, hchainE, hfoldQ⟩ :=
    annotOk_spine_inv _ (.const eqName [ℓA]) (by simp) hAtbody
  obtain ⟨vα, vl, vr, rfl⟩ : ∃ vα vl vr, vsE = [vα, vl, vr] := by
    match vsE, hspE with
    | [vα, vl, vr], _ => exact ⟨vα, vl, vr, rfl⟩
    | [], h => exact nomatch h
    | [_], h => exact nomatch h.2
    | [_, _], h => exact nomatch h.2.2
    | _ :: _ :: _ :: _ :: _, h => exact nomatch h.2.2.2
  obtain ⟨hiα, hil, hir, -⟩ := hspE
  have hQeq : Q = SpineFold V veq [vα, vl, vr] := by
    rw [hfoldQ] at hQI
    exact Option.some.inj hQI |>.symm
  have hveq : veq = eqVal V (Level.substFn
      (Level.substFn φ' lps us) [uN] [ℓA]) := by
    simp only [interpExpr, heqfind] at hveqi
    rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
    rw [← Option.some.inj hveqi, heqval]
    congr 2
  obtain ⟨⟨vE₁, A₁, B₁, hpi₁, hmem₁, -⟩, hchainE'⟩ := hchainE
  obtain ⟨⟨vE₂, A₂, B₂, hpi₂, hmem₂, -⟩, hchainE''⟩ := hchainE'
  obtain ⟨⟨vE₃, A₃, B₃, hpi₃, hmem₃, -⟩, -⟩ := hchainE''
  rw [hveq] at hpi₁ hpi₂ hpi₃
  have hαu : vα ∈ˢ univ (Level.substFn (Level.substFn φ' lps us) [uN]
      [ℓA] uN) := by
    have h1 := hpi₁
    simp only [eqVal] at h1
    refine lam_dom_of_ne h1 ?_ vα hmem₁
    simp [Nat.max_eq_zero_iff]
  have hvlmem : vl ∈ˢ vα := by
    have h2 := hpi₂
    rw [eqVal_app hαu] at h2
    refine lam_dom_of_ne h2 ?_ vl hmem₂
    simp [Nat.max_eq_zero_iff]
  have hvrmem : vr ∈ˢ vα := by
    have h3 := hpi₃
    rw [eqVal_app₂ hαu hvlmem] at h3
    refine lam_dom_of_ne h3 ?_ vr hmem₃
    simp
  have hQeqv : Q = eqv vl vr := by
    rw [hQeq, hveq]
    show SpineFold V _ [vα, vl, vr] = _
    rw [show SpineFold V (eqVal V (Level.substFn
        (Level.substFn φ' lps us) [uN] [ℓA])) [vα, vl, vr] =
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn (Level.substFn φ' lps us) [uN] [ℓA]))
        vα) vl) vr from rfl]
    exact eqVal_app₃ hαu hvlmem hvrmem
  have hvlvr : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  -- ===== S4: the left side is the recursor's spine fold =====
  have hlhsEq : lhsS = Expr.mkAppN (.const (f R) (lps.map .param))
      lhsS.getAppArgs := by
    have h0 := Expr.mkAppN_getApp lhsS
    rw [hlhead] at h0
    exact h0.symm
  have hAlhs : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) lhsS :=
    hcompsA lhsS (by simp)
  rw [hlhsEq] at hAlhs
  obtain ⟨-, hlargsA, vhead, lvals, hheadI, hspL, hchainL, hfoldL⟩ :=
    annotOk_spine_inv _ (.const (f R) (lps.map .param))
      (by
        intro h0
        rw [h0] at hlarity
        exact nomatch hlarity) hAlhs
  have hvlfold : vl = SpineFold V vhead lvals := by
    rw [← hlhsEq] at hfoldL
    rw [hfoldL] at hil
    exact Option.some.inj hil |>.symm
  -- the head is the recursor's value
  have hcRi : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (.const (f R) (lps.map .param)) =
      some (m₀.val R (Level.substFn φ' lps us)) := by
    simp only [interpExpr, hfRm]
    rw [if_pos (by rw [hRmlps]; simp)]
    rw [show cim.toConstantVal.levelParams = lps from hRmlps]
    have h1 : Level.substFn (Level.substFn φ' lps us) lps
        (lps.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1, hro.2.2 R]
  have hvhead : vhead = m₀.val R (Level.substFn φ' lps us) := by
    rw [hcRi] at hheadI
    exact Option.some.inj hheadI |>.symm
  -- ===== S4b: the argument values =====
  -- the whole equation body's syntactic facts (for the components)
  obtain ⟨hWtbody0, hbtbody0, htbodyL0⟩ := htbodyWf
  have hWtbody : WScoped (rP + cnF)
      (Expr.mkAppN (.const eqName [ℓA]) [αS, lhsS, rhsS]) := by
    rw [← htbodyEq]
    simpa using hWtbody0
  have hbtbody : (Expr.mkAppN (.const eqName [ℓA])
      [αS, lhsS, rhsS]).looseBVarsBounded 0 = true := by
    rw [← htbodyEq]
    exact hbtbody0
  obtain ⟨-, -, -, hleavesTbody⟩ := TeleFitI.rest_wf hfitS2 hWmidS hbmidS
    hAmidS
  have hFtbody : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) tbody := by
    intro l hl
    rcases hleavesTbody l hl with hl' | ⟨a, ha, hla⟩
    · exact hFmidS l hl'
    · exact hΘx a ha l hla
  have hLtbody : Expr.LeavesBounded tbody := by
    rw [htbodyEq]
    exact htbodyEq ▸ htbodyL0
  -- lhsS component facts
  have hlhsMem : lhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWlhs : WScoped (rP + cnF) lhsS := by
    have h0 := hWtbody0.getAppArgs lhsS hlhsMem
    rwa [Nat.zero_add] at h0
  have hblhs : lhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hlhsMem
  have hFlhs : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) lhsS :=
    FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hlhsMem l hl)
      hFtbody
  have hLlhs : Expr.LeavesBounded lhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hlhsMem l hl)
  -- rhsS component facts
  have hrhsMem : rhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWrhsS : WScoped (rP + cnF) rhsS := by
    have h0 := hWtbody0.getAppArgs rhsS hrhsMem
    rwa [Nat.zero_add] at h0
  have hbrhsS : rhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hrhsMem
  have hFrhsS : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) rhsS :=
    FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hrhsMem l hl)
      hFtbody
  have hLrhsS : Expr.LeavesBounded rhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hrhsMem l hl)
  have hArhsS : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) rhsS :=
    hcompsA rhsS (by simp)
  -- the full constructor fit and the residual `cres`'s facts
  have hfitCfull : TeleFitI V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (cvj.type.renameConsts f)
      (fvs.take cnP ++ fvs.drop (rP)) margs cres := by
    have h0 := TeleFitI.append hfitC1 hfitR2
    rwa [List.take_append_drop] at h0
  obtain ⟨hWcres, hbcres, hAcres, hleavesCres⟩ :=
    TeleFitI.rest_wf hfitCfull (WScoped.of_not_hasFvar hCRw) hCRb hACtyR
  have hFcres : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) cres := by
    intro l hl
    rcases hleavesCres l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · refine hΘpre a ?_ l hla
        have heq : fvs.take cnP = (fvs.take (rP)).take cnP := by
          rw [List.take_take, Nat.min_eq_left hplainLe]
        rw [heq] at ha
        exact List.mem_of_mem_take ha
      · exact hΘx a ha l hla
  have hLcres : Expr.LeavesBounded cres := by
    intro l hl
    rcases hleavesCres l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
      · exact (hfvsWf a (List.mem_of_mem_drop ha)).2.2 l hla
  -- the constructor body's instantiated forms
  obtain ⟨⟨bsCI, cbodyI⟩, hstripCI⟩ := Option.isSome_iff_exists.mp
    (Expr.stripPis_instantiateLevelParams_isSome cvj.levelParams usj
      (cnP + cnF) (e := cvj.type) (by rw [hCstripSome]; rfl))
  obtain ⟨hbodyIeq, -⟩ := Expr.stripPis_instantiateLevelParams_eq
    cvj.levelParams usj _ hCstripSome hstripCI
  have hrest2eq : rest₂ = instSeq argsC0 (cnP + cnF - 1)
      (cbody.instantiateLevelParams cvj.levelParams usj) := by
    obtain ⟨mid, hmid, bs', body', hstripMid, hbodyMid, -⟩ :=
      telescopeInst_stripPis (cnP + cnF) argsC0 0 hlenC0
        (by rw [Nat.add_zero]; exact hstripCI)
    rw [TeleFitI.rest_eq hfitL2] at hmid
    obtain rfl : rest₂ = mid := Option.some.inj hmid
    simp only [Expr.stripPis, Option.some.injEq, Prod.mk.injEq]
      at hstripMid
    rw [hstripMid.2, hbodyMid, hbodyIeq]
    simp
  have hcbodyNF : cbody.hasFvar = false :=
    stripPis_body_hasFvar _ hCstripSome hCw
  have hcbodyBnd : cbody.looseBVarsBounded (cnP + cnF) = true := by
    have h0 := stripPis_body_bounded _ hCstripSome hCb
    simpa using h0
  have hcbodyLPD : cbody.allLevelParamsDefined cvj.levelParams = true :=
    Expr.allLevelParamsDefined_stripPis_body _ hCstripSome hCps
  have hcspine : cbody = Expr.mkAppN cbody.getAppFn cbody.getAppArgs :=
    (Expr.mkAppN_getApp cbody).symm
  have hrest2Args : rest₂.getAppArgs =
      cbody.getAppArgs.map (fun e => instSeq argsC0 (cnP + cnF - 1)
        (e.instantiateLevelParams cvj.levelParams usj)) := by
    rw [hrest2eq]
    calc (instSeq argsC0 (cnP + cnF - 1)
          (cbody.instantiateLevelParams cvj.levelParams usj)).getAppArgs
        = (instSeq argsC0 (cnP + cnF - 1)
            (Expr.mkAppN (cbody.instantiateLevelParams cvj.levelParams
              usj).getAppFn (cbody.instantiateLevelParams cvj.levelParams
              usj).getAppArgs)).getAppArgs := by
          rw [Expr.mkAppN_getApp]
      _ = (Expr.mkAppN (instSeq argsC0 (cnP + cnF - 1)
            (cbody.instantiateLevelParams cvj.levelParams usj).getAppFn)
            ((cbody.instantiateLevelParams cvj.levelParams
              usj).getAppArgs.map
              (instSeq argsC0 (cnP + cnF - 1) ·))).getAppArgs := by
          rw [instSeq_mkAppN]
      _ = _ := by
          rw [Expr.getAppArgs_mkAppN,
            getAppArgs_of_not_app
              (instSeq_fvars_not_app argsC0 _ hfvC0
                (getAppFn_not_app _)),
            Expr.getAppArgs_instantiateLevelParams, List.map_map]
          simp [Function.comp]
  -- `cres`'s arguments are the renamed constructor result's
  have hcresEq' : cres = instSeq (fvs.take cnP ++ fvs.drop (rP))
      (cnP + cnF - 1) (cbody.renameConsts f) := by
    rw [hcresEq, hfvsCLen]
  have hheadRenNotApp : ∀ f' a',
      cbody.getAppFn.renameConsts f ≠ .app f' a' := by
    intro f' a' hcon
    cases hfn : cbody.getAppFn with
    | app g b => exact getAppFn_not_app cbody g b hfn
    | bvar _ => rw [hfn] at hcon; exact nomatch hcon
    | fvar _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | sort _ => rw [hfn] at hcon; exact nomatch hcon
    | const _ _ => rw [hfn] at hcon; exact nomatch hcon
    | lam _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | forallE _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | letE _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | lit _ => rw [hfn] at hcon; exact nomatch hcon
    | proj _ _ _ => rw [hfn] at hcon; exact nomatch hcon
  have hcresArgs : cres.getAppArgs = cbody.getAppArgs.map
      (fun e => instSeq (fvs.take cnP ++ fvs.drop (rP))
        (cnP + cnF - 1) (e.renameConsts f)) := by
    rw [hcresEq']
    calc (instSeq (fvs.take cnP ++ fvs.drop (rP))
          (cnP + cnF - 1) (cbody.renameConsts f)).getAppArgs
        = (instSeq (fvs.take cnP ++ fvs.drop (rP))
            (cnP + cnF - 1)
            (Expr.mkAppN (cbody.getAppFn.renameConsts f)
              (cbody.getAppArgs.map (·.renameConsts f)))).getAppArgs := by
          rw [← renameConsts_mkAppN, Expr.mkAppN_getApp]
      _ = (Expr.mkAppN (instSeq (fvs.take cnP ++ fvs.drop (rP))
            (cnP + cnF - 1) (cbody.getAppFn.renameConsts f))
            ((cbody.getAppArgs.map (·.renameConsts f)).map
              (instSeq (fvs.take cnP ++ fvs.drop (rP))
                (cnP + cnF - 1) ·))).getAppArgs := by
          rw [instSeq_mkAppN]
      _ = _ := by
          rw [Expr.getAppArgs_mkAppN,
            getAppArgs_of_not_app
              (instSeq_fvars_not_app _ _ hfvsCShapes hheadRenNotApp),
            List.map_map]
          simp [Function.comp]
  -- ===== S4c: the canonical index values =====
  have hspC0 : FvarSpine d₂ ρ₂ argsC0 margs :=
    FvarSpine_of_fit hfitL2 hfvC0
  have hidxPt := InterpSpine.of_mapM hidx
  have hsanShapes : ∀ a ∈ argsC0.map sanitizeArg, ∃ i n t,
      a = Expr.fvar i n t := hshC'
  have hsanLen : (argsC0.map sanitizeArg).length = cnP + cnF := by
    rw [List.length_map, hlenC0]
  have hsanInstId : (argsC0.map sanitizeArg).map
      (·.instantiateLevelParams cvj.levelParams usj) =
      argsC0.map sanitizeArg := by
    have h0 : (argsC0.map sanitizeArg).map
        (·.instantiateLevelParams cvj.levelParams usj) =
        (argsC0.map sanitizeArg).map id :=
      List.map_congr_left (fun a ha => by
        obtain ⟨i, n, rfl⟩ := hshC a ha
        rfl)
    rw [h0, List.map_id]
  have hcanVal : ∀ (j : Nat) (e : Expr) (v : V),
      (cres.getAppArgs.drop cnP)[j]? = some e →
      (args.drop (rP))[j]? = some v →
      interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j' => (args.take (rP) ++
          margs.drop cnP).getD j' SetTheory.empty) e = some v := by
    intro j e v he hv
    rw [hcresArgs, ← List.map_drop, List.getElem?_map] at he
    cases hcarg : (cbody.getAppArgs.drop cnP)[j]? with
    | none => rw [hcarg] at he; exact nomatch he
    | some carg => ?_
    rw [hcarg] at he
    obtain rfl := Option.some.inj he
    have hrestj : (rest₂.getAppArgs.drop cnP)[j]? =
        some (instSeq argsC0 (cnP + cnF - 1)
          (carg.instantiateLevelParams cvj.levelParams usj)) := by
      rw [hrest2Args, ← List.map_drop, List.getElem?_map, hcarg]
      rfl
    have hval := InterpSpine.pointwise hidxPt j hrestj hv
    have hcargMem : carg ∈ cbody.getAppArgs :=
      List.mem_of_mem_drop (List.mem_of_getElem? hcarg)
    have hcargNF : carg.hasFvar = false :=
      hasFvar_getAppArgs hcbodyNF _ hcargMem
    have hcargBnd : carg.looseBVarsBounded (cnP + cnF) = true :=
      looseBVarsBounded_getAppArgs hcbodyBnd _ hcargMem
    have hcargLPD : carg.allLevelParamsDefined cvj.levelParams = true :=
      Expr.allLevelParamsDefined_getAppArgs hcbodyLPD _ hcargMem
    -- rename away, cross frames, move the levels
    rw [interp_instSeq_ren hro hfvsCShapes]
    have hcross1 := interp_instSeq_fvarFrames (cval := m₀.val)
      (env := env₀) (φ := Level.substFn φ' lps us) (e := carg) hcargNF
      (by rw [hfvsCLen]; exact hcargBnd) hspWctor hspC
    rw [hfvsCLen, hsanLen] at hcross1
    rw [hcross1]
    have hstep2 : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        d₂ ρ₂ (instSeq (argsC0.map sanitizeArg) (cnP + cnF - 1) carg) =
        interpExpr V m₀.val env₀
          (Level.substFn φ' cvj.levelParams usj)
          d₂ ρ₂ (instSeq (argsC0.map sanitizeArg) (cnP + cnF - 1)
            carg) := by
      refine (interp_params_ext hcvp hleveq _ _ _ ?_).symm
      exact Expr.allLevelParamsDefined_instSeq_fvars _ _
        (fun a ha => ⟨by
          obtain ⟨i, n, rfl⟩ := hshC a ha
          rfl, hshC' a ha⟩)
        hcargLPD
    rw [hstep2, ← interp_instLevels hcvp]
    rw [Expr.instSeq_instantiateLevelParams_fvars _ _ _ _ _ hshC',
      hsanInstId]
    have hcross2 := interp_instSeq_fvarFrames (cval := m₀.val)
      (env := env₀) (φ := φ')
      (e := carg.instantiateLevelParams cvj.levelParams usj)
      (by rw [hasFvar_instantiateLevelParams]; exact hcargNF)
      (by
        rw [hsanLen, looseBVarsBounded_instantiateLevelParams]
        exact hcargBnd)
      hspC hspC0
    rw [hsanLen, hlenC0] at hcross2
    rw [hcross2]
    exact hval
  have hcresArgsLen : cres.getAppArgs.length = cnP + (mI - rP) := hclen
  have hspIdxCan : InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j' => (args.take (rP) ++
        margs.drop cnP).getD j' SetTheory.empty)
      (cres.getAppArgs.drop cnP) (args.drop (rP)) :=
    InterpSpine.of_pointwise (by
      rw [List.length_drop, hcresArgsLen, List.length_drop, hlena]
      omega) hcanVal
  -- `cres`'s per-argument facts (for the defeq side conditions)
  have hcresArgW : ∀ e ∈ cres.getAppArgs,
      WScoped (rP + cnF) e :=
    fun e he => hWcres.getAppArgs e he
  have hcresArgB : ∀ e ∈ cres.getAppArgs,
      e.looseBVarsBounded 0 = true :=
    fun e he => looseBVarsBounded_getAppArgs hbcres e he
  have hcresArgL : ∀ e ∈ cres.getAppArgs, Expr.LeavesBounded e :=
    fun e he l hl => hLcres l (fvarLeaves_getAppArgs he l hl)
  have hcresArgF : ∀ e ∈ cres.getAppArgs,
      FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j' => (args.take (rP) ++
          margs.drop cnP).getD j' SetTheory.empty) e :=
    fun e he => FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs he l hl) hFcres
  have hcresArgA : ∀ e ∈ cres.getAppArgs,
      AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j' => (args.take (rP) ++
          margs.drop cnP).getD j' SetTheory.empty) e := by
    intro e he
    have hne : cres.getAppArgs ≠ [] := by
      intro h0
      rw [h0] at he
      exact nomatch he
    have hAcres' : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j' => (args.take (rP) ++
          margs.drop cnP).getD j' SetTheory.empty)
        (Expr.mkAppN cres.getAppFn cres.getAppArgs) := by
      rw [Expr.mkAppN_getApp]
      exact hAcres
    obtain ⟨-, hargsA, -⟩ := annotOk_spine_inv _ cres.getAppFn hne hAcres'
    exact hargsA e he
  -- lhsS's per-argument facts
  have hlargsW : ∀ e ∈ lhsS.getAppArgs,
      WScoped (rP + cnF) e :=
    fun e he => hWlhs.getAppArgs e he
  have hlargsB : ∀ e ∈ lhsS.getAppArgs, e.looseBVarsBounded 0 = true :=
    fun e he => looseBVarsBounded_getAppArgs hblhs e he
  have hlargsL : ∀ e ∈ lhsS.getAppArgs, Expr.LeavesBounded e :=
    fun e he l hl => hLlhs l (fvarLeaves_getAppArgs he l hl)
  have hlargsF : ∀ e ∈ lhsS.getAppArgs,
      FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j' => (args.take (rP) ++
          margs.drop cnP).getD j' SetTheory.empty) e :=
    fun e he => FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs he l hl) hFlhs
  -- the index arguments' values, via the kernel's defeqs
  have hlvalsLen : lvals.length = mI + 1 := by
    have h0 := InterpSpine.length hspL
    omega
  have hidxArgsVal : ∀ (j : Nat) (e : Expr) (v : V),
      ((lhsS.getAppArgs.drop (rP)).take (mI - rP))[j]? = some e →
      (args.drop (rP))[j]? = some v →
      interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j' => (args.take (rP) ++
          margs.drop cnP).getD j' SetTheory.empty) e = some v := by
    intro j e v he hv
    have hj : j < mI - rP := by
      rcases Nat.lt_or_ge j (mI - rP) with hlt | hge
      · exact hlt
      · rw [List.getElem?_eq_none (by
          rw [List.length_take]
          omega)] at he
        exact nomatch he
    obtain ⟨ce, hce⟩ : ∃ ce, (cres.getAppArgs.drop cnP)[j]? = some ce :=
      ⟨_, List.getElem?_eq_getElem (by
        rw [List.length_drop, hcresArgsLen]; omega)⟩
    have hde := DefEqListOk.pointwise hdeIdx j he hce
    have hcei := hcanVal j ce v hce hv
    have hepos : lhsS.getAppArgs[rP + j]? = some e := by
      rw [List.getElem?_take_of_lt hj] at he
      rw [← List.getElem?_drop]
      exact he
    have heMem : e ∈ lhsS.getAppArgs := List.mem_of_getElem? hepos
    have hceMem : ce ∈ cres.getAppArgs :=
      List.mem_of_mem_drop (List.mem_of_getElem? hce)
    obtain ⟨ve, hvepos⟩ : ∃ ve, lvals[rP + j]? = some ve :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have hei := InterpSpine.pointwise hspL _ hepos hvepos
    have hvv : ve = v :=
      isDefEqCore_sound m₀ F hde (hlargsW e heMem) (hcresArgW ce hceMem)
        (hlargsB e heMem) (hcresArgB ce hceMem) (hlargsL e heMem)
        (hcresArgL ce hceMem) (hlargsF e heMem) (hcresArgF ce hceMem)
        (hlargsA e heMem) (hcresArgA ce hceMem) hei hcei
    rw [hei, hvv]
  have hspIdx : InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j' => (args.take (rP) ++
        margs.drop cnP).getD j' SetTheory.empty)
      ((lhsS.getAppArgs.drop (rP)).take (mI - rP))
      (args.drop (rP)) :=
    InterpSpine.of_pointwise (by
      rw [List.length_take, List.length_drop, hlarity,
        List.length_drop, hlena]
      omega) hidxArgsVal
  -- ===== S4d: the major's value =====
  have hcCi : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j' => (args.take (rP) ++
        margs.drop cnP).getD j' SetTheory.empty)
      (.const (f ctor) (cvj.levelParams.map .param)) =
      some (m₀.val ctor (Level.substFn φ' cvj.levelParams usj)) := by
    simp only [interpExpr, hfCm]
    rw [if_pos (by rw [hCmlps]; simp)]
    rw [show cimC.toConstantVal.levelParams = cvj.levelParams from hCmlps]
    have h1 : Level.substFn (Level.substFn φ' lps us) cvj.levelParams
        (cvj.levelParams.map .param) = Level.substFn φ' lps us :=
      funext (fun p => Level.substFn_map_param)
    rw [h1, hro.2.2 ctor]
    exact congrArg some (hcvp _ _ hfj _ _
      (fun p hp => (hleveq p hp).symm))
  have hmajorI : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j' => (args.take (rP) ++
        margs.drop cnP).getD j' SetTheory.empty)
      (lhsS.getAppArgs.getLastD (.bvar 0)) = some tv := by
    rw [hmaj, interp_mkAppN _ _ hcCi (InterpSpine_of_FvarSpine hspWctor),
      htv]
  -- ===== S4e: the whole left value =====
  obtain ⟨lastE, hlastE⟩ : ∃ x,
      lhsS.getAppArgs.drop (mI) = [x] := by
    have hlen1 : (lhsS.getAppArgs.drop (mI)).length = 1 := by
      rw [List.length_drop, hlarity]
      omega
    cases hdd : lhsS.getAppArgs.drop (mI) with
    | nil => rw [hdd] at hlen1; exact nomatch hlen1
    | cons x xs =>
      rw [hdd] at hlen1
      simp only [List.length_cons] at hlen1
      have : xs = [] := by
        cases xs with
        | nil => rfl
        | cons _ _ => simp at hlen1
      subst this
      exact ⟨x, rfl⟩
  have hlastIdx : lhsS.getAppArgs[mI]? = some lastE := by
    have h0 := congrArg (fun l => l[0]?) hlastE
    simp only [List.getElem?_drop] at h0
    simpa using h0
  have hlastD : lhsS.getAppArgs.getLastD (.bvar 0) = lastE := by
    rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?]
    rw [hlarity, show mI + 1 - 1 = mI
      from by omega, hlastIdx]
    rfl
  have hlargsDecomp : lhsS.getAppArgs =
      lhsS.getAppArgs.take (rP) ++
      ((lhsS.getAppArgs.drop (rP)).take (mI - rP) ++ [lastE]) := by
    have h0 := List.take_append_drop (rP) lhsS.getAppArgs
    have h1 := List.take_append_drop (mI - rP)
      (lhsS.getAppArgs.drop (rP))
    have h2 : (lhsS.getAppArgs.drop (rP)).drop (mI - rP) =
        [lastE] := by
      rw [List.drop_drop]
      first
        | exact hlastE
        | (rw [show (mI - rP) + rP = mI from by
            omega]; exact hlastE)
        | (rw [show rP + (mI - rP) = mI from by
            omega]; exact hlastE)
        | (rw [show mI = (mI - rP) + rP from by
            omega] at hlastE; exact hlastE)
    rw [← h2, h1, h0]
  have hspPrefix : InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j' => (args.take (rP) ++
        margs.drop cnP).getD j' SetTheory.empty)
      (lhsS.getAppArgs.take (rP)) (args.take (rP)) := by
    rw [hlpre]
    exact InterpSpine_of_FvarSpine hspWpre
  have hmajorI' : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j' => (args.take (rP) ++
        margs.drop cnP).getD j' SetTheory.empty) lastE = some tv := by
    rw [← hlastD]
    exact hmajorI
  have hspFull : InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j' => (args.take (rP) ++
        margs.drop cnP).getD j' SetTheory.empty)
      lhsS.getAppArgs
      (args.take (rP) ++ (args.drop (rP) ++ [tv])) := by
    have h0 := InterpSpine.append hspPrefix
      (InterpSpine.append hspIdx
        (show InterpSpine m₀.val env₀ (Level.substFn φ' lps us)
          (rP + cnF)
          (fun j' => (args.take (rP) ++
            margs.drop cnP).getD j' SetTheory.empty) [lastE] [tv] from
          ⟨hmajorI', trivial⟩))
    rwa [← hlargsDecomp] at h0
  have hlvalsEq : lvals =
      args.take (rP) ++ (args.drop (rP) ++ [tv]) := by
    have h1 := InterpSpine.mapM_eq hspL
    have h2 := InterpSpine.mapM_eq hspFull
    rw [h1] at h2
    exact Option.some.inj h2
  have hvlEq : vl = SpineFold V (m₀.val R (Level.substFn φ' lps us))
      (args ++ [tv]) := by
    rw [hvlfold, hvhead, hlvalsEq]
    congr 1
    rw [← List.append_assoc, List.take_append_drop]
  -- ===== S5: the right side is the applied rule =====
  -- mkAppN closure helpers
  have hWapp : ∀ (xs : List Expr) (h : Expr),
      WScoped (rP + cnF) h →
      (∀ x ∈ xs, WScoped (rP + cnF) x) →
      WScoped (rP + cnF) (Expr.mkAppN h xs) := by
    intro xs
    induction xs with
    | nil => intro h hh _; exact hh
    | cons x xs ih =>
      intro h hh hxs
      show WScoped _ (Expr.mkAppN (.app h x) xs)
      refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      simp only [WScoped]
      exact ⟨hh, hxs x List.mem_cons_self⟩
  have hbapp : ∀ (xs : List Expr) (h : Expr),
      h.looseBVarsBounded 0 = true →
      (∀ x ∈ xs, x.looseBVarsBounded 0 = true) →
      (Expr.mkAppN h xs).looseBVarsBounded 0 = true := by
    intro xs
    induction xs with
    | nil => intro h hh _; exact hh
    | cons x xs ih =>
      intro h hh hxs
      show (Expr.mkAppN (.app h x) xs).looseBVarsBounded 0 = true
      refine ih _ ?_ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      simp only [Expr.looseBVarsBounded, Bool.and_eq_true]
      exact ⟨hh, hxs x List.mem_cons_self⟩
  have hlapp : ∀ (xs : List Expr) (h : Expr) {l},
      l ∈ (Expr.mkAppN h xs).fvarLeaves →
      l ∈ h.fvarLeaves ∨ ∃ x ∈ xs, l ∈ x.fvarLeaves := by
    intro xs
    induction xs with
    | nil => intro h l hl; exact Or.inl hl
    | cons x xs ih =>
      intro h l hl
      rcases ih (.app h x) hl with hl' | ⟨y, hy, hly⟩
      · simp only [fvarLeaves, List.mem_append] at hl'
        rcases hl' with hl' | hl'
        · exact Or.inl hl'
        · exact Or.inr ⟨x, List.mem_cons_self, hl'⟩
      · exact Or.inr ⟨y, List.mem_cons_of_mem _ hy, hly⟩
  -- public prefix Θ
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec (rP) 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf (rP) 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  have hspP : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      fvsP (args.take (rP)) := by
    refine FvarSpine_of_open hopenP (by rw [hpreLen]) (by omega) ?_
    intro k v hkv
    refine hρWval k v ?_
    have hk : k < (args.take (rP)).length := by
      rcases Nat.lt_or_ge k (args.take (rP)).length with h | h
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hkv
        exact nomatch hkv
    rw [List.getElem?_append_left hk]
    exact hkv
  have hmemP := fit_mem_transfer (φ := Level.substFn φ' lps us)
    htyw htyb htyPreStrip hfvsPInst (by rw [hfvsPLen]) hspP hspR hfitRawR
  obtain ⟨hfitP, hΘP⟩ := self_walk hfvsPInst hspP
    (fun a ha => ((hfvsPWf a ha).1).mono (by omega))
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw)
    (AnnotOk.closed_invariant htyw _ _ (hAty (Level.substFn φ' lps us)))
    hmemP
  -- the constructor's public parameter walk
  have hspPtake : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvsP.take cnP) (margs.take cnP) := by
    have h0 := FvarSpine.take cnP hspP
    rw [List.take_take, Nat.min_eq_left hplainLe] at h0
    rwa [← hparam'] at h0
  -- full public constructor packages at the (fvsP ++ xFvsP) spine
  obtain ⟨hxInst, hxLen, hxShape⟩ :=
    openPisAtFvars_spec cnF (rP) hopenX
  have hpubP := instPisAt_append_of (fvsP.take cnP) hcinstP hxInst
  have hspX : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      xFvsP (margs.drop cnP) := by
    refine FvarSpine_of_open hopenX (by rw [List.length_drop, hlenm]; omega)
      (by omega) ?_
    intro k v hkv
    have h0 : (args.take (rP) ++
        margs.drop cnP)[rP + k]? = some v := by
      rw [List.getElem?_append_right (by rw [hpreLen]; omega), hpreLen,
        show rP + k - (rP) = k from by omega]
      exact hkv
    show (args.take (rP) ++
      margs.drop cnP).getD (rP + k) SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD, h0]
    rfl
  have hspPXctor : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvsP.take cnP ++ xFvsP) margs := by
    have h0 := FvarSpine.append hspPtake hspX
    rwa [List.take_append_drop] at h0
  have hfvsPXLen : (fvsP.take cnP ++ xFvsP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, hfvsPLen, hxLen]
    omega
  have hmemPubP := fit_mem_transfer (φ := Level.substFn φ' lps us)
    hCw hCb hCstripSome hpubP hfvsPXLen hspPXctor hspC hfitC4
  have hcdomsPLen : cdomsP.length = cnP := by
    rw [instPisAt_length _ hcinstP, List.length_take, hfvsPLen]
    omega
  -- crestP's facts
  have hfvsPWs : ∀ a ∈ fvsP.take cnP, WScoped (rP) a := by
    intro a ha
    have := (hfvsPWf a (List.mem_of_mem_take ha)).1
    simpa using this
  have hWcrestPre : WScoped (rP) crestP :=
    (instPisAt_wscoped _ hcinstP
      (WScoped.of_not_hasFvar hCw) hfvsPWs).2
  obtain ⟨hfitCP, hIcrestP⟩ := peel_walk hcinstP hspPtake
    (fun a ha => ((hfvsPWf a (List.mem_of_mem_take ha)).1).mono (by omega))
    (WScoped.of_not_hasFvar hCw)
    (AnnotOk.closed_invariant hCw _ _ (hACty (Level.substFn φ' lps us)))
    (by
      obtain ⟨TC, hTCc⟩ := hICty (Level.substFn φ' lps us)
      refine ⟨TC, ?_⟩
      rw [interp_closed_invariant hCw _ _]
      exact hTCc)
    (fun k a v ha hv => by
      have hkA : k < cnP := by
        rcases Nat.lt_or_ge k cnP with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by rw [hcdomsPLen]; omega)] at ha
          exact nomatch ha
      refine hmemPubP k a v ?_ ?_
      · rw [List.getElem?_append_left (by rw [hcdomsPLen]; omega)]
        exact ha
      · rw [List.getElem?_take_of_lt hkA] at hv
        exact hv)
  -- crestP's facts at the master frame
  obtain ⟨hWcrestP, hbcrestP, hAcrestP, hleavesCrestP⟩ :=
    TeleFitI.rest_wf hfitCP (WScoped.of_not_hasFvar hCw) hCb
      (AnnotOk.closed_invariant hCw _ _ (hACty (Level.substFn φ' lps us)))
  have hFcrestP : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) crestP := by
    intro l hl
    rcases hleavesCrestP l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hΘP a (List.mem_of_mem_take ha) l hla
  have hLcrestP : Expr.LeavesBounded crestP := by
    intro l hl
    rcases hleavesCrestP l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact (hfvsPWf a (List.mem_of_mem_take ha)).2.2 l hla
  obtain ⟨hxWf, -⟩ := openPisAtFvars_wf cnF (rP) hopenX
    hWcrestPre hbcrestP hLcrestP
  obtain ⟨hfitXP, hΘX2⟩ := self_walk hxInst hspX
    (fun a ha => ((hxWf a ha).1).mono (by omega))
    hWcrestP hbcrestP hLcrestP hFcrestP hAcrestP
    (fun k a v ha hv => by
      refine hmemPubP (cnP + k) a v ?_ ?_
      · rw [List.getElem?_append_right (by rw [hcdomsPLen]; omega),
          hcdomsPLen, show cnP + k - cnP = k from by omega]
        exact ha
      · rw [List.getElem?_drop] at hv
        exact hv)
  -- the λ-tower walk of the rule's right-hand side
  have hΘfull : ∀ a ∈ fvsP ++ xFvsP,
      FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘP a ha
    · exact hΘX2 a ha
  have hLfull : ∀ a ∈ fvsP ++ xFvsP, Expr.LeavesBounded a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsPWf a ha).2.2
    · exact (hxWf a ha).2.2
  have hWfull : ∀ a ∈ fvsP ++ xFvsP,
      WScoped (rP + cnF) a := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ((hfvsPWf a ha).1).mono (by omega)
    · exact ((hxWf a ha).1).mono (by omega)
  have hspPX : FvarSpine (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (fvsP ++ xFvsP)
      (args.take (rP) ++ margs.drop cnP) :=
    FvarSpine.append hspP hspX
  have hArhsW : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) rhsA :=
    AnnotOk.closed_invariant hrhsw _ _ (hArhs (Level.substFn φ' lps us))
  obtain ⟨L0, hL0c⟩ := hIrhs (Level.substFn φ' lps us)
  have hL0 : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) rhsA = some L0 := by
    rw [interp_closed_invariant hrhsw _ _]
    exact hL0c
  have hfitLam := lam_walk m₀ F hlinst hdeLam hspPX hWfull hΘfull hLfull
    (WScoped.of_not_hasFvar hrhsw) hrhsb
    (Expr.LeavesBounded.of_not_hasFvar hrhsw)
    (FvarsOk.of_not_hasFvar hrhsw) hArhsW ⟨L0, hL0⟩
  obtain ⟨Bf, hBfI, hBfold, hchainL2⟩ := TeleFitLam.fold hfitLam hArhsW hL0
  -- the applied form's typing and value
  have hrhsRw : (rhsA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact hrhsw
  have hArhsRen : AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) (rhsA.renameConsts f) :=
    AnnotOk.closed_invariant hrhsRw _ _
      (AnnotOk.renameConsts hro rhsA 0 (rho0 V)
        (hArhs (Level.substFn φ' lps us)))
  have hLren : interpExpr V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (rhsA.renameConsts f) = some L0 := by
    rw [interp_renameConsts hro]
    exact hL0
  have hfvsA : ∀ x ∈ fvs, AnnotOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty) x := by
    intro x hx
    obtain ⟨i, n, t, rfl⟩ := hfvsShapes x hx
    simp [AnnotOk]
  obtain ⟨hAappF, hIappF⟩ := annotOk_spine fvs (rhsA.renameConsts f)
    hArhsRen hLren hfvsA (InterpSpine_of_FvarSpine hspW) hchainL2
  -- side conditions for the statement's right side
  have hΘfvs : ∀ a ∈ fvs,
      FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
        (rP + cnF)
        (fun j => (args.take (rP) ++
          margs.drop cnP).getD j SetTheory.empty) a := by
    intro a ha
    rw [← List.take_append_drop (rP) fvs] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘpre a ha
    · exact hΘx a ha
  have hWappF : WScoped (rP + cnF)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) :=
    hWapp fvs _ (WScoped.of_not_hasFvar hrhsRw) hfvsW
  have hbappF : (Expr.mkAppN (rhsA.renameConsts f)
      fvs).looseBVarsBounded 0 = true := by
    refine hbapp fvs _ ?_ (FvarSpine.bounded hspW)
    rw [looseBVarsBounded_renameConsts]
    exact hrhsb
  have hLappF : Expr.LeavesBounded
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    intro l hl
    rcases hlapp fvs _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hl'
      cases hl'
    · exact (hfvsWf x hx).2.2 l hlx
  have hFappF : FvarsOk V m₀.val env₀ (Level.substFn φ' lps us)
      (rP + cnF)
      (fun j => (args.take (rP) ++
        margs.drop cnP).getD j SetTheory.empty)
      (Expr.mkAppN (rhsA.renameConsts f) fvs) := by
    intro l hl
    rcases hlapp fvs _ hl with hl' | ⟨x, hx, hlx⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsRw] at hl'
      cases hl'
    · exact hΘfvs x hx l hlx
  have hvrFold : vr = SpineFold V L0
      (args.take (rP) ++ margs.drop cnP) :=
    isDefEqCore_sound m₀ F hdeRhs hWrhsS hWappF hbrhsS hbappF hLrhsS
      hLappF hFrhsS hFappF hArhsS hAappF hir hIappF
  -- ===== S6: conclusion =====
  refine ⟨L0, hL0c, ?_, ?_⟩
  · rw [← hvlEq, hvlvr, hvrFold]
  · exact hchainL2

/-! ## The stage facts of the total rule equality (task #58)

`RecRulesOk`'s per-rule clause is the total λ-equality of the
canonical iota left-hand side tower against the stored rule right-hand
side.  `TowerOk.of_stages` assembles the pointwise tower spec from
*flat stage facts at the canonical list valuations*; this section
derives those facts from the kernel-checked `_model.iota_j` pins:
per stage, the frame annotation and the rule tower's instantiated
binder domain are kernel-definitionally equal (`hdeLam`), so their
interpretations agree — the wf packages on both sides come from
sequential telescope walks over the value prefix. -/

/-- The pointwise membership invariant carried through the tower
stages: each chosen value inhabits its frame annotation's
interpretation at the *prefix* canonical valuation. -/
def FramePref (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (spine : List Expr) (xs : List V) : Prop :=
  ∀ (j : Nat) (v : V) (fv : Expr), xs[j]? = some v →
    spine[j]? = some fv →
    ∃ B, interpExpr V cval env φ j
        (fun i => (xs.take j).getD i SetTheory.empty)
        (Expr.fvarTypeD fv) = some B ∧ v ∈ˢ B

/-- Everything `isDefEqCore_sound` wants of one side. -/
def InterpPkg (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (D : Nat) (ρ : Nat → V) (e : Expr) : Prop :=
  WScoped D e ∧ e.looseBVarsBounded 0 = true ∧ Expr.LeavesBounded e ∧
  FvarsOk V cval env φ D ρ e ∧ AnnotOk V cval env φ D ρ e ∧
  ∃ P, interpExpr V cval env φ D ρ e = some P

/-- The stage-fact tail: a kernel definitional equality between two
packaged sides at the padded master frame canonicalizes onto the stage
frame — the annotation side's interpretation and truthfulness, and the
(erased-)interpretation of the walk side, agree there. -/
theorem stage_out {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {a b : Expr} {k D : Nat} {xs : List V}
    (hk : xs.length = k) (hkD : k ≤ D)
    (hde : isDefEqCore env₀ F D a b = .ok true)
    (hpa : InterpPkg m₀.val env₀ ψ D
      (fun i => xs.getD i SetTheory.empty) a)
    (hpb : InterpPkg m₀.val env₀ ψ D
      (fun i => xs.getD i SetTheory.empty) b)
    (hwa : WScoped k a) (hwb : WScoped k b) :
    ∃ A, interpExpr V m₀.val env₀ ψ k
        (fun i => xs.getD i SetTheory.empty) a = some A ∧
      (∀ e, Expr.ErasedEq e b → interpExpr V m₀.val env₀ ψ k
        (fun i => xs.getD i SetTheory.empty) e = some A) ∧
      AnnotOk V m₀.val env₀ ψ k
        (fun i => xs.getD i SetTheory.empty) a := by
  obtain ⟨hWa, hba, hLa, hFa, hAa, Pa, hPa⟩ := hpa
  obtain ⟨hWb, hbb, hLb, hFb, hAb, Pb, hPb⟩ := hpb
  have hPab : Pa = Pb :=
    isDefEqCore_sound m₀ F hde hWa hWb hba hbb hLa hLb hFa hFb hAa hAb
      hPa hPb
  subst hk
  have htake : xs.take xs.length = xs := List.take_of_length_le
    (Nat.le_refl _)
  -- canonicalize the annotation side
  have hcanA := interp_getD_canon (cval := m₀.val) (env := env₀)
    (φ := ψ) (e := a) (xs := xs) hwa (Nat.le_refl _) hkD
  rw [htake] at hcanA
  have hcanB := interp_getD_canon (cval := m₀.val) (env := env₀)
    (φ := ψ) (e := b) (xs := xs) hwb (Nat.le_refl _) hkD
  rw [htake] at hcanB
  refine ⟨Pa, by rw [← hcanA]; exact hPa, ?_, ?_⟩
  · intro e hee
    rw [interp_erasedEq hee, ← hcanB, hPb, hPab]
  · have h := annotOk_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := a) (xs := xs) hwa (Nat.le_refl _) hkD hAa
    rwa [htake] at h

/-- The rule-tower side's stage package: walking the rule right-hand
side's λ-tower along the frame prefix packages the current stage's
instantiated binder domain at the padded master frame. -/
theorem stage_pkg_lam {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {D : Nat} {ρ : Nat → V}
    {spine : List Expr} {rhsA lrest ld : Expr} {ldoms : List Expr}
    (hlinst : Expr.instLamsAt spine rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ D (spine.map Expr.fvarTypeD) ldoms)
    {k : Nat} {vs : List V}
    (hk : k < spine.length)
    (hld : ldoms[k]? = some ld)
    (hsp : FvarSpine D ρ (spine.take k) vs)
    (hws : ∀ a ∈ spine.take k, WScoped D a)
    (hΘ : ∀ a ∈ spine.take k, FvarsOk V m₀.val env₀ ψ D ρ a)
    (hLs : ∀ a ∈ spine.take k, Expr.LeavesBounded a)
    (hwsK : ∀ a ∈ spine.take k, WScoped k a)
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∃ L, interpClosed V m₀.val env₀ ψ rhsA = some L) :
    InterpPkg m₀.val env₀ ψ D ρ ld ∧ WScoped k ld := by
  -- split the λ-walk at the prefix
  have hlinst' : Expr.instLamsAt (spine.take k ++ spine.drop k) rhsA =
      some (ldoms, lrest) := by
    rw [List.take_append_drop]
    exact hlinst
  obtain ⟨lds₁, lamMid, lds₂, hopL1, hopL2, hldsSplit⟩ :=
    instLamsAt_append (spine.take k) (spine.drop k) hlinst'
  have hlds₁len : lds₁.length = k := by
    rw [instLamsAt_length _ hopL1, List.length_take]
    omega
  have hlds₁ : lds₁ = ldoms.take k := by
    have h := congrArg (List.take k) hldsSplit
    rw [List.take_append_of_le_length (by omega)] at h
    rw [List.take_of_length_le (l := lds₁) (by omega)] at h
    exact h.symm
  -- the prefix defeq facts
  have hdeTk : DefEqListOk F env₀ D ((spine.take k).map Expr.fvarTypeD)
      lds₁ := by
    have h := DefEqListOk.take k hdeLam
    rwa [← List.map_take, ← hlds₁] at h
  -- the right-hand side's closed facts at the frame
  have hWr : WScoped D rhsA := WScoped.of_not_hasFvar hrhsw
  have hLr : Expr.LeavesBounded rhsA :=
    Expr.LeavesBounded.of_not_hasFvar hrhsw
  have hFr : FvarsOk V m₀.val env₀ ψ D ρ rhsA :=
    FvarsOk.of_not_hasFvar hrhsw
  have hAr : AnnotOk V m₀.val env₀ ψ D ρ rhsA :=
    AnnotOk.closed_invariant hrhsw _ _ hArhs
  obtain ⟨L0, hL0c⟩ := hIrhs
  have hL0 : interpExpr V m₀.val env₀ ψ D ρ rhsA = some L0 := by
    rw [interp_closed_invariant hrhsw _ _]
    exact hL0c
  -- walk the λ-tower along the prefix
  have hfitLam := lam_walk m₀ F hopL1 hdeTk hsp hws hΘ hLs hWr hrhsb
    hLr hFr hAr ⟨L0, hL0⟩
  obtain ⟨Bmid, hBmid, -, -⟩ := TeleFitLam.fold hfitLam hAr hL0
  obtain ⟨hWlm, hblm, hAlm, hllm⟩ := TeleFitLam.rest_wf hfitLam hWr
    hrhsb hAr
  have hFlm : FvarsOk V m₀.val env₀ ψ D ρ lamMid := by
    intro l hl
    rcases hllm l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at hl'
      cases hl'
    · exact hΘ a ha l hla
  have hLlm : Expr.LeavesBounded lamMid := by
    intro l hl
    rcases hllm l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hrhsw] at hl'
      cases hl'
    · exact hLs a ha l hla
  -- scoping at the stage frame
  obtain ⟨-, hWlmK⟩ := instLamsAt_wscoped (D := k) (spine.take k)
    hopL1 (WScoped.of_not_hasFvar hrhsw) hwsK
  -- invert the head binder
  have hdropC : spine.drop k = spine[k] :: spine.drop (k + 1) :=
    List.drop_eq_getElem_cons hk
  rw [hdropC] at hopL2
  obtain ⟨nL, domL, bodyL, mL, lds₂', rfl, hlds₂c, -⟩ :=
    instLamsAt_cons_inv hopL2
  have hdomL : domL = ld := by
    have h0 : ldoms[k]? = some domL := by
      rw [hldsSplit, List.getElem?_append_right (by omega), hlds₁len,
        Nat.sub_self, hlds₂c]
      rfl
    rw [hld] at h0
    exact (Option.some.inj h0).symm
  replace hdomL : ld = domL := hdomL.symm
  subst hdomL
  -- unpack the head binder's facts
  have hAlm' := hAlm
  simp only [AnnotOk] at hAlm'
  obtain ⟨hAld, ⟨cod, hcod⟩, -⟩ := hAlm'
  have hWld : WScoped D ld ∧ WScoped D bodyL := by
    simpa [WScoped] using hWlm
  have hbld : ld.looseBVarsBounded 0 = true ∧
      bodyL.looseBVarsBounded 1 = true := by
    revert hblm; simp [Expr.looseBVarsBounded]
  have hLld : Expr.LeavesBounded ld := fun l hl =>
    hLlm l (by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl)
  have hFld : FvarsOk V m₀.val env₀ ψ D ρ ld :=
    FvarsOk.of_subset (fun l hl => by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFlm
  have hIld : ∃ B, interpExpr V m₀.val env₀ ψ D ρ ld = some B := by
    revert hBmid
    simp only [interpExpr, hcod]
    cases hB0 : interpExpr V m₀.val env₀ ψ D ρ ld with
    | none => intro h; exact nomatch h
    | some B => intro _; exact ⟨B, rfl⟩
  have hWldK : WScoped k ld := by
    have h := hWlmK
    simp only [WScoped] at h
    exact h.1
  exact ⟨⟨hWld.1, hbld.1, hLld, hFld, hAld, hIld⟩, hWldK⟩

/-- The spine-prefix kit every stage hands to the λ-side walk. -/
def SpineKit (cval : ConstVal V) (env : Env) (φ : Name → Nat)
    (D k : Nat) (ρ : Nat → V) (spine : List Expr) (xs : List V) : Prop :=
  FvarSpine D ρ (spine.take k) xs ∧
  (∀ a ∈ spine.take k, WScoped D a) ∧
  (∀ a ∈ spine.take k, FvarsOk V cval env φ D ρ a) ∧
  (∀ a ∈ spine.take k, Expr.LeavesBounded a) ∧
  (∀ a ∈ spine.take k, WScoped k a)

/-- Stage package for the recursor-prefix region (`k < rP`): walk the
member type's telescope along the chosen values; the residual's head
binder is the stage annotation, packaged at the padded master frame. -/
theorem stage_pkg_pre {env₀ : Env} (m₀ : EnvModel V env₀)
    {ψ : Name → Nat} {tyA : Expr} {rP cnF : Nat}
    {fvsP : List Expr} {restP : Expr} {xFvsP : List Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∃ T, interpClosed V m₀.val env₀ ψ tyA = some T)
    {k : Nat} {xs : List V} {fv : Expr}
    (hk : k < rP) (hxs : xs.length = k)
    (hfv : (fvsP ++ xFvsP)[k]? = some fv)
    (hpref : FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs) :
    (InterpPkg m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) ∧
      WScoped k (Expr.fvarTypeD fv)) ∧
    SpineKit m₀.val env₀ ψ (rP + cnF) k
      (fun i => xs.getD i SetTheory.empty) (fvsP ++ xFvsP) xs := by
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  -- the spine prefix is inside the recursor prefix
  have hTkeq : (fvsP ++ xFvsP).take k = fvsP.take k := by
    rw [List.take_append_of_le_length (by omega)]
  -- fv is the k-th prefix variable, a fvar at index k
  have hfvP : fvsP[k]? = some fv := by
    rw [List.getElem?_append_left (by omega)] at hfv
    exact hfv
  obtain ⟨nmv, hfvShape⟩ := hfvsPShape k fv hfvP
  rw [Nat.zero_add] at hfvShape
  -- the padded value spine over the full prefix
  have hspFull : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP
      (xs ++ List.replicate (rP - k) SetTheory.empty) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_append, List.length_replicate, hxs]; omega)
      (by omega) ?_
    intro j v hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge j k with hj | hj
    · rw [List.getElem?_append_left (by omega)] at hjv
      rw [hjv]
      rfl
    · rw [List.getElem?_append_right (by omega), hxs,
        List.getElem?_replicate] at hjv
      split at hjv
      · rw [List.getElem?_eq_none (by omega)]
        exact Option.some.inj hjv
      · exact nomatch hjv
  have hspTk : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvsP.take k) xs := by
    have h := FvarSpine.take k hspFull
    rw [List.take_append_of_le_length (by omega)] at h
    rwa [List.take_of_length_le (l := xs) (by omega)] at h
  -- entry facts on the prefix
  have hwsTk : ∀ a ∈ fvsP.take k, WScoped (rP + cnF) a := by
    intro a ha
    exact ((hfvsPWf a (List.mem_of_mem_take ha)).1).mono (by omega)
  have hLsTk : ∀ a ∈ fvsP.take k, Expr.LeavesBounded a := fun a ha =>
    (hfvsPWf a (List.mem_of_mem_take ha)).2.2
  have hwsKTk : ∀ a ∈ fvsP.take k, WScoped k a := by
    intro a ha
    obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
    have hjlen : j < (fvsP.take k).length := by
      rcases Nat.lt_or_ge j (fvsP.take k).length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hja
        exact nomatch hja
    have hjk : j < k := by
      rw [List.length_take] at hjlen
      omega
    have hja' : fvsP[j]? = some a := by
      rw [List.getElem?_take_of_lt hjk] at hja
      exact hja
    obtain ⟨nm, hshape⟩ := hfvsPShape j a hja'
    rw [Nat.zero_add] at hshape
    have hW := (hfvsPWf a (List.mem_of_mem_take ha)).1
    rw [hshape] at hW ⊢
    simp only [WScoped] at hW ⊢
    exact ⟨hjk, hW.2⟩
  -- the pointwise membership pack at the padded master frame
  have hmem : ∀ (i : Nat) (a : Expr) (v : V),
      ((fvsP.take k).map Expr.fvarTypeD)[i]? = some a →
      xs[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hik : i < k := by
      rcases Nat.lt_or_ge i k with h | h
      · exact h
      · rw [List.getElem?_eq_none (by omega)] at hv
        exact nomatch hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, List.getElem?_take_of_lt hik, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  -- split the member-type walk at the prefix
  have hfvsPInst' : Expr.instPisAt (fvsP.take k ++ fvsP.drop k) tyA =
      some (fvsP.map Expr.fvarTypeD, restP) := by
    rw [List.take_append_drop]
    exact hfvsPInst
  obtain ⟨ds₁, midS, ds₂, hopS1, hopS2, hdsSplit⟩ :=
    instPisAt_append (fvsP.take k) (fvsP.drop k) hfvsPInst'
  have hds₁len : ds₁.length = k := by
    rw [instPisAt_length _ hopS1, List.length_take]
    omega
  have hds₁ : ds₁ = (fvsP.take k).map Expr.fvarTypeD := by
    have h := congrArg (List.take k) hdsSplit
    rw [List.take_append_of_le_length (by omega)] at h
    rw [List.take_of_length_le (l := ds₁) (by omega)] at h
    rw [List.map_take]
    exact h.symm
  subst hds₁
  -- walk the prefix (fit + spine typing packages + residual facts)
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hLty : Expr.LeavesBounded tyA :=
    Expr.LeavesBounded.of_not_hasFvar htyw
  have hFty : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    FvarsOk.of_not_hasFvar htyw
  have hAty' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    AnnotOk.closed_invariant htyw _ _ hAty
  have hIty' : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA = some T := by
    obtain ⟨T, hT⟩ := hIty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant htyw _ _]
    exact hT
  obtain ⟨hfitTk, hΘTk⟩ := self_walk hopS1 hspTk hwsTk hWty htyb hLty
    hFty hAty' hmem
  obtain ⟨-, hPmid⟩ := peel_walk hopS1 hspTk hwsTk hWty hAty' hIty' hmem
  obtain ⟨Pmid, hPmid⟩ := hPmid
  obtain ⟨hWmid, hbmid, hAmid, hlmid⟩ :=
    TeleFitI.rest_wf hfitTk hWty htyb hAty'
  have hFmid : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midS := by
    intro l hl
    rcases hlmid l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar htyw] at hl'
      cases hl'
    · exact hΘTk a ha l hla
  have hLmid : Expr.LeavesBounded midS := by
    intro l hl
    rcases hlmid l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar htyw] at hl'
      cases hl'
    · exact hLsTk a ha l hla
  -- residual-scoping at the stage frame
  obtain ⟨-, hWmidK⟩ := instPisAt_wscoped (D := k) (fvsP.take k) hopS1
    (WScoped.of_not_hasFvar htyw) hwsKTk
  -- invert the head binder
  have hdropC : fvsP.drop k = fv :: fvsP.drop (k + 1) := by
    have h := List.drop_eq_getElem_cons (l := fvsP) (i := k) (by omega)
    rw [h]
    congr 1
    have := List.getElem?_eq_getElem (l := fvsP) (i := k) (by omega)
    rw [hfvP] at this
    exact (Option.some.inj this).symm
  rw [hdropC] at hopS2
  obtain ⟨nH, domH, bodyH, mH, ds₂', rfl, hds₂c, -⟩ :=
    instPisAt_cons_inv hopS2
  have hdomH : domH = Expr.fvarTypeD fv := by
    have h0 : (fvsP.map Expr.fvarTypeD)[k]? = some domH := by
      rw [hdsSplit, List.getElem?_append_right
        (by rw [List.length_map, List.length_take]; omega)]
      rw [List.length_map, List.length_take,
        show k - min k fvsP.length = 0 from by omega, hds₂c]
      rfl
    rw [List.getElem?_map, hfvP] at h0
    exact (Option.some.inj h0).symm
  replace hdomH : Expr.fvarTypeD fv = domH := hdomH.symm
  subst hdomH
  -- extract the stage annotation's package
  have hAmid' := hAmid
  simp only [AnnotOk] at hAmid'
  obtain ⟨hAdom, ⟨cod, hcod⟩, -⟩ := hAmid'
  have hWdom : WScoped (rP + cnF) (Expr.fvarTypeD fv) ∧
      WScoped (rP + cnF) bodyH := by
    simpa [WScoped] using hWmid
  have hbdom : (Expr.fvarTypeD fv).looseBVarsBounded 0 = true ∧
      bodyH.looseBVarsBounded 1 = true := by
    revert hbmid; simp [Expr.looseBVarsBounded]
  have hLdom : Expr.LeavesBounded (Expr.fvarTypeD fv) :=
    LeavesBounded.of_forallE_ty hLmid
  have hFdom : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) :=
    FvarsOk.of_subset (fun l hl => by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFmid
  have hIdom : ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) =
        some B := by
    revert hPmid
    simp only [interpExpr, hcod]
    cases hB0 : interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) with
    | none => intro h; exact nomatch h
    | some B => intro _; exact ⟨B, rfl⟩
  have hWdomK : WScoped k (Expr.fvarTypeD fv) := by
    have hW := (hfvsPWf fv (List.mem_of_getElem? hfvP)).1
    rw [hfvShape] at hW
    simp only [WScoped] at hW
    rw [hfvShape]
    exact hW.2
  refine ⟨⟨⟨hWdom.1, hbdom.1, hLdom, hFdom, hAdom, hIdom⟩, hWdomK⟩,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hTkeq]; exact hspTk
  · rw [hTkeq]; exact hwsTk
  · rw [hTkeq]; exact hΘTk
  · rw [hTkeq]; exact hLsTk
  · rw [hTkeq]; exact hwsKTk

/-- Stage package for the constructor-field region (`rP ≤ k`): walk
the member type over the full recursor prefix, obtain the (plain- or
nested-specific) constructor-residual package, and walk it along the
chosen field values; the residual's head binder is the stage
annotation. -/
theorem stage_pkg_fld {env₀ : Env} (m₀ : EnvModel V env₀)
    {ψ : Name → Nat} {tyA : Expr} {rP cnF : Nat}
    {fvsP : List Expr} {restP : Expr} {crestP : Expr}
    {xFvsP : List Expr} {crest2 : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    {k : Nat} {xs : List V} {fv : Expr}
    (hctorPkg :
      WScoped rP crestP ∧ crestP.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded crestP ∧
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      ∃ P, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP = some P)
    (hkl : rP ≤ k) (hk : k < rP + cnF) (hxs : xs.length = k)
    (hfv : (fvsP ++ xFvsP)[k]? = some fv)
    (hpref : FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs) :
    (InterpPkg m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) ∧
      WScoped k (Expr.fvarTypeD fv)) ∧
    SpineKit m₀.val env₀ ψ (rP + cnF) k
      (fun i => xs.getD i SetTheory.empty) (fvsP ++ xFvsP) xs := by
  obtain ⟨hWcr, hbcr, hLcr, hFcr, hAcr, Pcr, hPcr⟩ := hctorPkg
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec cnF rP hopenX
  obtain ⟨hxWf, hcrest2Wf⟩ := openPisAtFvars_wf cnF rP hopenX hWcr hbcr
    hLcr
  obtain ⟨t, hktr⟩ : ∃ t, k = rP + t := ⟨k - rP, by omega⟩
  have ht : t < cnF := by omega
  -- the k-th spine entry is the t-th field variable
  have hfvX : xFvsP[t]? = some fv := by
    rw [List.getElem?_append_right (by omega), hfvsPLen,
      show k - rP = t from by omega] at hfv
    exact hfv
  obtain ⟨nmv, hfvShape⟩ := hxShape t fv hfvX
  -- the full recursor-prefix spine
  have hspP : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (xs.take rP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < rP := by
      rcases Nat.lt_or_ge j rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (rP + cnF) a := fun a ha =>
    ((hfvsPWf a ha).1).mono (by omega)
  -- the membership pack over the full recursor prefix
  have hmemP : ∀ (i : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.take rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hir : i < rP := by
      rcases Nat.lt_or_ge i rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hir] at hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  -- tyA's closed facts at the frame
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hLty : Expr.LeavesBounded tyA :=
    Expr.LeavesBounded.of_not_hasFvar htyw
  have hFty : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    FvarsOk.of_not_hasFvar htyw
  have hAty' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    AnnotOk.closed_invariant htyw _ _ hAty
  obtain ⟨-, hΘP⟩ := self_walk hfvsPInst hspP hwsP hWty htyb hLty hFty
    hAty' hmemP
  -- the field-prefix spine
  have hspXFull : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) xFvsP
      (xs.drop rP ++ List.replicate (cnF - t) SetTheory.empty) := by
    refine FvarSpine_of_open hopenX
      (by rw [List.length_append, List.length_drop,
        List.length_replicate]; omega) (by omega) ?_
    intro j v hjv
    show xs.getD (rP + j) SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge j t with hj | hj
    · rw [List.getElem?_append_left
        (by rw [List.length_drop]; omega), List.getElem?_drop] at hjv
      rw [hjv]
      rfl
    · rw [List.getElem?_append_right
        (by rw [List.length_drop]; omega), List.length_drop,
        List.getElem?_replicate] at hjv
      split at hjv
      · rw [List.getElem?_eq_none (by omega)]
        exact Option.some.inj hjv
      · exact nomatch hjv
  have hspXt : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (xFvsP.take t)
      (xs.drop rP) := by
    have h := FvarSpine.take t hspXFull
    rw [List.take_append_of_le_length
      (by rw [List.length_drop]; omega)] at h
    rwa [List.take_of_length_le (l := xs.drop rP)
      (by rw [List.length_drop]; omega)] at h
  have hwsXt : ∀ a ∈ xFvsP.take t, WScoped (rP + cnF) a := fun a ha =>
    (hxWf a (List.mem_of_mem_take ha)).1
  have hLsXt : ∀ a ∈ xFvsP.take t, Expr.LeavesBounded a := fun a ha =>
    (hxWf a (List.mem_of_mem_take ha)).2.2
  -- the membership pack over the field prefix
  have hmemX : ∀ (i : Nat) (a : Expr) (v : V),
      ((xFvsP.take t).map Expr.fvarTypeD)[i]? = some a →
      (xs.drop rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hit : i < t := by
      rcases Nat.lt_or_ge i t with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_drop]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_drop] at hv
    have hix : i < xFvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, xFvsP[i]? = some fvi :=
      ⟨xFvsP[i]'hix, List.getElem?_eq_getElem hix⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, List.getElem?_take_of_lt hit, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[rP + i]? = some fvi := by
      rw [List.getElem?_append_right (by omega), hfvsPLen,
        show rP + i - rP = i from by omega]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref (rP + i) v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hxShape i fvi hfvi
    have hWi : WScoped (rP + i) (Expr.fvarTypeD fvi) := by
      have hW := (hxWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  -- split the constructor-residual walk at the field prefix
  have hxInst' : Expr.instPisAt (xFvsP.take t ++ xFvsP.drop t) crestP =
      some (xFvsP.map Expr.fvarTypeD, crest2) := by
    rw [List.take_append_drop]
    exact hxInst
  obtain ⟨ds₁, midX, ds₂, hopX1, hopX2, hdsSplit⟩ :=
    instPisAt_append (xFvsP.take t) (xFvsP.drop t) hxInst'
  have hds₁len : ds₁.length = t := by
    rw [instPisAt_length _ hopX1, List.length_take]
    omega
  have hds₁ : ds₁ = (xFvsP.take t).map Expr.fvarTypeD := by
    have h := congrArg (List.take t) hdsSplit
    rw [List.take_append_of_le_length (by omega)] at h
    rw [List.take_of_length_le (l := ds₁) (by omega)] at h
    rw [List.map_take]
    exact h.symm
  subst hds₁
  have hWcrD : WScoped (rP + cnF) crestP := hWcr.mono (by omega)
  obtain ⟨hfitX, hΘX⟩ := self_walk hopX1 hspXt hwsXt hWcrD hbcr hLcr
    hFcr hAcr hmemX
  obtain ⟨-, hPmidX⟩ := peel_walk hopX1 hspXt hwsXt hWcrD hAcr
    ⟨Pcr, hPcr⟩ hmemX
  obtain ⟨PmidX, hPmidX⟩ := hPmidX
  obtain ⟨hWmidX, hbmidX, hAmidX, hlmidX⟩ :=
    TeleFitI.rest_wf hfitX hWcrD hbcr hAcr
  have hFmidX : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midX := by
    intro l hl
    rcases hlmidX l hl with hl' | ⟨a, ha, hla⟩
    · exact hFcr l hl'
    · exact hΘX a ha l hla
  have hLmidX : Expr.LeavesBounded midX := by
    intro l hl
    rcases hlmidX l hl with hl' | ⟨a, ha, hla⟩
    · exact hLcr l hl'
    · exact hLsXt a ha l hla
  -- invert the head binder
  have hdropC : xFvsP.drop t = fv :: xFvsP.drop (t + 1) := by
    have h := List.drop_eq_getElem_cons (l := xFvsP) (i := t)
      (by omega)
    rw [h]
    congr 1
    have := List.getElem?_eq_getElem (l := xFvsP) (i := t) (by omega)
    rw [hfvX] at this
    exact (Option.some.inj this).symm
  rw [hdropC] at hopX2
  obtain ⟨nH, domH, bodyH, mH, ds₂', rfl, hds₂c, -⟩ :=
    instPisAt_cons_inv hopX2
  have hdomH : domH = Expr.fvarTypeD fv := by
    have h0 : (xFvsP.map Expr.fvarTypeD)[t]? = some domH := by
      rw [hdsSplit, List.getElem?_append_right
        (by rw [List.length_map, List.length_take]; omega)]
      rw [List.length_map, List.length_take,
        show t - min t xFvsP.length = 0 from by omega, hds₂c]
      rfl
    rw [List.getElem?_map, hfvX] at h0
    exact (Option.some.inj h0).symm
  replace hdomH : Expr.fvarTypeD fv = domH := hdomH.symm
  subst hdomH
  -- extract the stage annotation's package
  have hAmidX' := hAmidX
  simp only [AnnotOk] at hAmidX'
  obtain ⟨hAdom, ⟨cod, hcod⟩, -⟩ := hAmidX'
  have hWdom : WScoped (rP + cnF) (Expr.fvarTypeD fv) ∧
      WScoped (rP + cnF) bodyH := by
    simpa [WScoped] using hWmidX
  have hbdom : (Expr.fvarTypeD fv).looseBVarsBounded 0 = true ∧
      bodyH.looseBVarsBounded 1 = true := by
    revert hbmidX; simp [Expr.looseBVarsBounded]
  have hLdom : Expr.LeavesBounded (Expr.fvarTypeD fv) :=
    LeavesBounded.of_forallE_ty hLmidX
  have hFdom : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) :=
    FvarsOk.of_subset (fun l hl => by
      simp only [fvarLeaves, List.mem_append]; exact Or.inl hl) hFmidX
  have hIdom : ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) =
        some B := by
    revert hPmidX
    simp only [interpExpr, hcod]
    cases hB0 : interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) with
    | none => intro h; exact nomatch h
    | some B => intro _; exact ⟨B, rfl⟩
  have hWdomK : WScoped k (Expr.fvarTypeD fv) := by
    have hW := (hxWf fv (List.mem_of_getElem? hfvX)).1
    rw [hfvShape] at hW
    simp only [WScoped] at hW
    rw [hfvShape, hktr]
    exact hW.2
  -- assemble the spine kit at the full stage prefix
  have hTkeq : (fvsP ++ xFvsP).take k = fvsP ++ xFvsP.take t := by
    rw [show k = fvsP.length + t from by omega,
      List.take_length_add_append]
  have hspTk : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) ((fvsP ++ xFvsP).take k)
      xs := by
    rw [hTkeq]
    have h := FvarSpine.append hspP hspXt
    rwa [List.take_append_drop] at h
  refine ⟨⟨⟨hWdom.1, hbdom.1, hLdom, hFdom, hAdom, hIdom⟩, hWdomK⟩,
    hspTk, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hTkeq] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hwsP a ha
    · exact hwsXt a ha
  · intro a ha
    rw [hTkeq] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hΘP a ha
    · exact hΘX a ha
  · intro a ha
    rw [hTkeq] at ha
    rcases List.mem_append.mp ha with ha | ha
    · exact (hfvsPWf a ha).2.2
    · exact hLsXt a ha
  · intro a ha
    rw [hTkeq] at ha
    rcases List.mem_append.mp ha with ha | ha
    · -- a recursor-prefix variable, index below rP ≤ k
      obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      have hjlen : j < fvsP.length := by
        rcases Nat.lt_or_ge j fvsP.length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hja
          exact nomatch hja
      obtain ⟨nm, hshape⟩ := hfvsPShape j a hja
      rw [Nat.zero_add] at hshape
      have hW := (hfvsPWf a ha).1
      rw [hshape] at hW ⊢
      simp only [WScoped] at hW ⊢
      exact ⟨by omega, hW.2⟩
    · -- a field variable below the stage
      obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      have hjlen : j < (xFvsP.take t).length := by
        rcases Nat.lt_or_ge j (xFvsP.take t).length with h | h
        · exact h
        · rw [List.getElem?_eq_none h] at hja
          exact nomatch hja
      have hjt : j < t := by
        rw [List.length_take] at hjlen
        omega
      have hja' : xFvsP[j]? = some a := by
        rw [List.getElem?_take_of_lt hjt] at hja
        exact hja
      obtain ⟨nm, hshape⟩ := hxShape j a hja'
      have hW := (hxWf a (List.mem_of_mem_take ha)).1
      rw [hshape] at hW ⊢
      simp only [WScoped] at hW ⊢
      exact ⟨by omega, hW.2⟩

/-- The flat stage facts (`Hty` of `TowerOk.of_stages`) of a modeled
recursor rule: at every stage, the frame annotation and (anything
erased-equal to) the rule tower's instantiated binder domain interpret
to the same set, the annotation is truthful, and members extend the
frame-membership invariant. -/
theorem modeled_stage {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {tyA : Expr} {rP cnF : Nat}
    {fvsP : List Expr} {restP : Expr} {crestP : Expr}
    {xFvsP : List Expr} {crest2 : Expr}
    {rhsA lrest : Expr} {ldoms : List Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∃ T, interpClosed V m₀.val env₀ ψ tyA = some T)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    (hctorPkg : ∀ (xs : List V), xs.length ≤ rP + cnF →
      rP ≤ xs.length →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      WScoped rP crestP ∧ crestP.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded crestP ∧
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      ∃ P, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP = some P)
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA =
      some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∃ L, interpClosed V m₀.val env₀ ψ rhsA = some L) :
    ∀ (k : Nat) (xs : List V) (fv ld : Expr), xs.length = k →
      (fvsP ++ xFvsP)[k]? = some fv → ldoms[k]? = some ld →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      ∃ A, interpExpr V m₀.val env₀ ψ k
          (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) =
            some A ∧
        (∀ e, Expr.ErasedEq e ld → interpExpr V m₀.val env₀ ψ k
          (fun i => xs.getD i SetTheory.empty) e = some A) ∧
        AnnotOk V m₀.val env₀ ψ k
          (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) ∧
        ∀ x, x ∈ˢ A →
          FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) (xs ++ [x]) := by
  intro k xs fv ld hxs hfv hld hpref
  have hfvsPLen : fvsP.length = rP :=
    (openPisAtFvars_spec rP 0 hopenP).2.1
  have hxLen : xFvsP.length = cnF :=
    (openPisAtFvars_spec cnF rP hopenX).2.1
  have hspineLen : (fvsP ++ xFvsP).length = rP + cnF := by
    rw [List.length_append, hfvsPLen, hxLen]
  have hkD : k < rP + cnF := by
    have h1 : k < ldoms.length := by
      rcases Nat.lt_or_ge k ldoms.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hld
        exact nomatch hld
    rw [instLamsAt_length _ hlinst, hspineLen] at h1
    exact h1
  -- the annotation package + spine kit, by region
  have hpkg : (InterpPkg m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) (Expr.fvarTypeD fv) ∧
      WScoped k (Expr.fvarTypeD fv)) ∧
      SpineKit m₀.val env₀ ψ (rP + cnF) k
        (fun i => xs.getD i SetTheory.empty) (fvsP ++ xFvsP) xs := by
    rcases Nat.lt_or_ge k rP with hk | hk
    · exact stage_pkg_pre m₀ hopenP htyw htyb hAty hIty hk hxs hfv
        hpref
    · exact stage_pkg_fld m₀ hopenP htyw htyb hAty hopenX
        (hctorPkg xs (by omega) (by omega) hpref) hk hkD hxs hfv hpref
  obtain ⟨⟨hpkgA, hWkA⟩, hsp, hws, hΘ, hLs, hwsK⟩ := hpkg
  -- the λ-side package
  obtain ⟨hpkgB, hWkB⟩ := stage_pkg_lam m₀ F hlinst hdeLam
    (by omega) hld hsp hws hΘ hLs hwsK hrhsw hrhsb hArhs hIrhs
  -- the stage defeq
  have hde : isDefEqCore env₀ F (rP + cnF) (Expr.fvarTypeD fv) ld =
      .ok true := by
    refine DefEqListOk.pointwise hdeLam k ?_ hld
    rw [List.getElem?_map, hfv]
    rfl
  obtain ⟨A, h1, h2, h3⟩ := stage_out m₀ F hxs (by omega) hde hpkgA
    hpkgB hWkA hWkB
  refine ⟨A, h1, h2, h3, ?_⟩
  -- extending the membership invariant
  intro x hx j v fv' hjv hjfv
  rcases Nat.lt_trichotomy j k with hj | hj | hj
  · rw [List.getElem?_append_left (by omega)] at hjv
    obtain ⟨B, hB, hvB⟩ := hpref j v fv' hjv hjfv
    refine ⟨B, ?_, hvB⟩
    rwa [List.take_append_of_le_length (by omega)]
  · subst hj
    rw [List.getElem?_append_right (by omega), hxs, Nat.sub_self] at hjv
    obtain rfl : x = v := Option.some.inj hjv
    have hfv' : fv' = fv := by
      rw [hfv] at hjfv
      exact (Option.some.inj hjfv.symm)
    subst hfv'
    refine ⟨A, ?_, hx⟩
    rw [List.take_append_of_le_length (by omega),
      List.take_of_length_le (by omega)]
    exact h1
  · have hlen : (xs ++ [x]).length ≤ j := by
      simp only [List.length_append, List.length_cons,
        List.length_nil, hxs]
      omega
    rw [List.getElem?_eq_none hlen] at hjv
    exact nomatch hjv

/-- The constructor-residual package of a **plain** rule: the
constructor type is walked at the leading recursor parameters, whose
memberships transfer into the walk's domains along the kernel's
parameter-domain pins (`pi_walk_src` over `hdePars`). -/
theorem ctor_pkg_plain {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat)
    {ψ : Name → Nat} {tyA : Expr} {rP cnP cnF : Nat} {cty : Expr}
    {fvsP : List Expr} {restP : Expr} {cdomsP : List Expr}
    {crestP : Expr} {xFvsP : List Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cty =
      some (cdomsP, crestP))
    (hdePars : DefEqListOk F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    (hplainLe : cnP ≤ rP)
    (hCw : cty.hasFvar = false)
    (hCb : cty.looseBVarsBounded 0 = true)
    (hACty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cty)
    (hICty : ∃ T, interpClosed V m₀.val env₀ ψ cty = some T) :
    ∀ (xs : List V), xs.length ≤ rP + cnF → rP ≤ xs.length →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      WScoped rP crestP ∧ crestP.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded crestP ∧
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP ∧
      ∃ P, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) crestP = some P := by
  intro xs hlen hge hpref
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  -- the full recursor-prefix spine and its typing packages
  have hspP : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (xs.take rP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < rP := by
      rcases Nat.lt_or_ge j rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (rP + cnF) a := fun a ha =>
    ((hfvsPWf a ha).1).mono (by omega)
  have hmemP : ∀ (i : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.take rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hir : i < rP := by
      rcases Nat.lt_or_ge i rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hir] at hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hΘP := (self_walk hfvsPInst hspP hwsP hWty htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw)
    (AnnotOk.closed_invariant htyw _ _ hAty) hmemP).2
  -- restrict to the constructor parameters
  have hspC : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvsP.take cnP)
      (xs.take cnP) := by
    have h := FvarSpine.take cnP hspP
    rwa [List.take_take, Nat.min_eq_left hplainLe] at h
  have hwsC : ∀ a ∈ fvsP.take cnP, WScoped (rP + cnF) a := fun a ha =>
    hwsP a (List.mem_of_mem_take ha)
  have hLsC : ∀ a ∈ fvsP.take cnP, Expr.LeavesBounded a := fun a ha =>
    (hfvsPWf a (List.mem_of_mem_take ha)).2.2
  have hFsC : ∀ a ∈ fvsP.take cnP,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := fun a ha =>
    hΘP a (List.mem_of_mem_take ha)
  -- the constructor type's closed facts at the frame
  have hWc : WScoped (rP + cnF) cty := WScoped.of_not_hasFvar hCw
  have hAc : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty :=
    AnnotOk.closed_invariant hCw _ _ hACty
  have hIc : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cty = some T := by
    obtain ⟨T, hT⟩ := hICty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant hCw _ _]
    exact hT
  -- walk the parameters, transferring along the parameter-domain pins
  obtain ⟨hfitC, hpackC⟩ := pi_walk_src m₀ F hcinstP hdePars hspC hwsC
    hLsC hFsC hWc hCb (Expr.LeavesBounded.of_not_hasFvar hCw)
    (FvarsOk.of_not_hasFvar hCw) hAc hIc
  obtain ⟨-, hPcr⟩ := peel_walk hcinstP hspC hwsC hWc hAc hIc hpackC
  obtain ⟨Pcr, hPcr⟩ := hPcr
  obtain ⟨hWcrD, hbcr, hAcr, hlcr⟩ := TeleFitI.rest_wf hfitC hWc hCb hAc
  -- residual scoping at the recursor prefix
  have hwsCrP : ∀ a ∈ fvsP.take cnP, WScoped rP a := by
    intro a ha
    have h := (hfvsPWf a (List.mem_of_mem_take ha)).1
    rwa [Nat.zero_add] at h
  obtain ⟨-, hWcr⟩ := instPisAt_wscoped (D := rP) (fvsP.take cnP)
    hcinstP (WScoped.of_not_hasFvar hCw) hwsCrP
  refine ⟨hWcr, hbcr, ?_, ?_, hAcr, ⟨Pcr, hPcr⟩⟩
  · intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hLsC a ha l hla
  · intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hFsC a ha l hla

set_option maxHeartbeats 3200000 in
/-- The bottom fact (`Hbot` of `TowerOk.of_stages`) of a **plain**
modeled rule: over any full frame-fitting value list, the canonical
iota left-hand side body (the recursor applied to the prefix
variables, the constructor residual's indices and the applied
constructor) and the rule right-hand side's instantiated body
interpret to the same value, and the body's annotations are truthful.
Derived by eliminating the checked `_model.iota_j` theorem's
inhabitant into the interpreted equation at the master frame. -/
theorem modeled_bottom_plain
    {env₀ : Env} (m₀ : EnvModel V env₀) (F : Nat) {ψ : Name → Nat}
    {f : Name → Name}
    (hro : RenameOk m₀.val env₀ f)
    (hcvp : ConstValParams m₀.val env₀)
    -- the recursor, its public entry and its model
    {R : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    {ciR cim : ConstantInfo}
    (hfR : env₀.find? R = some ciR)
    (hRlps : ciR.toConstantVal.levelParams = lps)
    (hfRm : env₀.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    -- the constructor and its model
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    {cimC : ConstantInfo}
    (hfCm : env₀.find? (f ctor) = some cimC)
    (hCmlps : cimC.toConstantVal.levelParams = cvj.levelParams)
    {ciC : ConstantInfo}
    (hfC : env₀.find? ctor = some ciC)
    (hClps : ciC.toConstantVal.levelParams = cvj.levelParams)
    -- the pinned equality former
    (heqfind : env₀.find? eqName = some eqA)
    (heqval : ∀ ψ'' : Name → Nat, m₀.val eqName ψ'' = eqVal V ψ'')
    -- the iota theorem's semantic facts
    {cvt : ConstantVal} {thmName : Name}
    (hthm_mem : ∀ ψ'' : Name → Nat, ∃ P,
      interpClosed V m₀.val env₀ ψ'' cvt.type = some P ∧
      m₀.val thmName ψ'' ∈ˢ P)
    (hthm_annot : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvt.type)
    (hSw : cvt.type.hasFvar = false)
    (hSb : cvt.type.looseBVarsBounded 0 = true)
    -- kernel kit (theorem side)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    {cdoms : List Expr} {cres : Expr} {rdoms : List Expr} {rrest : Expr}
    (htyStrip : (tyA.stripPis mI).isSome = true)
    (hrPmI : rP ≤ mI)
    (hplainLe : cnP ≤ rP)
    (hopen : openPisAtFvars (rP + cnF) cvt.type 0 = some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f R) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = mI + 1)
    (hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    (hCstripSome : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvj.type.renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + (mI - rP))
    (hdeIdx : DefEqListOk F env₀ (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (hrinst : Expr.instPisAt (fvs.take rP)
      (tyA.renameConsts f) = some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (hdeFld : DefEqListOk F env₀ (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    -- kernel kit (public side)
    {rhsA : Expr} {fvsP : List Expr} {restP : Expr}
    {cdomsP : List Expr} {crestP : Expr} {xFvsP : List Expr}
    {crest2 : Expr} {ldoms : List Expr} {lrest : Expr}
    (hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hdePars : DefEqListOk F env₀ (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    (hopenX : openPisAtFvars cnF crestP rP = some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hdeRhs : isDefEqCore env₀ F (rP + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    -- the rule right-hand side's facts
    (hrhsw : rhsA.hasFvar = false)
    (hrhsb : rhsA.looseBVarsBounded 0 = true)
    (hArhs : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) rhsA)
    (hIrhs : ∃ L, interpClosed V m₀.val env₀ ψ rhsA = some L)
    -- member and constructor type wf
    (htyw : tyA.hasFvar = false)
    (htyb : tyA.looseBVarsBounded 0 = true)
    (hAty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) tyA)
    (hIty : ∃ T, interpClosed V m₀.val env₀ ψ tyA = some T)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hACty : AnnotOk V m₀.val env₀ ψ 0 (rho0 V) cvj.type)
    (hICty : ∃ T, interpClosed V m₀.val env₀ ψ cvj.type = some T) :
    ∀ (xs : List V), xs.length = rP + cnF →
      FramePref m₀.val env₀ ψ (fvsP ++ xFvsP) xs →
      (∃ w, interpExpr V m₀.val env₀ ψ (rP + cnF)
          (fun i => xs.getD i SetTheory.empty)
          (Expr.mkAppN (.const R (lps.map .param))
            (fvsP ++ crest2.getAppArgs.drop cnP ++
              [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
                (fvsP.take cnP ++ xFvsP)])) = some w ∧
        ∀ e, Expr.ErasedEq e lrest →
          interpExpr V m₀.val env₀ ψ (rP + cnF)
            (fun i => xs.getD i SetTheory.empty) e = some w) ∧
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN (.const R (lps.map .param))
          (fvsP ++ crest2.getAppArgs.drop cnP ++
            [Expr.mkAppN (.const ctor (cvj.levelParams.map .param))
              (fvsP.take cnP ++ xFvsP)])) := by
  intro xs hxs hpref
  -- ===== S0: the theorem-side master frame =====
  obtain ⟨hfvsInst, hfvsLen, hfvsShape⟩ :=
    openPisAtFvars_spec (rP + cnF) 0 hopen
  obtain ⟨hfvsWf, htbodyWf⟩ := openPisAtFvars_wf (rP + cnF) 0 hopen
    (WScoped.of_not_hasFvar hSw) hSb
    (Expr.LeavesBounded.of_not_hasFvar hSw)
  have hfvsW : ∀ a ∈ fvs, WScoped (rP + cnF) a := by
    intro a ha
    have := (hfvsWf a ha).1
    simpa using this
  have hfvsShapes : ∀ a ∈ fvs, ∃ i n t, a = .fvar i n t := by
    intro a ha
    obtain ⟨k, hk⟩ := List.getElem?_of_mem ha
    obtain ⟨nm', ha'⟩ := hfvsShape k a hk
    exact ⟨0 + k, nm', _, ha'⟩
  have hspW : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvs xs := by
    refine FvarSpine_of_open hopen hxs (by omega) ?_
    intro k v hkv
    show xs.getD (0 + k) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hkv]
    rfl
  have hspWpre := FvarSpine.take rP hspW
  have hspWdrop := FvarSpine.drop rP hspW
  have hspWctorPre : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvs.take cnP)
      (xs.take cnP) := by
    have h := FvarSpine.take cnP hspW
    exact h
  have hspWctor := FvarSpine.append hspWctorPre hspWdrop
  have hfvsPreLen : (fvs.take rP).length = rP := by
    rw [List.length_take, hfvsLen]; omega
  have hfvsCLen : (fvs.take cnP ++ fvs.drop rP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, List.length_drop,
      hfvsLen]
    omega
  -- ===== S0': the public frame and its walks =====
  obtain ⟨hfvsPInst, hfvsPLen, hfvsPShape⟩ :=
    openPisAtFvars_spec rP 0 hopenP
  obtain ⟨hfvsPWf, hrestPWf⟩ := openPisAtFvars_wf rP 0 hopenP
    (WScoped.of_not_hasFvar htyw) htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
  have hspP : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) fvsP (xs.take rP) := by
    refine FvarSpine_of_open hopenP
      (by rw [List.length_take]; omega) (by omega) ?_
    intro j v hjv
    have hjr : j < rP := by
      rcases Nat.lt_or_ge j rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hjv
        exact nomatch hjv
    rw [List.getElem?_take_of_lt hjr] at hjv
    show xs.getD (0 + j) SetTheory.empty = v
    rw [Nat.zero_add, List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsP : ∀ a ∈ fvsP, WScoped (rP + cnF) a := fun a ha =>
    ((hfvsPWf a ha).1).mono (by omega)
  have hmemP : ∀ (i : Nat) (a : Expr) (v : V),
      (fvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.take rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hir : i < rP := by
      rcases Nat.lt_or_ge i rP with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_take]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_take_of_lt hir] at hv
    have hifv : i < fvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, fvsP[i]? = some fvi :=
      ⟨fvsP[i]'hifv, List.getElem?_eq_getElem hifv⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[i]? = some fvi := by
      rw [List.getElem?_append_left (by omega)]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref i v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hfvsPShape i fvi hfvi
    rw [Nat.zero_add] at hshapei
    have hWi : WScoped i (Expr.fvarTypeD fvi) := by
      have hW := (hfvsPWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWty : WScoped (rP + cnF) tyA := WScoped.of_not_hasFvar htyw
  have hAty' : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tyA :=
    AnnotOk.closed_invariant htyw _ _ hAty
  obtain ⟨hfitP, hΘP⟩ := self_walk hfvsPInst hspP hwsP hWty htyb
    (Expr.LeavesBounded.of_not_hasFvar htyw)
    (FvarsOk.of_not_hasFvar htyw) hAty' hmemP
  -- the public constructor walk (parameters via the kernel pins)
  have hspC : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvsP.take cnP)
      (xs.take cnP) := by
    have h := FvarSpine.take cnP hspP
    rwa [List.take_take, Nat.min_eq_left hplainLe] at h
  have hwsC : ∀ a ∈ fvsP.take cnP, WScoped (rP + cnF) a := fun a ha =>
    hwsP a (List.mem_of_mem_take ha)
  have hLsC : ∀ a ∈ fvsP.take cnP, Expr.LeavesBounded a := fun a ha =>
    (hfvsPWf a (List.mem_of_mem_take ha)).2.2
  have hFsC : ∀ a ∈ fvsP.take cnP,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) a := fun a ha =>
    hΘP a (List.mem_of_mem_take ha)
  have hWc : WScoped (rP + cnF) cvj.type := WScoped.of_not_hasFvar hCw
  have hAc : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvj.type :=
    AnnotOk.closed_invariant hCw _ _ hACty
  have hIc : ∃ T, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvj.type = some T := by
    obtain ⟨T, hT⟩ := hICty
    refine ⟨T, ?_⟩
    rw [interp_closed_invariant hCw _ _]
    exact hT
  obtain ⟨hfitC, hpackC⟩ := pi_walk_src m₀ F hcinstP hdePars hspC hwsC
    hLsC hFsC hWc hCb (Expr.LeavesBounded.of_not_hasFvar hCw)
    (FvarsOk.of_not_hasFvar hCw) hAc hIc
  obtain ⟨-, hPcrEx⟩ := peel_walk hcinstP hspC hwsC hWc hAc hIc hpackC
  obtain ⟨Pcr, hPcr⟩ := hPcrEx
  obtain ⟨hWcrD, hbcr, hAcr, hlcr⟩ := TeleFitI.rest_wf hfitC hWc hCb hAc
  have hFcr : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) crestP := by
    intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hFsC a ha l hla
  have hLcr : Expr.LeavesBounded crestP := by
    intro l hl
    rcases hlcr l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · exact hLsC a ha l hla
  -- the public field walk
  obtain ⟨hxInst, hxLen, hxShape⟩ := openPisAtFvars_spec cnF rP hopenX
  have hwsCrP : ∀ a ∈ fvsP.take cnP, WScoped rP a := by
    intro a ha
    have h := (hfvsPWf a (List.mem_of_mem_take ha)).1
    rwa [Nat.zero_add] at h
  obtain ⟨-, hWcrRp⟩ := instPisAt_wscoped (D := rP) (fvsP.take cnP)
    hcinstP (WScoped.of_not_hasFvar hCw) hwsCrP
  obtain ⟨hxWf, hcrest2Wf⟩ := openPisAtFvars_wf cnF rP hopenX hWcrRp
    hbcr hLcr
  have hspX : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) xFvsP (xs.drop rP) := by
    refine FvarSpine_of_open hopenX
      (by rw [List.length_drop]; omega) (by omega) ?_
    intro j v hjv
    rw [List.getElem?_drop] at hjv
    show xs.getD (rP + j) SetTheory.empty = v
    rw [List.getD_eq_getElem?_getD, hjv]
    rfl
  have hwsX : ∀ a ∈ xFvsP, WScoped (rP + cnF) a := fun a ha =>
    (hxWf a ha).1
  have hLsX : ∀ a ∈ xFvsP, Expr.LeavesBounded a := fun a ha =>
    (hxWf a ha).2.2
  have hmemX : ∀ (i : Nat) (a : Expr) (v : V),
      (xFvsP.map Expr.fvarTypeD)[i]? = some a →
      (xs.drop rP)[i]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro i a v ha hv
    have hit : i < cnF := by
      rcases Nat.lt_or_ge i cnF with h | h
      · exact h
      · rw [List.getElem?_eq_none
          (by rw [List.length_drop]; omega)] at hv
        exact nomatch hv
    rw [List.getElem?_drop] at hv
    have hix : i < xFvsP.length := by omega
    obtain ⟨fvi, hfvi⟩ : ∃ fvi, xFvsP[i]? = some fvi :=
      ⟨xFvsP[i]'hix, List.getElem?_eq_getElem hix⟩
    have ha' : a = Expr.fvarTypeD fvi := by
      rw [List.getElem?_map, hfvi] at ha
      exact (Option.some.inj ha).symm
    subst ha'
    have hsp : (fvsP ++ xFvsP)[rP + i]? = some fvi := by
      rw [List.getElem?_append_right (by omega), hfvsPLen,
        show rP + i - rP = i from by omega]
      exact hfvi
    obtain ⟨B, hB, hvB⟩ := hpref (rP + i) v fvi hv hsp
    obtain ⟨nmi, hshapei⟩ := hxShape i fvi hfvi
    have hWi : WScoped (rP + i) (Expr.fvarTypeD fvi) := by
      have hW := (hxWf fvi (List.mem_of_getElem? hfvi)).1
      rw [hshapei] at hW
      simp only [WScoped] at hW
      rw [hshapei]
      exact hW.2
    have hcan := interp_getD_canon (cval := m₀.val) (env := env₀)
      (φ := ψ) (e := Expr.fvarTypeD fvi) (xs := xs) (D := rP + cnF)
      hWi (by omega) (by omega)
    rw [hcan]
    exact ⟨B, hB, hvB⟩
  have hWcrD' : WScoped (rP + cnF) crestP := hWcrRp.mono (by omega)
  obtain ⟨hfitXP, hΘX⟩ := self_walk hxInst hspX hwsX hWcrD' hbcr hLcr
    hFcr hAcr hmemX
  obtain ⟨-, hPcrest2Ex⟩ := peel_walk hxInst hspX hwsX hWcrD' hAcr
    ⟨Pcr, hPcr⟩ hmemX
  obtain ⟨Pcr2, hPcr2⟩ := hPcrest2Ex
  have hfitCfullP : TeleFitI V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvj.type
      (fvsP.take cnP ++ xFvsP) (xs.take cnP ++ xs.drop rP) crest2 :=
    TeleFitI.append hfitC hfitXP
  obtain ⟨hWcrest2, hbcrest2, hAcrest2, hlcrest2⟩ :=
    TeleFitI.rest_wf hfitCfullP hWc hCb hAc
  have hFcrest2 : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) crest2 := by
    intro l hl
    rcases hlcrest2 l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact hFsC a ha l hla
      · exact hΘX a ha l hla
  have hLcrest2 : Expr.LeavesBounded crest2 := by
    intro l hl
    rcases hlcrest2 l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact hLsC a ha l hla
      · exact hLsX a ha l hla
  -- ===== S1: the membership packs across the frames =====
  -- the theorem prefix: memberships in the renamed member type's
  -- instantiated parameter domains
  obtain ⟨⟨bsTy, restTy⟩, htyStripSome⟩ :=
    Option.isSome_iff_exists.mp htyStrip
  obtain ⟨restTyPre, htyPreStrip⟩ :=
    Expr.stripPis_prefix rP (mI - rP)
      (by rw [show rP + (mI - rP) = mI from by omega]
          exact htyStripSome)
  obtain ⟨⟨dsPubR, restPubR⟩, hinstPubR⟩ :=
    Option.isSome_iff_exists.mp
      (instPisAt_isSome_of_stripPis (fvs.take rP)
        (by rw [hfvsPreLen, htyPreStrip]; rfl))
  have hiaWpre : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (fvs.take rP)
      (xs.take rP) :=
    InstArgs.of_fvarSpine hspWpre (fun a ha =>
      ⟨hfvsW a (List.mem_of_mem_take ha),
        (hfvsWf a (List.mem_of_mem_take ha)).2.1⟩)
  have hpackR := fit_mem_frames (φ := ψ) htyw htyb htyPreStrip
    hinstPubR hfvsPreLen hiaWpre hfitP
  have hstripRenPre := stripPis_renameConsts (f := f) rP htyPreStrip
  have hmemR : ∀ (k : Nat) (a : Expr) (v : V), rdoms[k]? = some a →
      (xs.take rP)[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro k a v ha hv
    have hkr : k < rP := by
      rcases Nat.lt_or_ge k rP with h | h
      · exact h
      · rw [List.getElem?_eq_none (by
          rw [instPisAt_length _ hrinst, hfvsPreLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨b, hb⟩ : ∃ b, (bsTy.take rP)[k]? = some b := by
      have := Expr.stripPis_length rP htyPreStrip
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hdsRen⟩ := instPisAt_stripPis (fvs.take rP) hrinst
      (by rw [hfvsPreLen]; exact hstripRenPre)
    obtain ⟨-, hdsPub⟩ := instPisAt_stripPis (fvs.take rP) hinstPubR
      (by rw [hfvsPreLen]; exact htyPreStrip)
    have ha1 := hdsRen k _ (by
      rw [List.getElem?_map, hb]
      rfl)
    rw [ha] at ha1
    obtain rfl := Option.some.inj ha1
    obtain ⟨B, hBi, hvB⟩ := hpackR k _ v (hdsPub k b hb) hv
    refine ⟨B, ?_, hvB⟩
    have hshapes : ∀ x ∈ (fvs.take rP).take k, ∃ i n t,
        x = .fvar i n t := fun x hx =>
      hfvsShapes x (List.mem_of_mem_take (List.mem_of_mem_take hx))
    rw [interp_instSeq_ren hro hshapes]
    exact hBi
  -- the constructor telescope: memberships in the renamed constructor
  -- type's instantiated domains (parameters and fields)
  obtain ⟨⟨bsC, cbody⟩, hCstripPair⟩ :=
    Option.isSome_iff_exists.mp hCstripSome
  obtain ⟨⟨dsPubC, restPubC⟩, hinstPubC⟩ :=
    Option.isSome_iff_exists.mp
      (instPisAt_isSome_of_stripPis (fvs.take cnP ++ fvs.drop rP)
        (by rw [hfvsCLen, hCstripPair]; rfl))
  have hiaWctor : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvs.take cnP ++ fvs.drop rP) (xs.take cnP ++ xs.drop rP) :=
    InstArgs.of_fvarSpine hspWctor (fun a ha => by
      rcases List.mem_append.mp ha with ha' | ha'
      · exact ⟨hfvsW a (List.mem_of_mem_take ha'),
          (hfvsWf a (List.mem_of_mem_take ha')).2.1⟩
      · exact ⟨hfvsW a (List.mem_of_mem_drop ha'),
          (hfvsWf a (List.mem_of_mem_drop ha')).2.1⟩)
  have hpackCF := fit_mem_frames (φ := ψ) hCw hCb hCstripPair
    hinstPubC hfvsCLen hiaWctor hfitCfullP
  have hstripRenC := stripPis_renameConsts (f := f) (cnP + cnF)
    hCstripPair
  have hmemC : ∀ (k : Nat) (a : Expr) (v : V), cdoms[k]? = some a →
      (xs.take cnP ++ xs.drop rP)[k]? = some v →
      ∃ B, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun l => xs.getD l SetTheory.empty) a = some B ∧ v ∈ˢ B := by
    intro k a v ha hv
    have hkc : k < cnP + cnF := by
      rcases Nat.lt_or_ge k (cnP + cnF) with h | h
      · exact h
      · rw [List.getElem?_eq_none (by
          rw [instPisAt_length _ hcinst, hfvsCLen]; omega)] at ha
        exact nomatch ha
    obtain ⟨b, hb⟩ : ∃ b, bsC[k]? = some b := by
      have := Expr.stripPis_length (cnP + cnF) hCstripPair
      exact ⟨_, List.getElem?_eq_getElem (by omega)⟩
    obtain ⟨-, hdsRen⟩ := instPisAt_stripPis
      (fvs.take cnP ++ fvs.drop rP) hcinst
      (by rw [hfvsCLen]; exact hstripRenC)
    obtain ⟨-, hdsPub⟩ := instPisAt_stripPis
      (fvs.take cnP ++ fvs.drop rP) hinstPubC
      (by rw [hfvsCLen]; exact hCstripPair)
    have ha1 := hdsRen k _ (by
      rw [List.getElem?_map, hb]
      rfl)
    rw [ha] at ha1
    obtain rfl := Option.some.inj ha1
    obtain ⟨B, hBi, hvB⟩ := hpackCF k _ v (hdsPub k b hb) hv
    refine ⟨B, ?_, hvB⟩
    have hshapes : ∀ x ∈ (fvs.take cnP ++ fvs.drop rP).take k,
        ∃ i n t, x = .fvar i n t := by
      intro x hx
      have hx' := List.mem_of_mem_take hx
      rcases List.mem_append.mp hx' with hx'' | hx''
      · exact hfvsShapes x (List.mem_of_mem_take hx'')
      · exact hfvsShapes x (List.mem_of_mem_drop hx'')
    rw [interp_instSeq_ren hro hshapes]
    exact hBi
  -- ===== S2: the theorem walk =====
  have hfvsInst' : Expr.instPisAt
      (fvs.take rP ++ fvs.drop rP) cvt.type =
      some (fvs.map Expr.fvarTypeD, tbody) := by
    rw [List.take_append_drop]
    exact hfvsInst
  obtain ⟨dsS1, midS, dsS2, hopS1, hopS2, hdsSplit⟩ :=
    instPisAt_append _ _ hfvsInst'
  have hdsS1len : dsS1.length = rP := by
    rw [instPisAt_length _ hopS1, hfvsPreLen]
  obtain ⟨hdsS1eq, hdsS2eq⟩ : dsS1 = (fvs.take rP).map
      Expr.fvarTypeD ∧ dsS2 = (fvs.drop rP).map
      Expr.fvarTypeD := by
    have hmap : fvs.map Expr.fvarTypeD =
        (fvs.take rP).map Expr.fvarTypeD ++
        (fvs.drop rP).map Expr.fvarTypeD := by
      rw [← List.map_append, List.take_append_drop]
    rw [hmap] at hdsSplit
    exact List.append_inj hdsSplit.symm (by
      rw [hdsS1len, List.length_map, hfvsPreLen])
  subst hdsS1eq hdsS2eq
  have hWS : WScoped (rP + cnF) cvt.type :=
    WScoped.of_not_hasFvar hSw
  have hLS : Expr.LeavesBounded cvt.type :=
    Expr.LeavesBounded.of_not_hasFvar hSw
  have hFS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type :=
    FvarsOk.of_not_hasFvar hSw
  have hAS : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type :=
    AnnotOk.closed_invariant hSw _ _ (hthm_annot ψ)
  obtain ⟨P, hPc, hPmem⟩ := hthm_mem ψ
  have hPI : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cvt.type = some P := by
    rw [interp_closed_invariant hSw _ _]
    exact hPc
  -- the renamed member type's invariants
  have htyRw : (tyA.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]
    exact htyw
  have htyRb : (tyA.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]
    exact htyb
  have hAtyR : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (tyA.renameConsts f) :=
    AnnotOk.closed_invariant htyRw _ _
      (AnnotOk.renameConsts hro tyA 0 (rho0 V) hAty)
  obtain ⟨Tty, hTtyc⟩ := hIty
  have hItyR : ∃ TR, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) (tyA.renameConsts f) =
      some TR := by
    refine ⟨Tty, ?_⟩
    rw [interp_closed_invariant htyRw _ _]
    show interpClosed V m₀.val env₀ _ (tyA.renameConsts f) = some Tty
    unfold interpClosed
    rw [interp_renameConsts hro tyA 0 (rho0 V)]
    exact hTtyc
  -- stage 1: the prefix walk
  obtain ⟨hfitS1, hfitR1, hΘpre⟩ := pi_walk m₀ F hopS1 hrinst hdePre
    hspWpre (fun a ha => hfvsW a (List.mem_of_mem_take ha))
    hWS hSb hLS hFS hAS
    (WScoped.of_not_hasFvar htyRw) htyRb
    (Expr.LeavesBounded.of_not_hasFvar htyRw)
    (FvarsOk.of_not_hasFvar htyRw) hAtyR
    ⟨P, hPI⟩ hItyR hmemR
  obtain ⟨Qmid, hQmidI, hQmidMem, hAmidS⟩ :=
    TeleFitI.elim hfitS1 hAS hPI hPmem
  obtain ⟨hWmidS, hbmidS, -, hleavesMidS⟩ :=
    TeleFitI.rest_wf hfitS1 hWS hSb hAS
  have hFmidS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact hΘpre a ha l hla
  have hLmidS : Expr.LeavesBounded midS := by
    intro l hl
    rcases hleavesMidS l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hSw] at hl'
      cases hl'
    · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
  -- the renamed constructor's parameter walk to its mid residual
  obtain ⟨cdomsA, midC, cdomsB, hopC1, hopC2, hcdomsSplit⟩ :=
    instPisAt_append _ _ hcinst
  have hcdomsAlen : cdomsA.length = cnP := by
    rw [instPisAt_length _ hopC1, List.length_take, hfvsLen]
    omega
  have hcdomsBeq : cdoms.drop cnP = cdomsB := by
    rw [hcdomsSplit, List.drop_append_of_le_length (by omega),
      List.drop_eq_nil_of_le (by omega), List.nil_append]
  have hCRw : (cvj.type.renameConsts f).hasFvar = false := by
    rw [hasFvar_renameConsts]; exact hCw
  have hCRb : (cvj.type.renameConsts f).looseBVarsBounded 0 = true := by
    rw [looseBVarsBounded_renameConsts]; exact hCb
  have hACtyR : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (cvj.type.renameConsts f) :=
    AnnotOk.closed_invariant hCRw _ _
      (AnnotOk.renameConsts hro cvj.type 0 (rho0 V) hACty)
  have hICtyR : ∃ TR, interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (cvj.type.renameConsts f) = some TR := by
    obtain ⟨TC, hTCc⟩ := hICty
    refine ⟨TC, ?_⟩
    rw [interp_closed_invariant hCRw _ _]
    show interpClosed V m₀.val env₀ _ (cvj.type.renameConsts f) = some TC
    unfold interpClosed
    rw [interp_renameConsts hro cvj.type 0 (rho0 V)]
    exact hTCc
  obtain ⟨hfitC1, hImidC⟩ := peel_walk hopC1 hspWctorPre
    (fun a ha => hfvsW a (List.mem_of_mem_take ha))
    (WScoped.of_not_hasFvar hCRw) hACtyR hICtyR
    (fun k a v ha hv => by
      have hkA : k < cnP := by
        rcases Nat.lt_or_ge k cnP with hlt | hge
        · exact hlt
        · rw [List.getElem?_eq_none (by omega)] at ha
          exact nomatch ha
      refine hmemC k a v ?_ ?_
      · rw [hcdomsSplit, List.getElem?_append_left (by omega)]
        exact ha
      · rw [List.getElem?_append_left
          (by rw [List.length_take]; omega)]
        exact hv)
  obtain ⟨hWmidC, hbmidC, hAmidC, hleavesMidC⟩ :=
    TeleFitI.rest_wf hfitC1 (WScoped.of_not_hasFvar hCRw) hCRb hACtyR
  have hFmidC : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · refine hΘpre a ?_ l hla
      have heq : fvs.take cnP = (fvs.take rP).take cnP := by
        rw [List.take_take, Nat.min_eq_left hplainLe]
      rw [heq] at ha
      exact List.mem_of_mem_take ha
  have hLmidC : Expr.LeavesBounded midC := by
    intro l hl
    rcases hleavesMidC l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
  -- stage 2: the field walk
  obtain ⟨hfitS2, hfitR2, hΘx⟩ := pi_walk m₀ F hopS2
    (by rw [← hcdomsBeq] at hopC2; exact hopC2)
    hdeFld
    hspWdrop (fun a ha => hfvsW a (List.mem_of_mem_drop ha))
    hWmidS hbmidS hLmidS hFmidS hAmidS
    hWmidC hbmidC hLmidC hFmidC hAmidC
    ⟨Qmid, hQmidI⟩ hImidC
    (fun k a v ha hv => by
      refine hmemC (cnP + k) a v ?_ ?_
      · rw [List.getElem?_drop] at ha
        exact ha
      · rw [List.getElem?_append_right
          (by rw [List.length_take]; omega)]
        rw [List.length_take,
          show cnP + k - min cnP xs.length = k from by omega]
        exact hv)
  obtain ⟨Q, hQI, hQmem0, hAtbody⟩ :=
    TeleFitI.elim hfitS2 hAmidS hQmidI hQmidMem
  have hQmem : SpineFold V (m₀.val thmName ψ) xs ∈ˢ Q := by
    have h0 : SpineFold V (m₀.val thmName ψ)
        (xs.take rP ++ xs.drop rP) ∈ˢ Q := by
      rw [SpineFold_append]
      exact hQmem0
    rwa [List.take_append_drop] at h0
  -- ===== S3: the Eq collapse =====
  have htbodyEq : tbody = Expr.mkAppN (.const eqName [ℓA])
      [αS, lhsS, rhsS] := by
    have h0 := Expr.mkAppN_getApp tbody
    rw [hheadEq, hargs3] at h0
    exact h0.symm
  rw [htbodyEq] at hQI hAtbody
  obtain ⟨-, hcompsA, veq, vsE, hveqi, hspE, hchainE, hfoldQ⟩ :=
    annotOk_spine_inv _ (.const eqName [ℓA]) (by simp) hAtbody
  obtain ⟨vα, vl, vr, rfl⟩ : ∃ vα vl vr, vsE = [vα, vl, vr] := by
    match vsE, hspE with
    | [vα, vl, vr], _ => exact ⟨vα, vl, vr, rfl⟩
    | [], h => exact nomatch h
    | [_], h => exact nomatch h.2
    | [_, _], h => exact nomatch h.2.2
    | _ :: _ :: _ :: _ :: _, h => exact nomatch h.2.2.2
  obtain ⟨hiα, hil, hir, -⟩ := hspE
  have hQeq : Q = SpineFold V veq [vα, vl, vr] := by
    rw [hfoldQ] at hQI
    exact Option.some.inj hQI |>.symm
  have hveq : veq = eqVal V (Level.substFn ψ [uN] [ℓA]) := by
    simp only [interpExpr, heqfind] at hveqi
    rw [if_pos (by simp [eqA, ConstantInfo.toConstantVal])] at hveqi
    rw [← Option.some.inj hveqi, heqval]
    congr 2
  obtain ⟨⟨vE₁, A₁, B₁, hpi₁, hmem₁, -⟩, hchainE'⟩ := hchainE
  obtain ⟨⟨vE₂, A₂, B₂, hpi₂, hmem₂, -⟩, hchainE''⟩ := hchainE'
  obtain ⟨⟨vE₃, A₃, B₃, hpi₃, hmem₃, -⟩, -⟩ := hchainE''
  rw [hveq] at hpi₁ hpi₂ hpi₃
  have hαu : vα ∈ˢ univ (Level.substFn ψ [uN] [ℓA] uN) := by
    have h1 := hpi₁
    simp only [eqVal] at h1
    refine lam_dom_of_ne h1 ?_ vα hmem₁
    simp [Nat.max_eq_zero_iff]
  have hvlmem : vl ∈ˢ vα := by
    have h2 := hpi₂
    rw [eqVal_app hαu] at h2
    refine lam_dom_of_ne h2 ?_ vl hmem₂
    simp [Nat.max_eq_zero_iff]
  have hvrmem : vr ∈ˢ vα := by
    have h3 := hpi₃
    rw [eqVal_app₂ hαu hvlmem] at h3
    refine lam_dom_of_ne h3 ?_ vr hmem₃
    simp
  have hQeqv : Q = eqv vl vr := by
    rw [hQeq, hveq]
    show SpineFold V _ [vα, vl, vr] = _
    rw [show SpineFold V (eqVal V (Level.substFn ψ [uN] [ℓA]))
        [vα, vl, vr] =
      SetTheory.app (SetTheory.app (SetTheory.app
        (eqVal V (Level.substFn ψ [uN] [ℓA]))
        vα) vl) vr from rfl]
    exact eqVal_app₃ hαu hvlmem hvrmem
  have hvlvr : vl = vr := by
    rw [hQeqv] at hQmem
    exact mem_eqv hQmem
  -- ===== S4: decompose the statement's left side =====
  have hlhsEq : lhsS = Expr.mkAppN (.const (f R) (lps.map .param))
      lhsS.getAppArgs := by
    have h0 := Expr.mkAppN_getApp lhsS
    rw [hlhead] at h0
    exact h0.symm
  have hAlhs : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) lhsS :=
    hcompsA lhsS (by simp)
  rw [hlhsEq] at hAlhs
  obtain ⟨-, hlargsA, vhead, lvals, hheadI, hspL, hchainL, hfoldL⟩ :=
    annotOk_spine_inv _ (.const (f R) (lps.map .param))
      (by
        intro h0
        rw [h0] at hlarity
        exact nomatch hlarity) hAlhs
  have hvlfold : vl = SpineFold V vhead lvals := by
    rw [← hlhsEq] at hfoldL
    rw [hfoldL] at hil
    exact Option.some.inj hil |>.symm
  -- the head is the recursor's value
  have hsubstψ : Level.substFn ψ lps (lps.map .param) = ψ :=
    funext (fun p => Level.substFn_map_param)
  have hcRi : interpExpr V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (.const (f R) (lps.map .param)) = some (m₀.val R ψ) := by
    simp only [interpExpr, hfRm]
    rw [if_pos (by rw [hRmlps]; simp)]
    rw [show cim.toConstantVal.levelParams = lps from hRmlps]
    rw [hsubstψ, hro.2.2 R]
  have hvhead : vhead = m₀.val R ψ := by
    rw [hcRi] at hheadI
    exact Option.some.inj hheadI |>.symm
  -- the equation body's component facts
  obtain ⟨hWtbody0, hbtbody0, htbodyL0⟩ := htbodyWf
  have hlhsMem : lhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWlhs : WScoped (rP + cnF) lhsS := by
    have h0 := hWtbody0.getAppArgs lhsS hlhsMem
    rwa [Nat.zero_add] at h0
  have hblhs : lhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hlhsMem
  obtain ⟨-, -, -, hleavesTbody⟩ := TeleFitI.rest_wf hfitS2 hWmidS hbmidS
    hAmidS
  have hFtbody : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) tbody := by
    intro l hl
    rcases hleavesTbody l hl with hl' | ⟨a, ha, hla⟩
    · exact hFmidS l hl'
    · exact hΘx a ha l hla
  have hFlhs : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) lhsS :=
    FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hlhsMem l hl)
      hFtbody
  have hLlhs : Expr.LeavesBounded lhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hlhsMem l hl)
  have hrhsMem : rhsS ∈ tbody.getAppArgs := by
    rw [hargs3]; simp
  have hWrhsS : WScoped (rP + cnF) rhsS := by
    have h0 := hWtbody0.getAppArgs rhsS hrhsMem
    rwa [Nat.zero_add] at h0
  have hbrhsS : rhsS.looseBVarsBounded 0 = true :=
    looseBVarsBounded_getAppArgs hbtbody0 _ hrhsMem
  have hFrhsS : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsS :=
    FvarsOk.of_subset (fun l hl => fvarLeaves_getAppArgs hrhsMem l hl)
      hFtbody
  have hLrhsS : Expr.LeavesBounded rhsS :=
    fun l hl => htbodyL0 l (fvarLeaves_getAppArgs hrhsMem l hl)
  have hArhsS : AnnotOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) rhsS :=
    hcompsA rhsS (by simp)
  -- the full renamed constructor fit and `cres`'s facts
  have hfitCfull : TeleFitI V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (cvj.type.renameConsts f)
      (fvs.take cnP ++ fvs.drop rP) (xs.take cnP ++ xs.drop rP)
      cres := by
    exact TeleFitI.append hfitC1 hfitR2
  obtain ⟨hWcres, hbcres, hAcres, hleavesCres⟩ :=
    TeleFitI.rest_wf hfitCfull (WScoped.of_not_hasFvar hCRw) hCRb hACtyR
  have hFcres : FvarsOk V m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty) cres := by
    intro l hl
    rcases hleavesCres l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · refine hΘpre a ?_ l hla
        have heq : fvs.take cnP = (fvs.take rP).take cnP := by
          rw [List.take_take, Nat.min_eq_left hplainLe]
        rw [heq] at ha
        exact List.mem_of_mem_take ha
      · exact hΘx a ha l hla
  have hLcres : Expr.LeavesBounded cres := by
    intro l hl
    rcases hleavesCres l hl with hl' | ⟨a, ha, hla⟩
    · rw [fvarLeaves_eq_nil_of_not_hasFvar hCRw] at hl'
      cases hl'
    · rcases List.mem_append.mp ha with ha | ha
      · exact (hfvsWf a (List.mem_of_mem_take ha)).2.2 l hla
      · exact (hfvsWf a (List.mem_of_mem_drop ha)).2.2 l hla
  -- the constructor body and both residuals' argument spines
  have hcbodyNF : cbody.hasFvar = false :=
    stripPis_body_hasFvar _ hCstripPair hCw
  have hcbodyBnd : cbody.looseBVarsBounded (cnP + cnF) = true := by
    have h0 := stripPis_body_bounded _ hCstripPair hCb
    simpa using h0
  have hcspine : cbody = Expr.mkAppN cbody.getAppFn cbody.getAppArgs :=
    (Expr.mkAppN_getApp cbody).symm
  have hfvsCShapes : ∀ a ∈ fvs.take cnP ++ fvs.drop rP,
      ∃ i n t, a = .fvar i n t := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact hfvsShapes a (List.mem_of_mem_take ha)
    · exact hfvsShapes a (List.mem_of_mem_drop ha)
  obtain ⟨hcresEq0, -⟩ := instPisAt_stripPis
    (fvs.take cnP ++ fvs.drop rP) hcinst
    (by rw [hfvsCLen]; exact hstripRenC)
  have hcresEq' : cres = instSeq (fvs.take cnP ++ fvs.drop rP)
      (cnP + cnF - 1) (cbody.renameConsts f) := by
    rw [hcresEq0, hfvsCLen]
  have hheadRenNotApp : ∀ f' a',
      cbody.getAppFn.renameConsts f ≠ .app f' a' := by
    intro f' a' hcon
    cases hfn : cbody.getAppFn with
    | app g b => exact getAppFn_not_app cbody g b hfn
    | bvar _ => rw [hfn] at hcon; exact nomatch hcon
    | fvar _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | sort _ => rw [hfn] at hcon; exact nomatch hcon
    | const _ _ => rw [hfn] at hcon; exact nomatch hcon
    | lam _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | forallE _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | letE _ _ _ _ => rw [hfn] at hcon; exact nomatch hcon
    | lit _ => rw [hfn] at hcon; exact nomatch hcon
    | proj _ _ _ => rw [hfn] at hcon; exact nomatch hcon
  have hcresArgs : cres.getAppArgs = cbody.getAppArgs.map
      (fun e => instSeq (fvs.take cnP ++ fvs.drop rP)
        (cnP + cnF - 1) (e.renameConsts f)) := by
    rw [hcresEq']
    calc (instSeq (fvs.take cnP ++ fvs.drop rP)
          (cnP + cnF - 1) (cbody.renameConsts f)).getAppArgs
        = (instSeq (fvs.take cnP ++ fvs.drop rP)
            (cnP + cnF - 1)
            (Expr.mkAppN (cbody.getAppFn.renameConsts f)
              (cbody.getAppArgs.map (·.renameConsts f)))).getAppArgs := by
          rw [← renameConsts_mkAppN, Expr.mkAppN_getApp]
      _ = (Expr.mkAppN (instSeq (fvs.take cnP ++ fvs.drop rP)
            (cnP + cnF - 1) (cbody.getAppFn.renameConsts f))
            ((cbody.getAppArgs.map (·.renameConsts f)).map
              (instSeq (fvs.take cnP ++ fvs.drop rP)
                (cnP + cnF - 1) ·))).getAppArgs := by
          rw [instSeq_mkAppN]
      _ = _ := by
          rw [Expr.getAppArgs_mkAppN,
            getAppArgs_of_not_app
              (instSeq_fvars_not_app _ _ hfvsCShapes hheadRenNotApp),
            List.map_map]
          simp [Function.comp]
  -- the public composed constructor walk and `crest2`'s spine
  have hpubC : Expr.instPisAt (fvsP.take cnP ++ xFvsP) cvj.type =
      some (cdomsP ++ xFvsP.map Expr.fvarTypeD, crest2) :=
    instPisAt_append_of (fvsP.take cnP) hcinstP hxInst
  have hfvsPXLen : (fvsP.take cnP ++ xFvsP).length = cnP + cnF := by
    rw [List.length_append, List.length_take, hfvsPLen, hxLen]
    omega
  have hfvsPXShapes : ∀ a ∈ fvsP.take cnP ++ xFvsP,
      ∃ i n t, a = .fvar i n t := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨j, hja⟩ := List.getElem?_of_mem
        (List.mem_of_mem_take ha)
      obtain ⟨nm, hsh⟩ := hfvsPShape j a hja
      exact ⟨0 + j, nm, _, hsh⟩
    · obtain ⟨j, hja⟩ := List.getElem?_of_mem ha
      obtain ⟨nm, hsh⟩ := hxShape j a hja
      exact ⟨rP + j, nm, _, hsh⟩
  obtain ⟨hcrest2Eq0, -⟩ := instPisAt_stripPis
    (fvsP.take cnP ++ xFvsP) hpubC
    (by rw [hfvsPXLen]; exact hCstripPair)
  have hcrest2Eq : crest2 = instSeq (fvsP.take cnP ++ xFvsP)
      (cnP + cnF - 1) cbody := by
    rw [hcrest2Eq0, hfvsPXLen]
  have hcrest2Args : crest2.getAppArgs = cbody.getAppArgs.map
      (fun e => instSeq (fvsP.take cnP ++ xFvsP)
        (cnP + cnF - 1) e) := by
    rw [hcrest2Eq]
    calc (instSeq (fvsP.take cnP ++ xFvsP)
          (cnP + cnF - 1) cbody).getAppArgs
        = (instSeq (fvsP.take cnP ++ xFvsP)
            (cnP + cnF - 1)
            (Expr.mkAppN cbody.getAppFn cbody.getAppArgs)).getAppArgs := by
          rw [Expr.mkAppN_getApp]
      _ = (Expr.mkAppN (instSeq (fvsP.take cnP ++ xFvsP)
            (cnP + cnF - 1) cbody.getAppFn)
            (cbody.getAppArgs.map
              (instSeq (fvsP.take cnP ++ xFvsP)
                (cnP + cnF - 1) ·))).getAppArgs := by
          rw [instSeq_mkAppN]
      _ = _ := by
          rw [Expr.getAppArgs_mkAppN,
            getAppArgs_of_not_app
              (instSeq_fvars_not_app _ _ hfvsPXShapes
                (getAppFn_not_app _))]
          rfl
  -- ===== S4b: the argument values =====
  have hlvalsLen : lvals.length = mI + 1 := by
    rw [InterpSpine.length hspL, hlarity]
  obtain ⟨lastE, hlargsDecomp, hlastE⟩ :=
    take_concat_of_length (l := lhsS.getAppArgs) (n := mI) hlarity
  obtain ⟨vlast, hlvalsDecomp, hvlast⟩ :=
    take_concat_of_length (l := lvals) (n := mI) hlvalsLen
  have hlastEmaj : lastE =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP) := by
    have h0 : lhsS.getAppArgs.getLastD (.bvar 0) = lastE := by
      conv => lhs; rw [hlargsDecomp]
      rw [List.getLastD_concat]
    rw [← h0, hmaj]
  -- the prefix values are the frame values
  have hcbodyArgsLen : cbody.getAppArgs.length = cnP + (mI - rP) := by
    have h0 : cres.getAppArgs.length = cbody.getAppArgs.length := by
      rw [hcresArgs, List.length_map]
    rw [← h0, hclen]
  have hpreValsEq : lvals.take rP = xs.take rP := by
    apply List.ext_getElem?
    intro i
    rcases Nat.lt_or_ge i rP with hi | hi
    · obtain ⟨ei, hei⟩ : ∃ e, lhsS.getAppArgs[i]? = some e :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      obtain ⟨vi, hvi⟩ : ∃ v, lvals[i]? = some v :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      have hint := InterpSpine.pointwise hspL i hei hvi
      have heifv : fvs[i]? = some ei := by
        have h0 := congrArg (·[i]?) hlpre
        simp only [List.getElem?_take_of_lt hi] at h0
        rw [← h0, hei]
      obtain ⟨nmi, hshi⟩ := hfvsShape i ei heifv
      rw [Nat.zero_add] at hshi
      rw [hshi] at hint
      simp only [interpExpr] at hint
      have hvix : vi = xs.getD i SetTheory.empty :=
        (Option.some.inj hint).symm
      rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi,
        hvi, hvix, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem (l := xs) (i := i) (by omega)]
      rfl
    · rw [List.getElem?_eq_none (by rw [List.length_take]; omega),
        List.getElem?_eq_none (by rw [List.length_take]; omega)]
  -- `cres`'s per-argument facts
  have hcresArgW : ∀ e ∈ cres.getAppArgs, WScoped (rP + cnF) e :=
    fun e he => hWcres.getAppArgs e he
  have hcresArgB : ∀ e ∈ cres.getAppArgs,
      e.looseBVarsBounded 0 = true :=
    fun e he => looseBVarsBounded_getAppArgs hbcres e he
  have hcresArgL : ∀ e ∈ cres.getAppArgs, Expr.LeavesBounded e :=
    fun e he l hl => hLcres l (fvarLeaves_getAppArgs he l hl)
  have hcresArgF : ∀ e ∈ cres.getAppArgs,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e :=
    fun e he => FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs he l hl) hFcres
  have hcresSpineInv : cres.getAppArgs ≠ [] →
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (Expr.mkAppN cres.getAppFn cres.getAppArgs) := by
    intro _
    rw [Expr.mkAppN_getApp]
    exact hAcres
  have hcresArgA : ∀ e ∈ cres.getAppArgs,
      AnnotOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e := by
    intro e he
    have hne : cres.getAppArgs ≠ [] := by
      intro h0
      rw [h0] at he
      exact nomatch he
    obtain ⟨-, hargsA, -⟩ := annotOk_spine_inv _ cres.getAppFn hne
      (hcresSpineInv hne)
    exact hargsA e he
  have hcresArgI : ∀ e ∈ cres.getAppArgs,
      ∃ w, interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e = some w := by
    intro e he
    have hne : cres.getAppArgs ≠ [] := by
      intro h0
      rw [h0] at he
      exact nomatch he
    obtain ⟨-, -, vf, cvals, -, hspCres, -, -⟩ :=
      annotOk_spine_inv _ cres.getAppFn hne (hcresSpineInv hne)
    obtain ⟨j, hj⟩ := List.getElem?_of_mem he
    obtain ⟨w, hw⟩ : ∃ w, cvals[j]? = some w := by
      have hlen := InterpSpine.length hspCres
      refine ⟨_, List.getElem?_eq_getElem ?_⟩
      rw [hlen]
      rcases Nat.lt_or_ge j cres.getAppArgs.length with h | h
      · exact h
      · rw [List.getElem?_eq_none h] at hj
        exact nomatch hj
    exact ⟨w, InterpSpine.pointwise hspCres j hj hw⟩
  -- lhsS's per-argument facts
  have hlargsW : ∀ e ∈ lhsS.getAppArgs, WScoped (rP + cnF) e :=
    fun e he => hWlhs.getAppArgs e he
  have hlargsB : ∀ e ∈ lhsS.getAppArgs, e.looseBVarsBounded 0 = true :=
    fun e he => looseBVarsBounded_getAppArgs hblhs e he
  have hlargsL : ∀ e ∈ lhsS.getAppArgs, Expr.LeavesBounded e :=
    fun e he l hl => hLlhs l (fvarLeaves_getAppArgs he l hl)
  have hlargsF : ∀ e ∈ lhsS.getAppArgs,
      FvarsOk V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e :=
    fun e he => FvarsOk.of_subset
      (fun l hl => fvarLeaves_getAppArgs he l hl) hFlhs
  -- the index values: statement's equal the public residual's
  have hpubSpine : FvarSpine (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvsP.take cnP ++ xFvsP) (xs.take cnP ++ xs.drop rP) :=
    FvarSpine.append hspC hspX
  have hiaPub : InstArgs m₀.val env₀ ψ (rP + cnF)
      (fun i => xs.getD i SetTheory.empty)
      (fvsP.take cnP ++ xFvsP) (xs.take cnP ++ xs.drop rP) :=
    InstArgs.of_fvarSpine hpubSpine (fun a ha => by
      rcases List.mem_append.mp ha with ha' | ha'
      · exact ⟨hwsP a (List.mem_of_mem_take ha'),
          (hfvsPWf a (List.mem_of_mem_take ha')).2.1⟩
      · exact ⟨(hxWf a ha').1, (hxWf a ha').2.1⟩)
  have hidxVal : ∀ (j : Nat) (e2 : Expr) (v : V),
      (crest2.getAppArgs.drop cnP)[j]? = some e2 →
      (lvals.drop rP)[j]? = some v → j < mI - rP →
      interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty) e2 = some v := by
    intro j e2 v he2 hv hjlt
    -- the statement-side index argument and its value
    obtain ⟨eS, heS⟩ : ∃ e, lhsS.getAppArgs[rP + j]? = some e :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    rw [List.getElem?_drop] at hv
    have hintS := InterpSpine.pointwise hspL (rP + j) heS hv
    -- the renamed residual's index argument
    obtain ⟨carg, hcarg⟩ : ∃ c, cbody.getAppArgs[cnP + j]? = some c :=
      ⟨_, List.getElem?_eq_getElem (by omega)⟩
    have heR : cres.getAppArgs[cnP + j]? = some
        (instSeq (fvs.take cnP ++ fvs.drop rP) (cnP + cnF - 1)
          (carg.renameConsts f)) := by
      rw [hcresArgs, List.getElem?_map, hcarg]
      rfl
    have he2' : e2 = instSeq (fvsP.take cnP ++ xFvsP)
        (cnP + cnF - 1) carg := by
      rw [List.getElem?_drop, hcrest2Args, List.getElem?_map,
        hcarg] at he2
      exact (Option.some.inj he2).symm
    -- the kernel index pin identifies the two interpretations
    have hdej := DefEqListOk.pointwise hdeIdx j
      (a := eS) (b := instSeq (fvs.take cnP ++ fvs.drop rP)
        (cnP + cnF - 1) (carg.renameConsts f))
      (by
        rw [List.getElem?_take_of_lt hjlt, List.getElem?_drop]
        exact heS)
      (by
        rw [List.getElem?_drop]
        exact heR)
    have heSmem : eS ∈ lhsS.getAppArgs := List.mem_of_getElem? heS
    have heRmem : instSeq (fvs.take cnP ++ fvs.drop rP)
        (cnP + cnF - 1) (carg.renameConsts f) ∈ cres.getAppArgs :=
      List.mem_of_getElem? heR
    obtain ⟨wR, hwR⟩ := hcresArgI _ heRmem
    have hveq := isDefEqCore_sound m₀ F hdej
      (hlargsW eS heSmem) (hcresArgW _ heRmem)
      (hlargsB eS heSmem) (hcresArgB _ heRmem)
      (hlargsL eS heSmem) (hcresArgL _ heRmem)
      (hlargsF eS heSmem) (hcresArgF _ heRmem)
      (hlargsA eS heSmem) (hcresArgA _ heRmem)
      hintS hwR
    -- cross to the public residual's argument
    have hcargNF : carg.hasFvar = false :=
      hasFvar_getAppArgs hcbodyNF _ (List.mem_of_getElem? hcarg)
    have hcargBnd : carg.looseBVarsBounded (cnP + cnF) = true :=
      looseBVarsBounded_getAppArgs hcbodyBnd _
        (List.mem_of_getElem? hcarg)
    have hren : interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (instSeq (fvs.take cnP ++ fvs.drop rP) (cnP + cnF - 1)
          (carg.renameConsts f)) =
        interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (instSeq (fvs.take cnP ++ fvs.drop rP) (cnP + cnF - 1)
          carg) :=
      interp_instSeq_ren hro hfvsCShapes
    have hframes : interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (instSeq (fvs.take cnP ++ fvs.drop rP)
          ((fvs.take cnP ++ fvs.drop rP).length - 1) carg) =
        interpExpr V m₀.val env₀ ψ (rP + cnF)
        (fun i => xs.getD i SetTheory.empty)
        (instSeq (fvsP.take cnP ++ xFvsP)
          ((fvsP.take cnP ++ xFvsP).length - 1) carg) :=
      interp_instSeq_frames hiaWctor hiaPub hcargNF
        (by rw [hfvsCLen]; exact hcargBnd)
    rw [hfvsCLen] at hframes
    rw [hfvsPXLen] at hframes
    rw [he2', ← hframes, ← hren, hwR]
    exact congrArg some hveq.symm
  sorry

end Setlec
