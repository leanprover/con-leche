import Setlec.Model.TypeChecker
import Setlec.Model.IotaWalk

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
    {nP nM nm ni : Nat}
    {cim : ConstantInfo}
    (hfRm : env₀.find? (f R) = some cim)
    (hRmlps : cim.toConstantVal.levelParams = lps)
    -- the constructor and its model
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    (hfj : env₀.find? ctor = some (.ctorInfo cvj cnP cnF))
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
    (hopen : openPisAtFvars (nP + nM + nm + cnF) cvt.type 0 =
      some (fvs, tbody))
    (hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (hlhead : lhsS.getAppFn = Expr.const (f R) (lps.map .param))
    (hlarity : lhsS.getAppArgs.length = nP + nM + nm + ni + 1)
    (hlpre : lhsS.getAppArgs.take (nP + nM + nm) =
      fvs.take (nP + nM + nm))
    (hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop (nP + nM + nm)))
    (hcstrip : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    (hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop (nP + nM + nm))
      (cvj.type.renameConsts f) = some (cdoms, cres))
    (hclen : cres.getAppArgs.length = cnP + ni)
    (hdeIdx : DefEqListOk F env₀ (nP + nM + nm + cnF)
      ((lhsS.getAppArgs.drop (nP + nM + nm)).take ni)
      (cres.getAppArgs.drop cnP))
    (hdeFld : DefEqListOk F env₀ (nP + nM + nm + cnF)
      ((fvs.drop (nP + nM + nm)).map Expr.fvarTypeD) (cdoms.drop cnP))
    (hrinst : Expr.instPisAt (fvs.take (nP + nM + nm))
      (tyA.renameConsts f) = some (rdoms, rrest))
    (hdePre : DefEqListOk F env₀ (nP + nM + nm + cnF)
      ((fvs.take (nP + nM + nm)).map Expr.fvarTypeD) rdoms)
    (hopenP : openPisAtFvars (nP + nM + nm) tyA 0 = some (fvsP, restP))
    (hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type =
      some (cdomsP, crestP))
    (hopenX : openPisAtFvars cnF crestP (nP + nM + nm) =
      some (xFvsP, crest2))
    (hlinst : Expr.instLamsAt (fvsP ++ xFvsP) rhsA = some (ldoms, lrest))
    (hdeLam : DefEqListOk F env₀ (nP + nM + nm + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldoms)
    (hdeRhs : isDefEqCore env₀ F (nP + nM + nm + cnF) rhsS
      (Expr.mkAppN (rhsA.renameConsts f) fvs) = .ok true)
    -- rule right-hand-side facts
    (hstripR : rhsA.stripLams (nP + nM + nm + cnF) =
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
    (htyps : tyA.allLevelParamsDefined lps = true)
    (hAty : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) tyA)
    (hCw : cvj.type.hasFvar = false)
    (hCb : cvj.type.looseBVarsBounded 0 = true)
    (hCps : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (hACty : ∀ ψ'' : Name → Nat,
      AnnotOk V m₀.val env₀ ψ'' 0 (rho0 V) cvj.type)
    -- fold clause inputs
    {us usj : List Level} {args margs : List V} {tv : V}
    (hplainLe : cnP ≤ nP + nM + nm)
    (hlena : args.length = nP + nM + nm + ni)
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
      some (args.drop (nP + nM + nm))) :
    ∃ Rv, interpClosed V m₀.val env₀ (Level.substFn φ' lps us) rhsA =
        some Rv ∧
      SpineFold V (m₀.val R (Level.substFn φ' lps us)) (args ++ [tv]) =
        SpineFold V Rv (args.take (nP + nM + nm) ++ margs.drop cnP) ∧
      ChainSlots V Rv (args.take (nP + nM + nm) ++ margs.drop cnP) := by
  sorry

end Setlec
