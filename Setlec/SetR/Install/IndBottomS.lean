import Setlec.SetR.Install.Cons
import Setlec.SetR.Sound.Main
import Setlec.SetBase.Decl
import Setlec.Verify.Denote.EnvExt
import Setlec.Verify.Extend.Block
import Setlec.Verify.Denote.OpenRevDenote

/-!
# The modeled-iota bottoms: statements (task #148, T5 c1)

The [set] transposes of `IndBottomPlainTT`/`IndBottomNestedTT`
(`Setlec/TTVerify/IndBottom{Plain,Nested}.lean`), stated as obligation
`Prop`s (the house pattern of `DivModPinS`/`StdAxiomKeyS`): each
consumes the checked `_model.iota_j` theorem's kit — the shape pins
and the D6-refined quantified-context walks of `IotaThmR`/`IotaThmNR`
— together with the block-provisional `EnvS`, and concludes the
**fired `RecRulesV` law** for the stored rule at the provisional
environment (`EnvS.cons`'s `hheadRec` clause body, verbatim; the
recursor-group fold transports it to the final environment through
`denote_env_ext` and re-spells the level premise through
`recFireComparands`).

Deltas against the TT statements, all design-mandated:

* `Deq` conclusions become `interp`-equalities at every `ρ`; the
  `VTeleTyped` fits become `TeleFitV` memberships; the padding trick's
  `dummyPropT` becomes `pt` at `.sort 0` slots (`pt ∈ˢ univ 0`);
* the walks arrive as relation derivations (the quantified-context
  packs), consumed through T4's soundness at `Sat`-constructed padded
  chains — `mS.toHyp` is the claims bundle;
* **no `IotaSlotSorted`** (#146 is tt-only): the equation slot's
  universe membership is recovered from the statement's own
  truthfulness (the type front door's subject conjunct) plus graph
  rigidity of the pinned `Eq` tower;
* the conclusion carries the applied reduct's **truthfulness
  transport** (the `RecRulesOk` `AnnotOk`-of-rhs clause, fired) — the
  extra conjunct `RecRulesV` demands beyond `RecRulesTT`.
-/

namespace Setlec.SetR

open Setlec.TT Setlec.TTVerify
open SetTheory

universe w

/-- **The plain bottom** ([set] transpose of `IndBottomPlainTT`): the
checked canonical `iota_j` kit yields the fired `RecRulesV` law of the
stored `.plain` rule at the provisional environment. -/
def IndBottomPlainS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {envS : Env} (mS : EnvS V envS)
    {f : Name → Name} (_hro : RenameOkT mS.cval envS f)
    (_heqfE : envS.find? eqName = some eqA)
    {Rn : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    (_htyw : tyA.hasFvar = false)
    (_htyb : tyA.looseBVarsBounded 0 = true)
    {ciRm : ConstantInfo}
    (_hfRnE : envS.find? (f Rn) = some ciRm)
    (_hRmlps : ciRm.toConstantVal.levelParams = lps)
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    (_hctorE : envS.find? ctor = some (.ctorInfo cvj cnP cnF))
    {ciCm : ConstantInfo}
    (_hfCmE : envS.find? (f ctor) = some ciCm)
    (_hCmlps : ciCm.toConstantVal.levelParams = cvj.levelParams)
    (_hCw : cvj.type.hasFvar = false)
    (_hCb : cvj.type.looseBVarsBounded 0 = true)
    (_hClp : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (_hrPmI : rP ≤ mI) (_hplainLe : cnP ≤ rP)
    {rhsA : Expr} (_hrhsw : rhsA.hasFvar = false)
    (_hrhsb : rhsA.looseBVarsBounded 0 = true)
    -- the rule rhs's front door (from `IotaRuleR`, sound side): the
    -- denoted λ-tower is truthful and inhabits its inferred type
    (_hrhsKey : ∀ ψ' : Name → Nat, ∃ Rv t,
      denoteClosed mS.cval envS ψ' rhsA = some Rv ∧
      ∀ ρ : Nat → V, AnnotOkV V ρ Rv ∧ interp V ρ Rv ∈ˢ interp V ρ t)
    {stmtTy : Expr} (_hSw : stmtTy.hasFvar = false)
    (_hSb : stmtTy.looseBVarsBounded 0 = true)
    -- the statement's front doors: its denotation is inhabited (the
    -- theorem's own valuation) and truthful (the type front door's
    -- subject conjunct)
    (_hthm : ∀ ψ' : Name → Nat, ∃ t,
      denoteClosed mS.cval envS ψ' stmtTy = some t ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp V ρ t) ∧ AnnotOkV V ρ t)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    (_hopen : openPisAtFvars (rP + cnF) stmtTy 0 = some (fvs, tbody))
    (_hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (_hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (_hlhead : lhsS.getAppFn = Expr.const (f Rn) (lps.map .param))
    (_hlarity : lhsS.getAppArgs.length = mI + 1)
    (_hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (_hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    (_hCstrips : (cvj.type.stripPis (cnP + cnF)).isSome = true)
    {cdoms : List Expr} {cres : Expr}
    (_hcinst : Expr.instPisAt (fvs.take cnP ++ fvs.drop rP)
      (cvj.type.renameConsts f) = some (cdoms, cres))
    (_hclen : cres.getAppArgs.length = cnP + (mI - rP))
    {rdoms : List Expr} {rrest : Expr}
    (_hrinst : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
      = some (rdoms, rrest))
    {fvsP : List Expr} {restP : Expr}
    (_hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    {cdomsP : List Expr} {crestP : Expr}
    (_hcinstP : Expr.instPisAt (fvsP.take cnP) cvj.type
      = some (cdomsP, crestP))
    {xFvsP : List Expr} {ldoms : Expr}
    (_hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    (_hstripRhs : (rhsA.stripLams (rP + cnF)).isSome = true)
    {ldomsL : List Expr} {lrest2 : Expr}
    (_hinstLam : Expr.instLamsAt (fvsP ++ xFvsP) rhsA
      = some (ldomsL, lrest2))
    -- the walks (D6-refined quantified-context packs, `Decl.lean`)
    (_hdeIdx : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (_hdePre : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (_hdeFld : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    (_hdePars : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((fvsP.take cnP).map Expr.fvarTypeD) cdomsP)
    (_hdeLam : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL)
    (_hdeRhs : ∀ ψ' : Name → Nat, DefEqAtW μ envS mS.cval ψ' (rP + cnF)
      rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs))
    (_hsidesTy : ∀ ψ' : Name → Nat,
      IotaSidesTyR μ envS mS.cval ψ' (rP + cnF) αS lhsS rhsS),
    ∀ (φ : Name → Nat) (us : List Level), us.length = lps.length →
      ∃ RV, denoteClosed mS.cval envS φ
          (rhsA.instantiateLevelParams lps us) = some RV ∧
        ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List VExpr)
          (TV TVj restR restC : VExpr),
          xs.length = mI →
          ys.length = cnP + cnF →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj
            = Level.substFn φ cvj.levelParams
                (cvj.levelParams.map fun p => Level.subst lps us (.param p)) →
          (∀ i, i < cnP → i < mI →
            interp V ρ (ys.getD i default)
              = interp V ρ (xs.getD i default)) →
          IotaIndexPinV V ρ restC cnP mI rP xs →
          denoteClosed mS.cval envS φ
            (tyA.instantiateLevelParams lps us) = some TV →
          denoteClosed mS.cval envS φ
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            = some TVj →
          TeleFitV V ρ TV
            (xs ++ [VExpr.mkAppN
              (mS.cval ctor (Level.substFn φ cvj.levelParams usj)) ys])
            restR →
          TeleFitV V ρ TVj ys restC →
          interp V ρ
              (VExpr.mkAppN (mS.cval Rn (Level.substFn φ lps us))
                (xs ++ [VExpr.mkAppN
                  (mS.cval ctor (Level.substFn φ cvj.levelParams usj))
                  ys]))
            = interp V ρ
                (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)) ∧
          ((∀ a ∈ xs, AnnotOkV V ρ a) → (∀ b ∈ ys, AnnotOkV V ρ b) →
            AnnotOkV V ρ (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)))

/-- **The nested bottom** ([set] transpose of `IndBottomNestedTT` — the
risk-R1 detection point): the checked nested-auxiliary `iota_j` kit
yields the fired `RecRulesV` law of the stored `.nested` rule.  Deltas
against the plain statement mirror the TT pair exactly: no
`cnP ≤ rP`; the stored `lvls`/`pins` with their well-formedness; the
major pin up to display names against the stored instantiations; the
constructor walks at the level-instantiated renamed type; the pin
walk is a `TypedListW`; the conclusion's level premise is at the
stored `lvls` and its parameter premise is the value-quantified
`openRev`/`instRevChain` form (the §8.1-corrected shape). -/
def IndBottomNestedS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {envS : Env} (mS : EnvS V envS)
    {f : Name → Name} (_hro : RenameOkT mS.cval envS f)
    (_heqfE : envS.find? eqName = some eqA)
    {Rn : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    (_htyw : tyA.hasFvar = false)
    (_htyb : tyA.looseBVarsBounded 0 = true)
    {ciRm : ConstantInfo}
    (_hfRnE : envS.find? (f Rn) = some ciRm)
    (_hRmlps : ciRm.toConstantVal.levelParams = lps)
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    (_hctorE : envS.find? ctor = some (.ctorInfo cvj cnP cnF))
    {ciCm : ConstantInfo}
    (_hfCmE : envS.find? (f ctor) = some ciCm)
    (_hCmlps : ciCm.toConstantVal.levelParams = cvj.levelParams)
    (_hCw : cvj.type.hasFvar = false)
    (_hCb : cvj.type.looseBVarsBounded 0 = true)
    (_hClp : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    (_hrPmI : rP ≤ mI)
    {lvls : List Level} {pins : List Expr}
    (_hlvlsLen : lvls.length = cvj.levelParams.length)
    (_hpinsLen : pins.length = cnP)
    (_hpinsWf : ∀ p ∈ pins, p.hasFvar = false ∧
      p.looseBVarsBounded rP = true)
    {rhsA : Expr} (_hrhsw : rhsA.hasFvar = false)
    (_hrhsb : rhsA.looseBVarsBounded 0 = true)
    (_hrhsKey : ∀ ψ' : Name → Nat, ∃ Rv t,
      denoteClosed mS.cval envS ψ' rhsA = some Rv ∧
      ∀ ρ : Nat → V, AnnotOkV V ρ Rv ∧ interp V ρ Rv ∈ˢ interp V ρ t)
    {stmtTy : Expr} (_hSw : stmtTy.hasFvar = false)
    (_hSb : stmtTy.looseBVarsBounded 0 = true)
    (_hthm : ∀ ψ' : Name → Nat, ∃ t,
      denoteClosed mS.cval envS ψ' stmtTy = some t ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp V ρ t) ∧ AnnotOkV V ρ t)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    (_hopen : openPisAtFvars (rP + cnF) stmtTy 0 = some (fvs, tbody))
    (_hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (_hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (_hlhead : lhsS.getAppFn = Expr.const (f Rn) (lps.map .param))
    (_hlarity : lhsS.getAppArgs.length = mI + 1)
    (_hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (_hmaj : Expr.ErasedEq (lhsS.getAppArgs.getLastD (.bvar 0))
      (Expr.mkAppN (.const (f ctor) lvls)
        (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
          (p.renameConsts f)) ++ fvs.drop rP)))
    (_hCstripsHead : ∃ bsC0 cbody0 Dc usc,
      cvj.type.stripPis (cnP + cnF) = some (bsC0, cbody0) ∧
      cbody0.getAppFn = Expr.const Dc usc)
    {cdoms : List Expr} {cres : Expr}
    (_hcinst : Expr.instPisAt
      (pins.map (fun p => Expr.instSpine (fvs.take rP) (rP - 1)
        (p.renameConsts f)) ++ fvs.drop rP)
      ((cvj.type.instantiateLevelParams cvj.levelParams lvls).renameConsts
        f) = some (cdoms, cres))
    (_hclen : cres.getAppArgs.length = cnP + (mI - rP))
    {rdoms : List Expr} {rrest : Expr}
    (_hrinst : Expr.instPisAt (fvs.take rP) (tyA.renameConsts f)
      = some (rdoms, rrest))
    {fvsP : List Expr} {restP : Expr}
    (_hopenP : openPisAtFvars rP tyA 0 = some (fvsP, restP))
    {cdomsP : List Expr} {crestP : Expr}
    (_hcinstP : Expr.instPisAt
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1)))
      (cvj.type.instantiateLevelParams cvj.levelParams lvls)
      = some (cdomsP, crestP))
    {xFvsP : List Expr} {ldoms : Expr}
    (_hopenXP : openPisAtFvars cnF crestP rP = some (xFvsP, ldoms))
    (_hstripRhs : (rhsA.stripLams (rP + cnF)).isSome = true)
    {ldomsL : List Expr} {lrest2 : Expr}
    (_hinstLam : Expr.instLamsAt (fvsP ++ xFvsP) rhsA
      = some (ldomsL, lrest2))
    -- the pins' typed walk (the nested pack's `TypedListW`)
    (_hTypedP : ∀ ψ' : Name → Nat, TypedListW μ envS mS.cval ψ' (rP + cnF)
      (pins.map (Expr.instSpine (fvsP.take rP) (rP - 1))) cdomsP)
    (_hdeIdx : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((lhsS.getAppArgs.drop rP).take (mI - rP))
      (cres.getAppArgs.drop cnP))
    (_hdePre : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((fvs.take rP).map Expr.fvarTypeD) rdoms)
    (_hdeFld : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((fvs.drop rP).map Expr.fvarTypeD) (cdoms.drop cnP))
    (_hdeLam : ∀ ψ' : Name → Nat, DefEqListW μ envS mS.cval ψ' (rP + cnF)
      ((fvsP ++ xFvsP).map Expr.fvarTypeD) ldomsL)
    (_hdeRhs : ∀ ψ' : Name → Nat, DefEqAtW μ envS mS.cval ψ' (rP + cnF)
      rhsS (Expr.mkAppN (rhsA.renameConsts f) fvs))
    (_hsidesTy : ∀ ψ' : Name → Nat,
      IotaSidesTyR μ envS mS.cval ψ' (rP + cnF) αS lhsS rhsS),
    ∀ (φ : Name → Nat) (us : List Level), us.length = lps.length →
      ∃ RV, denoteClosed mS.cval envS φ
          (rhsA.instantiateLevelParams lps us) = some RV ∧
        ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List VExpr)
          (TV TVj restR restC : VExpr),
          xs.length = mI →
          ys.length = cnP + cnF →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj
            = Level.substFn φ cvj.levelParams (lvls.map (Level.subst lps us)) →
          (∀ i, i < cnP →
            ∀ vp : VExpr,
              denote mS.cval envS φ rP
                (openRev 0 rP
                  ((pins.getD i default).instantiateLevelParams lps us))
                = some vp →
              VExpr.bvarsBelow rP vp →
              interp V ρ (ys.getD i default)
                = interp V ρ (VExpr.instRevChain (xs.take rP) vp)) →
          IotaIndexPinV V ρ restC cnP mI rP xs →
          denoteClosed mS.cval envS φ
            (tyA.instantiateLevelParams lps us) = some TV →
          denoteClosed mS.cval envS φ
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            = some TVj →
          TeleFitV V ρ TV
            (xs ++ [VExpr.mkAppN
              (mS.cval ctor (Level.substFn φ cvj.levelParams usj)) ys])
            restR →
          TeleFitV V ρ TVj ys restC →
          interp V ρ
              (VExpr.mkAppN (mS.cval Rn (Level.substFn φ lps us))
                (xs ++ [VExpr.mkAppN
                  (mS.cval ctor (Level.substFn φ cvj.levelParams usj))
                  ys]))
            = interp V ρ
                (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)) ∧
          ((∀ a ∈ xs, AnnotOkV V ρ a) → (∀ b ∈ ys, AnnotOkV V ρ b) →
            AnnotOkV V ρ (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)))

/-- **The projection bottom** ([set] transpose of `IndBottomProjTT`):
the checked `proj_i.iota` theorem of a stored *degenerate* projection
recursor (`mI = rP`, `ctorParams = rP`, no indices) yields its fired
`RecRulesV` law.

Deltas against the plain statement — all forced by the projection
install running **different checks** (`checkProjShape`/`checkProjRule`/
`checkProjIota`, not `checkIotaThm`):

* no domain *walks*: the statement's telescope domains are the
  constructor's, **renamed** (`_hdomsSC`, `checkProjIota`'s
  `domsMatchAux`), and the rule λ-tower's domains are the
  constructor's on the nose (`_hrdomsEq`, `checkProjRule`'s), so the
  three contexts are identified syntactically (`towerCtxEq{,D}`)
  instead of by firing `DefEqListW`s;
* no rhs walk: the reduct is the λ-tower's β-contractum to the
  field's bound variable (`_hrhsAstrip`), read off by
  `projBodyValue`;
* consequently no `_hdePre`/`_hdeFld`/`_hdeRhs`/`_hdeIdx`/`_hdeLam`
  and no P-frame (`fvsP`/`xFvsP`) at all;
* **no `IotaSlotSorted`** either (the TT statement's one unsupplied
  premise): `fireS` recovers the equation slot's universe membership
  from the statement's own truthfulness plus `Eq`-former graph
  rigidity, exactly as in the plain bottom. -/
def IndBottomProjS (V : Type w) [SetTheory V] : Prop :=
  ∀ {μ : CheckMode} {envS : Env} (mS : EnvS V envS)
    {f : Name → Name} (_hro : RenameOkT mS.cval envS f)
    (_heqfE : envS.find? eqName = some eqA)
    {Rn : Name} {lps : List Name} {tyA : Expr} {mI rP : Nat}
    {ciRm : ConstantInfo}
    (_hfRnE : envS.find? (f Rn) = some ciRm)
    (_hRmlps : ciRm.toConstantVal.levelParams = lps)
    {ctor : Name} {cvj : ConstantVal} {cnP cnF : Nat}
    (_hctorE : envS.find? ctor = some (.ctorInfo cvj cnP cnF))
    {ciCm : ConstantInfo}
    (_hfCmE : envS.find? (f ctor) = some ciCm)
    (_hCmlps : ciCm.toConstantVal.levelParams = cvj.levelParams)
    (_hCw : cvj.type.hasFvar = false)
    (_hCb : cvj.type.looseBVarsBounded 0 = true)
    (_hClp : cvj.type.allLevelParamsDefined cvj.levelParams = true)
    -- the degenerate recursor's shape
    {i : Nat} (_hmIrP : mI = rP) (_hcnPrP : cnP = rP) (_hilt : i < cnF)
    -- `checkProjShape`: the constructor's telescope and residual
    {cbinders : List (Name × Expr × BinderMeta)} {cbody : Expr}
    (_hCstrip : cvj.type.stripPis (cnP + cnF) = some (cbinders, cbody))
    (_hcbodyArity : cbody.getAppArgs.length = cnP)
    {Dc : Name} {usc : List Level}
    (_hcbodyHead : cbody.getAppFn = Expr.const Dc usc)
    -- `checkProjRule`: the rule is the constructor telescope's
    -- λ-tower returning the field, with the constructor's domains
    {rhsA : Expr} (_hrhsw : rhsA.hasFvar = false)
    (_hrhsb : rhsA.looseBVarsBounded 0 = true)
    {rbinders : List (Name × Expr × BinderMeta)}
    (_hrhsAstrip : rhsA.stripLams (cnP + cnF)
      = some (rbinders, .bvar (cnF - 1 - i)))
    (_hrdomsEq : ∀ (i0 : Nat) (b b' : Name × Expr × BinderMeta),
      i0 < cnP + cnF → rbinders[i0]? = some b →
      cbinders[i0]? = some b' → b.2.1 = b'.2.1)
    (_hrhsKey : ∀ ψ' : Name → Nat, ∃ Rv t,
      denoteClosed mS.cval envS ψ' rhsA = some Rv ∧
      ∀ ρ : Nat → V, AnnotOkV V ρ Rv ∧ interp V ρ Rv ∈ˢ interp V ρ t)
    -- the checked statement's front doors and opened kit
    {stmtTy : Expr} (_hSw : stmtTy.hasFvar = false)
    (_hSb : stmtTy.looseBVarsBounded 0 = true)
    (_hthm : ∀ ψ' : Name → Nat, ∃ t,
      denoteClosed mS.cval envS ψ' stmtTy = some t ∧
      ∀ ρ : Nat → V, (∃ pv : V, pv ∈ˢ interp V ρ t) ∧ AnnotOkV V ρ t)
    {fvs : List Expr} {tbody : Expr} {ℓA : Level} {αS lhsS rhsS : Expr}
    (_hopen : openPisAtFvars (rP + cnF) stmtTy 0 = some (fvs, tbody))
    (_hheadEq : tbody.getAppFn = .const eqName [ℓA])
    (_hargs3 : tbody.getAppArgs = [αS, lhsS, rhsS])
    (_hlhead : lhsS.getAppFn = Expr.const (f Rn) (lps.map .param))
    (_hlarity : lhsS.getAppArgs.length = mI + 1)
    (_hlpre : lhsS.getAppArgs.take rP = fvs.take rP)
    (_hmaj : lhsS.getAppArgs.getLastD (.bvar 0) =
      Expr.mkAppN (.const (f ctor) (cvj.levelParams.map .param))
        (fvs.take cnP ++ fvs.drop rP))
    (_hrhsSpin : rhsS = fvs.getD (rP + i) default)
    -- `checkProjIota`: the statement's domains are the constructor's,
    -- renamed to the model side
    {sbinders : List (Name × Expr × BinderMeta)} {sbody : Expr}
    (_hSstrip : stmtTy.stripPis (cnP + cnF) = some (sbinders, sbody))
    (_hdomsSC : ∀ (i0 : Nat) (b b' : Name × Expr × BinderMeta),
      i0 < cnP + cnF → sbinders[i0]? = some b →
      cbinders[i0]? = some b' → b.2.1 = b'.2.1.renameConsts f)
    (_hsidesTy : ∀ ψ' : Name → Nat,
      IotaSidesTyR μ envS mS.cval ψ' (rP + cnF) αS lhsS rhsS),
    ∀ (φ : Name → Nat) (us : List Level), us.length = lps.length →
      ∃ RV, denoteClosed mS.cval envS φ
          (rhsA.instantiateLevelParams lps us) = some RV ∧
        ∀ (usj : List Level) (ρ : Nat → V) (xs ys : List VExpr)
          (TV TVj restR restC : VExpr),
          xs.length = mI →
          ys.length = cnP + cnF →
          usj.length = cvj.levelParams.length →
          Level.substFn φ cvj.levelParams usj
            = Level.substFn φ cvj.levelParams
                (cvj.levelParams.map fun p => Level.subst lps us (.param p)) →
          (∀ i, i < cnP → i < mI →
            interp V ρ (ys.getD i default)
              = interp V ρ (xs.getD i default)) →
          IotaIndexPinV V ρ restC cnP mI rP xs →
          denoteClosed mS.cval envS φ
            (tyA.instantiateLevelParams lps us) = some TV →
          denoteClosed mS.cval envS φ
            (cvj.type.instantiateLevelParams cvj.levelParams usj)
            = some TVj →
          TeleFitV V ρ TV
            (xs ++ [VExpr.mkAppN
              (mS.cval ctor (Level.substFn φ cvj.levelParams usj)) ys])
            restR →
          TeleFitV V ρ TVj ys restC →
          interp V ρ
              (VExpr.mkAppN (mS.cval Rn (Level.substFn φ lps us))
                (xs ++ [VExpr.mkAppN
                  (mS.cval ctor (Level.substFn φ cvj.levelParams usj))
                  ys]))
            = interp V ρ
                (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)) ∧
          ((∀ a ∈ xs, AnnotOkV V ρ a) → (∀ b ∈ ys, AnnotOkV V ρ b) →
            AnnotOkV V ρ (VExpr.mkAppN RV (xs.take rP ++ ys.drop cnP)))

end Setlec.SetR
