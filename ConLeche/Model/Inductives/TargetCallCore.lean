module

public import ConLeche.Model.Inductives.TargetIhData
import ConLeche.Model.Inductives.TargetResidue
import ConLeche.Model.Inductives.BlockDeclRun

public section

/-!
# A target call's target, at a valuation of the holes (lane RECLIB, B3 (e) + B4)

The target check types every recursive call on the member-ABSTRACTED
terms (`targetCallOk`, K1): at the rule frame extended by the block's
member HOLES (`targetHoles`, after the prefix and the fields), the
field's abstract type through whnf (`fnorm`) is defeq to
`∀ a⃗, hole_m x⃗ e⃗` (`hdeq`), whose body was inferred (`hwant`).  So at
EVERY valuation of the holes satisfying their types (each hole at its
member former's type), a field lying in its abstract type's reading has
its call target in the hole's family: the index readings fit the
member's index telescope at the parameters, and the applied field lies
in the hole applied to them.

`tgtCall_core` states that once, at a hole valuation `hv` with a
member-application law (`hlaw`: the hole of the callee's member, applied
to the parameters and a fitting index spine, is `Y` at the index
tuple).  Its two instances:

* the CARRIER — `hv` the member constants' own values, `hlaw` the lfp
  clause's leaf, `hii` the concrete field fit (the abstraction read at
  the constants' values is the concrete term): the call target is a
  MAJOR (`TargetRowCall.lean`);
* the SEPARATED tuple — `hv` the clause's hole values (`holeVal`),
  `hlaw` `holeVal_app`, `hii` the hole fit at it: the call target lies
  in the property (`TargetRowInd.lean`, B4).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.SetTheory
open ConLeche.SetTheory.Tower
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo FEnv BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Core

variable {F : Nat} {fe : FEnv} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {nested : Bool} {blk : List ConstantInfo}
  {out : List (ConstantVal × TargetMajor × List Expr)} {mpC : EnvModelM V μ fe.env}
  {names : List Name} {d : BlockData V}
  {isRec : Bool} {A : Nat → (Name → Nat) → AnnotTerm}
  {fssZ : (Name → Nat) → Nat → List (List AnnotTerm)} {envI : Env}

/-- **A target call's target, at a valuation of the holes.**  At the
`(c, j)`-th rule, a frame the prefix and the fields fit (`hsp`), a
valuation `hv` of the member holes at their formers' types (`hvTy`),
under which the callee's member hole applied to the parameters and a
fitting index spine is `Y` at the index tuple (`hlaw`), and in which the
called field lies in its member-abstracted type's reading (`hii`): at
every spine `bs` of the call's telescope, the call's index readings
form an index tuple of the callee's member and the applied field lies
in `Y` there. -/
theorem tgtCall_core (hμ : μ.verifiedChecks = true)
    (h : ConLeche.checkBlockRecK (ConLeche.fueledOps μ F) fe.env pp cvTas ctorsAs
      = .ok (tgtRs out))
    (R : ConLeche.TargetRecRun μ F fe pp.toBlockShape nested blk cvTas ctorsAs out)
    (hkLen : ∀ (c : Nat) (ctorsA : List (ConstantVal × Nat)), ctorsAs[c]? = some ctorsA →
      (pp.kinds.getD c []).length = ctorsA.length)
    (hdR : ∃ (env₀ : Env) (pk : Nat → BlockMemberPick) (uOfD : Nat → (Name → Nat) → Nat)
        (ppsOf : Nat → (Name → Nat) → List (Nat × Nat × AnnotTerm)),
      d = blockDataOf V pp.toBlockShape env₀ ctorsAs pp.kinds pk uOfD ppsOf)
    (hN : BlockNamesOk (V := V) d cvTas)
    (hS : BlockCtorsStage (V := V) μ F d pp.lps cvTas pp.toBlockShape isRec A fssZ envI
      pp.ctorNamesAt)
    (hcore : BlockCtorsCore mpC.base2 d pp.lps cvTas pp.toBlockShape isRec A d.k)
    (hmr : BlockMembersRun mpC.base2 d pp.toBlockShape cvTas)
    (hM : BlockModelAt mpC.base2 names d)
    (ψ : Name → Nat) (ρ : Nat → V) {c j : Nat} (hc : c < (tgtRs out).length)
    (hj : j < blockRecNCt (tgtRs out) c) {xs fs : List V}
    (hsp : SpineFit ρ (blockRulePdomsAV mpC.base2.acval fe.env pp.toBlockShape (tgtRs out) ψ c
      ++ blockRuleFdomsAV pp.toBlockShape (tgtRs out) mpC.base2.acval fe.env ψ c j) (xs ++ fs))
    {r : Nat}
    (hr : r < (tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).length)
    (hv : List V) (hvl : hv.length = cvTas.length)
    (hvTy : ∀ t, t < cvTas.length → ∃ T : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ 0 (cvTas.getD t default).type = some T ∧
      hv.getD t pt ∈ˢ interp V ρ T)
    (Y : V)
    (hlaw : ∀ is : List V,
      SpineFit (consList (xs.take d.nP) ρ)
        (d.IdsM (pp.toBlockShape.recTgtAt
          ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD r
            default).callee) ψ) is →
      (xs.take d.nP ++ is).foldl SetTheory.app
          (hv.getD (pp.toBlockShape.recTgtAt
            ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD r
              default).callee) pt)
        = app Y (d.tup ψ (pp.toBlockShape.recTgtAt
            ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD r
              default).callee) is))
    (hii : ∀ Aty : AnnotTerm,
      denoteMeta mpC.base2.acval fe.env ψ
          (tgtB pp.toBlockShape (tgtRs out) c j + cvTas.length)
          (tgtAbsM pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j
            ((tgtFieldFvs pp.toBlockShape (tgtRs out) c j).getD
              ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD r
                default).field default).fvarTypeD) = some Aty →
      fs.getD ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD r
          default).field pt
        ∈ˢ interp V (consList (xs ++ fs ++ hv) ρ) Aty)
    (bs : List V)
    (hbs : SpineFit (consList (xs ++ fs) ρ)
      ((tgtTlA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env ψ
        c j r).map (·.2.2)) bs) :
    d.tup ψ (pp.toBlockShape.recTgtAt
        ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD r
          default).callee)
      ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env
        ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ))))
      ∈ˢ d.idx ψ (consList (xs.take d.nP) ρ) (pp.toBlockShape.recTgtAt
        ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD r
          default).callee) ∧
    interp V (consList bs (consList (xs ++ fs) ρ))
        (tgtFapA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval fe.env
          ψ c j r)
      ∈ˢ app Y (d.tup ψ (pp.toBlockShape.recTgtAt
        ((tgtIhL μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) c j).getD r
          default).callee)
        ((tgtEisA μ F fe pp.toBlockShape (cvTas.map (·.type)) (tgtRs out) mpC.base2.acval
          fe.env ψ c j r).map (interp V (consList bs (consList (xs ++ fs) ρ))))) := by
  sorry

end Core

end ConLeche.Model
