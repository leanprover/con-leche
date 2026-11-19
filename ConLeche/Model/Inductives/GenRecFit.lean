module

public import ConLeche.Model.Inductives.GenRecFitBase
public import ConLeche.Model.Inductives.BlockRecAssembly
public import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRuleFit
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockStageRec
import ConLeche.Model.Inductives.GenClsData
import ConLeche.Model.Inductives.StreamRecsSem
import ConLeche.Model.Inductives.NestedRecPins
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.RecRulesCons
import ConLeche.Model.IndPointKit
import ConLeche.Model.IndFrame
import ConLeche.Model.IndStageKit
import ConLeche.Model.OpenedCtx
import ConLeche.Model.Levels
import ConLeche.Verify.InstLevels
import ConLeche.Verify.Inductives.TargetAuxFire

public section

/-!
# The generated rules' forward fit (`RecRuleFit`)

`genRecFit_of`: the field `RecRuleFit` at every rule of the generated recursors' stage, from
its two statements at the constructors' environment (`GenFit1`, `GenFit2`,
`GenRecFitBase.lean`).  The reduction:

* the two reading binders are eliminated: the recursor type's reading at the recursors'
  environment is `blockRecTyAV` (`blockRuleTVa_run`), the constructor type's is
  `blockRecCtorTy` (the constructor is stored below the recursors, `blockRecDenote_cross`);
* the constructor's leaf is the constructors' environment's (`blockRecAcv_stored`);
* the rule's parameters, read at the recursors' environment, are read at the constructors'
  (`GenPs`): a member rule's are the prefix's, a nested rule's pins read as the class's
  parameters at the prefix (`genOutPinVal`);
* the constructor's level valuation is the class's on its level parameters (`GenLv`, from
  `recFireComparands`);
* the universe clause is the stored type's own inference: its conclusion after the major
  infers to the motive's sort (`storedMotive_sort`), which is the sort the stage checked the
  conclusion at (`blockRecConcl_univ`).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal BlockShape TargetMajor FEnv
  GenRecRun NestState)

universe w

variable {V : Type w} [SetTheory V]

/-! ## The universe clause -/

section Univ

variable {F : Nat} {envC : Env} {pp : BlockShape}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}

set_option maxHeartbeats 2000000 in
/-- **The universe clause of a stored recursor's fit**: a fit of all `mI + 1` binders of the
recursor type's reading has a residual in the motive's universe — the stored type's inference
infers its conclusion after the major to the motive's sort (`storedMotive_sort`), the sort the
stage checked the conclusion at (`blockRecConcl_univ`). -/
theorem blockRecFit_univ (mpC : EnvModelM V envC)
    (h : ConLeche.RecStageG .verified F envC pp rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) (φ : Name → Nat) (us : List Level)
    {ρ : Nat → V} {ws : List Term} {restR : Term}
    (hwl : ws.length = pp.majorIdxAt j + 1)
    (hfit : TeleFitPA V ρ
      (blockRecTyAV mpC.base2.acval envC rs (Level.substFn φ r.1.levelParams us) j) ws restR) :
    ∀ (pre idx : List Expr) (rest body : Expr) (u : Level),
      (r.1.type.instantiateLevelParams r.1.levelParams us).stripPis (pp.rulePrefixAt j)
        = some (pre, rest) →
      rest.stripPis (pp.majorIdxAt j - pp.rulePrefixAt j + 1) = some (idx, body) →
      ConLeche.motiveLevel? pre (pp.majorIdxAt j - pp.rulePrefixAt j) body = some u →
      interp V ρ restR ∈ˢ (univ (Level.eval φ u) : V) := by
  intro pre idx rest body u hpre hidx hu
  rw [Expr.stripPis_instantiateLevelParams] at hpre
  obtain ⟨⟨pre₀, rest₀⟩, hpre₀, hpe⟩ := Option.map_eq_some_iff.mp hpre
  simp only [Prod.mk.injEq] at hpe
  obtain ⟨rfl, rfl⟩ := hpe
  rw [Expr.stripPis_instantiateLevelParams] at hidx
  obtain ⟨⟨idx₀, body₀⟩, hidx₀, hie⟩ := Option.map_eq_some_iff.mp hidx
  simp only [Prod.mk.injEq] at hie
  obtain ⟨rfl, rfl⟩ := hie
  obtain ⟨u₀, hu₀, rfl⟩ := motiveLevel?_instantiateLevelParams _ _ hu
  rw [Level.eval_subst]
  generalize hψ : Level.substFn φ r.1.levelParams us = ψ at hfit ⊢
  -- the stored type's inference, and the stage's check of its conclusion
  obtain ⟨_, u, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  obtain ⟨st, -, hinf0, -⟩ := TE.hcv.sorted
  have hrP : pp.rulePrefixAt j ≤ pp.majorIdxAt j := by have := TE.hmI'; omega
  obtain ⟨hbt, -⟩ := storedMotive_sort hinf0 TE.hopen hrP hpre₀ hidx₀ hu₀
  have hsty : TE.sty = .sort u₀ := by
    have := TE.hsty
    rw [hbt] at this
    exact (Except.ok.inj this).symm
  have hsty' := TE.hu
  rw [hsty] at hsty'
  obtain rfl : u = u₀ := ensureSortCore_sort_eq hsty'
  -- the fit's residual is the conclusion at the fitted spine
  obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -⟩ := recStage_tyPis (V := V) mpC h hr ψ
  rw [hTyE] at hfit
  have htele := piTeleAV_of_stripPisAV (stripPisAV_mkPisAV
    (blockRecRdsAV mpC.base2.acval envC pp rs ψ j) (blockRecConclAV mpC.base2.acval envC pp rs ψ j))
  have hwl' : ws.length = (blockRecRdsAV mpC.base2.acval envC pp rs ψ j).length := by
    rw [hwl, hlenRds]
  rw [teleFitPA_rest_eq _ htele hwl' hfit, ← hwl', interp_instSeq]
  exact blockRecConcl_univ mpC h hr ψ TE.hopen TE.hsty TE.hu _
    (sat_of_tower htele hwl' (teleFitPA_to_chain _ htele hwl' hfit))

end Univ

/-! ## The reduction -/

section Reduce

variable {F : Nat} {env₁ envC : Env} {pp : BlockShape} {nestedBit : Bool} {pos : NestState}
  {block : List ConstantInfo} {out : List (ConstantVal × TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

set_option maxHeartbeats 4000000 in
/-- **The generated rules' `RecRuleFit`, from its two statements at the constructors'
environment** (see the module docstring). -/
theorem genRecFit_of
    (R : GenRecRun .verified F (ConLeche.mkFEnv env₁) env₁ (ConLeche.mkFEnv envC) pp nestedBit
      pos block out)
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    (hrdAll : ∀ c, c < (tgtRs out).length → pp.nP ≤ pp.rulePrefixAt c ∧
      ∃ cvI, GenClsRd mpC d Dc mc cvc pp out c cvI)
    (hseam : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        ∃ iT, envC.find? ctor.1.name
            = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2 iT) ∧
        ConstsBound envC ctor.1.type ∧
        ∀ ψ : Name → Nat,
          denote mpC.base2.acval envC ψ 0 ctor.1.type
            = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ))
    (h1 : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat),
      r.2.2.2[i]? = some ctor → GenFit1 mpC pp out j i ctor)
    (h2 : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat),
      r.2.2.2[i]? = some ctor → GenFit2 mpC pp out j i ctor)
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List Term} :
    AtStreamRules mpC (ConLeche.tgtRulesR pp (ConLeche.tgtMajorsOf out)) pp (tgtRs out) s eqs
      (ConLeche.tgtFireOf pp (ConLeche.tgtMajorsOf out))
      fun m₃ φ j r _ _ _ rl => RecRuleFit m₃ φ r.1 (pp.majorIdxAt j) (pp.rulePrefixAt j) rl := by
  intro m₃ hac φ j r hr i ctor rhs hctor _
  intro us hus TVa hTVa cvj cnP cnF iT hfc usj hlj hsj TVja hTVja ρ xs ps mid hxl hxw hmid hpw
    hps
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  -- the recursor type's reading
  obtain rfl := blockRuleTVa_run mpC h hac hr φ us hTVa
  -- the constructor, stored below the recursors
  obtain ⟨iT0, hfind0, hcb, hread⟩ := hseam j r hr i ctor hctor
  have hkeep := find?_consBlockRecsR_keep (R := ConLeche.tgtRulesR pp (ConLeche.tgtMajorsOf out))
    (q := pp) (fun r' hr' => recStage_cvFacts h r' hr') ctor.1.name _ hfind0
  have hfc' := hfc
  change (ConLeche.consBlockRecsR _ pp 0 (tgtRs out) envC).find? ctor.1.name = _ at hfc'
  rw [hkeep] at hfc'
  obtain ⟨rfl, rfl, rfl, rfl⟩ : ctor.1 = cvj ∧ (ConLeche.tgtMajorsOf out j).nPc = cnP ∧
      ctor.2 = cnF ∧ iT0 = iT := by
    injection hfc' with h'; injection h' with a b c e; exact ⟨a, b, c, e⟩
  -- the constructor type's reading
  rw [denote_instLevels m₃.acval_params φ,
    blockRecDenote_cross h hac _ 0 _ hcb (hread _)] at hTVja
  obtain rfl := Option.some.inj hTVja
  have hstored : m₃.acval ctor.1.name = mpC.base2.acval ctor.1.name :=
    blockRecAcv_stored h hac (by rw [hfind0]; rfl)
  have hcAM : (tgtMajor out j).ctors[i]? = some ctor := by rw [← tgtRs_ctors hr]; exact hctor
  have hMM : (ConLeche.tgtMajorsOf out j).nPc = (tgtMajor out j).nPc := rfl
  -- the level valuation and the parameters, at the constructors' environment
  have hLP : GenLv out (Level.substFn φ r.1.levelParams us)
        (Level.substFn φ ctor.1.levelParams usj) j ctor ∧
      GenPs mpC pp out (Level.substFn φ r.1.levelParams us) ρ j xs ps := by
    obtain ⟨hpl, hpr⟩ := hps
    cases hmb : (tgtMajor out j).member with
    | some t =>
      have hmb' : (ConLeche.tgtMajorsOf out j).member = some t := hmb
      have hplain : ConLeche.tgtFireOf pp (ConLeche.tgtMajorsOf out) j r = .plain := by
        simp only [ConLeche.tgtFireOf, hmb']
      have hplain' : ConLeche.RecRule.fire (ConLeche.RecRule.mk ctor.1.name ctor.2
          (ConLeche.tgtFireOf pp (ConLeche.tgtMajorsOf out) j r) rhs) = .plain := hplain
      have hag := blockRuleLevelAgree hplain' hsj
      refine ⟨fun q hq => ?_, hpl, fun q hq => ?_⟩
      · simp only [hmb, Option.isSome_some, ite_true]; exact hag q hq
      · have := hpr q hq
        simp only [hplain] at this
        simp only [hmb, Option.isSome_some, ite_true]; exact this
    | none =>
      have hmb' : (ConLeche.tgtMajorsOf out j).member = none := hmb
      have hf := ConLeche.tgtFireOf_of_out (q := pp) r hmb'
      obtain ⟨-, cvI, Rd⟩ := hrdAll j hj
      obtain ⟨hlvls, hpv⟩ := genOutPinVal R h hr Rd hf φ us
      have hsyn := R.fire_nestedRead hr hf
      obtain ⟨-, -, hpinsWf, -, -, -, -, -, -, -, hplen⟩ := hsyn
      obtain ⟨-, -, hlpsI, -⟩ := Rd.hctor i ctor hcAM
      refine ⟨fun q hq => ?_, hpl, fun q hq => ?_⟩
      · simp only [hmb, Option.isSome_none, Bool.false_eq_true, ite_false]
        rw [hsj]
        simp only [ConLeche.recFireComparands, hf]
        exact Level.substFn_map_subst (by show (tgtMajor out j).lvls.length = _; rw [Rd.hul, hlpsI]) hq
      · simp only [hmb, Option.isSome_none, Bool.false_eq_true, ite_false]
        obtain ⟨vpa, hvpa, hch⟩ := hpv q hq
        have hpr' := hpr q hq
        simp only [hf] at hpr'
        have hqm : ((tgtMajor out j).ds.map
            (Expr.abstractPrefix (pp.rulePrefixAt j) 0)).getD q default
              ∈ (tgtMajor out j).ds.map (Expr.abstractPrefix (pp.rulePrefixAt j) 0) := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by
            rw [List.length_map, ← Rd.hnpc]; exact hq)]
          exact List.getElem_mem _
        obtain ⟨-, -, hpR, -⟩ := hpinsWf _ hqm
        rw [openRev_instantiateLevelParams, denote_instLevels mpC.base2.acval_params φ] at hvpa
        have hvpa3 := blockRecDenote_cross h hac _ _ _
          (constsBound_openRev (constsBound_of_constsResolve _ hpR) 0 _) hvpa
        rw [← denote_instLevels m₃.acval_params φ, ← openRev_instantiateLevelParams] at hvpa3
        rw [hpr' vpa hvpa3, hch ρ xs hxl]
  obtain ⟨hlv, hps'⟩ := hLP
  refine ⟨fun _ _ _ _ => h1 j r hr i ctor hctor _ _ hlv ρ xs ps mid hxl hxw hmid hpw hps',
    fun fs is restC hfl hil hfw hiw hfit hpin => ?_⟩
  obtain ⟨restR, hR⟩ := h2 j r hr i ctor hctor _ _ hlv ρ xs ps mid hxl hxw hmid hpw hps' fs is
    restC hfl hil hfw hiw hfit hpin
  refine ⟨restR, by rw [hstored]; exact hR, fun pre idx rest body u hpre hidx hu =>
    blockRecFit_univ mpC h hr φ us (by simp [hxl, hil]; have := blockRecHrPle (p := pp) h hj; omega) hR pre idx rest body u hpre
      hidx hu⟩

end Reduce

end ConLeche.Model
