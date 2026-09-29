module

public import ConLeche.Model.Inductives.BlockRecAssembly
public import ConLeche.Model.Inductives.BlockRecLaw
public import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Capstone
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.Inductives.NestedRuleSyn
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Verify.InstSpine
import ConLeche.Verify.AbstractRange
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.InstLevels
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.BinderLoop
import ConLeche.Verify.Extend.Inversions
import ConLeche.Model.Inductives.NestedRecPins
import ConLeche.Model.Inductives.NestedRecRest
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.ClassGenMinor
import ConLeche.Model.IndPinGrade
import ConLeche.Model.IndOpenRev
import ConLeche.Model.IndFrame
import ConLeche.Model.RecRulesCons
import ConLeche.Model.Levels
import ConLeche.Model.Tiers
import ConLeche.Model.WellDenotedTransport
import ConLeche.Semantics.Tower.SumTower

public section

/-!
# The `.nested` pins' law, off the stored recursor type alone

`recStagePinsOk`: `RecRulePinsOk` at every stored rule of ANY recursor
stage (`RecStageG`) whose rules fire by `tgtFireOf` — in particular the
GENERATED stage (`genRecStage`'s `hpins`).  A `.nested` firing is an
outside major's; its pins are the stored type's major-domain parameters
closed over the rule prefix (`nestedRuleSyn_open`), so what the law asks
is that each parameter's reading is graded at every prefix spine.

That grading comes from the stored type's OWN inference
(`checkConstantVal`): inferring the telescope infers the major's domain
at the major's depth `mI`, hence every argument of it
(`storedMajorArg_graded`).  The argument mentions only prefix openers, so
its typing claim is taken in a context whose index positions are
replaced by the always-inhabited `Sort 0` — a prefix spine then always
extends to a context spine, and the grading comes back down to the
prefix by lifting.  (The stored index domains themselves may be empty:
the stored type's own grading says nothing below them.)
-/

namespace ConLeche

variable {mode : CheckMode}

/-- **An inferred application infers its arguments.** -/
theorem inferTypeCore_mkAppN_args {env : Env} {F d : Nat} :
    ∀ (as : List Expr) {f t : Expr},
      inferTypeCore mode env F d (Expr.mkAppN f as) = .ok t →
      ∀ a ∈ as, ∃ ta, inferTypeCore mode env F d a = .ok ta
  | [], _, _, _, a, ha => nomatch ha
  | b :: as, f, t, h, a, ha => by
    rcases List.mem_cons.mp ha with rfl | ha
    · obtain ⟨tfa, hfa⟩ := Model.inferTypeCore_mkAppN_fn_inv as (f := .app f a) h
      obtain ⟨-, -, -, -, -, -, -, ta, hta, -⟩ := inferTypeCore_app_inv' hfa
      exact ⟨ta, hta⟩
    · exact inferTypeCore_mkAppN_args as (f := .app f b) h a ha

/-- **An inferred `∀` infers its domain.** -/
theorem inferTypeCore_forallE_dom {env : Env} {F d : Nat} {ty bd s : Expr} {mb : BinderMeta}
    (h : inferTypeCore mode env F d (.forallE ty bd mb) = .ok s) :
    ∃ t, inferTypeCore mode env F d ty = .ok t := by
  cases F with
  | zero => rw [inferTypeCore_zero] at h; exact nomatch h
  | succ F₀ =>
    rw [inferTypeCore_forallE_eq] at h
    obtain ⟨tty, htty, -⟩ := exceptBind_ok h
    exact ⟨tty, inferTypeCore_mono (Nat.le_succ _) htty⟩

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- A spine of `truthVal True`s fits a run of `Sort 0`s. -/
theorem spineFit_replicate_sort0 (σ : Nat → V) :
    ∀ k : Nat, SpineFit σ (List.replicate k (.sort 0 : AnnotTerm))
      (List.replicate k (truthVal True : V))
  | 0 => trivial
  | k + 1 => ⟨by simpa using truthVal_mem_univ (V := V) True 0, spineFit_replicate_sort0 _ k⟩

section Pins

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))} {memR : Nat → Prop}

set_option maxHeartbeats 2000000 in
/-- **A stored major-domain argument over the prefix is graded at every
prefix spine** — from the stored type's own inference (see the module
docstring). -/
theorem storedMajorArg_graded (hμ : μ.verifiedChecks = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageG μ F envC pp cvTas ctorsAs rs memR)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) (ψ : Name → Nat) {fvs : List Expr} {concl maj : Expr}
    (hop : openPisAtFvars (pp.toBlockShape.majorIdxAt j + 1) r.1.type 0 = some (fvs, concl))
    (hmaj : fvs[pp.toBlockShape.majorIdxAt j]? = some maj)
    {x : Expr} (hxA : x ∈ maj.fvarTypeD.getAppArgs)
    (hlt : ∀ l ∈ x.fvarLeaves, l.1 < pp.toBlockShape.rulePrefixAt j) :
    ∃ w, denoteMeta mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j) x = some w ∧
      ∀ σ : Nat → V,
        Sat V (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j).reverse σ →
        WellDenotedV V σ w := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  generalize hmIdef : pp.toBlockShape.majorIdxAt j = mI at hop hmaj
  generalize hrPdef : pp.toBlockShape.rulePrefixAt j = rP at hlt ⊢
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  have hle : rP ≤ mI := by have := TE.hmI'; omega
  obtain ⟨-, -, -, -, -, -, tyA, stype, u0, -, -, -, hinfT, -, hcv'⟩ :=
    ConLeche.checkConstantVal_inv TE.hcv
  have hrty : r.1.type = tyA := by rw [hcv']
  obtain ⟨hw0, hb0⟩ := recStage_tyClosed h hr
  -- the major's domain, inferred at `mI`
  obtain ⟨fvsA, fvsB, o₀, hA, hB, hfe⟩ := openPisAtFvars_split mI (m := 1) hop
  obtain ⟨dom, bd, mb, rfl⟩ : ∃ dom bd mb, o₀ = .forallE dom bd mb := by
    match o₀, hB with
    | .forallE dom bd mb, _ => exact ⟨dom, bd, mb, rfl⟩
  have hAlen : fvsA.length = mI := ConLeche.Verify.openPisAtFvars_length _ hA
  have hmajE : maj = .fvar mI dom := by
    simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hB
    obtain ⟨rfl, -⟩ := hB
    rw [hfe, List.getElem?_append_right (by omega), hAlen, Nat.sub_self] at hmaj
    simpa using hmaj.symm
  have hdomInf : ∃ t, ConLeche.inferTypeCore .verified envC F mI dom = .ok t := by
    rw [hrty] at hA
    cases mI with
    | zero =>
      simp only [openPisAtFvars, Option.some.injEq, Prod.mk.injEq] at hA
      obtain ⟨-, rfl⟩ := hA
      exact ConLeche.inferTypeCore_forallE_dom hinfT
    | succ n =>
      obtain ⟨bt, -, hbt, -⟩ := inferTypeCore_openPis_body rfl n hA hinfT
      rw [Nat.zero_add] at hbt
      exact ConLeche.inferTypeCore_forallE_dom hbt
  obtain ⟨tdom, htdom⟩ := hdomInf
  rw [hmajE] at hxA
  simp only [Expr.fvarTypeD] at hxA
  obtain ⟨tx, htx⟩ := ConLeche.inferTypeCore_mkAppN_args _ (f := dom.getAppFn)
    (by rw [ConLeche.Expr.mkAppN_getApp]; exact htdom) x hxA
  -- the argument's scoping: an opener's type's argument, its leaves prefix openers
  have hwsDom : Expr.WScoped mI dom := by
    have := openPisAtFvars_typeWScoped (mI + 1) hop hw0 mI maj hmaj
    rw [hmajE, Nat.zero_add] at this; exact this
  have hwsX : Expr.WScoped mI x := wscoped_of_getAppArgs hwsDom x hxA
  have hbFvs := (openPisAtFvars_bounded _ hop hb0).2
  have hbDom : dom.looseBVarsBounded 0 = true := by
    have := hbFvs maj (List.mem_of_getElem? hmaj); rw [hmajE] at this; exact this
  have hbX : x.looseBVarsBounded 0 = true := ConLeche.looseBVarsBounded_getAppArgs hbDom x hxA
  have hnil : r.1.type.fvarLeaves = [] := fvarLeaves_nil_of_wscoped_zero hw0
  have hleafF : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    have hlD : l ∈ dom.fvarLeaves := ConLeche.fvarLeaves_getAppArgs hxA l hl
    have hlM : l ∈ maj.fvarLeaves := by
      rw [hmajE]; simp only [Expr.fvarLeaves, List.mem_cons]; exact Or.inr hlD
    rcases openPisAtFvars_leaves _ hop l (Or.inr ⟨maj, List.mem_of_getElem? hmaj, hlM⟩) with
      h' | h'
    · rw [hnil] at h'; exact nomatch h'
    · exact h'
  -- the prefix openers
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix rP (mI + 1) r.1.type 0 (by omega) hop
  have hleafP : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs.take rP := by
    intro l hl
    obtain ⟨pos, hpos⟩ := List.getElem?_of_mem (hleafF l hl)
    obtain ⟨ty', hty'⟩ := ConLeche.openPisAtFvars_index _ _ _ hop pos _ hpos
    have h1 : l.1 = pos := by injection hty' with a b; omega
    have hpt : (fvs.take rP)[pos]? = some (Expr.fvar l.1 l.2) := by
      rw [List.getElem?_take, if_pos (show pos < rP by have := hlt l hl; omega)]; exact hpos
    exact List.mem_of_getElem? hpt
  have hLX : Expr.LeavesBounded x :=
    leavesBounded_of_openers (fun y hy => hbFvs y (List.mem_of_mem_take hy)) hleafP
  -- the recursor type's reading: its prefix domains
  obtain ⟨fvs', concl', hop', -, hTyE, hlenRds, -, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) rfl mpC h hr ψ
  rw [hmIdef] at hop' hlenRds
  obtain ⟨hff, -⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans hop))
  rw [hff] at hdomsR
  generalize hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j = pdoms
  have hPdE : pdoms = ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape rs ψ j).take
      rP).map (·.2.2) := by
    rw [← hPd, blockRulePdomsAV, hrPdef]
  have hlenPd : pdoms.length = rP := by
    rw [hPdE, List.length_map, List.length_take, hlenRds]; omega
  have hAa : ∀ i, i < rP → ∀ y, fvs[i]? = some y →
      denoteMeta mpC.base2.acval envC ψ i (Expr.fvarTypeD y) = some (pdoms.getD i default) := by
    intro i hi y hy
    obtain ⟨pd, hpd, -, hrd⟩ := hdomsR i y hy
    rw [hrd, hPdE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_take,
      if_pos hi, hpd]
    rfl
  have hokTower : ∀ l, l < rP → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((pdoms ++ [] ++ []).take l) ys →
      WellDenotedV V (consList ys σ) ((pdoms ++ [] ++ []).getD l default) := by
    intro l hl σ ys hys
    simp only [List.append_nil] at hys ⊢
    rw [hPdE] at hys ⊢
    exact prefixDoms_graded_of_tower
      (cc := blockRecConclAV mpC.base2.acval envC pp.toBlockShape rs ψ j)
      (by rw [hlenRds]; omega) (fun ρ' => by rw [← hTyE]; exact hwdTy ρ') hl hys
  have hokΔ := blockRuleHokΔ_of (V := V) (pdoms := pdoms) (fdoms := []) (ihdoms := [])
    (nF := 0) (nR := 0) hlenPd rfl rfl (by simpa using hokTower)
  simp only [List.reverse_nil, List.append_nil, List.nil_append, Nat.add_zero] at hokΔ
  -- the context at `mI`: the prefix, then `Sort 0` at every index position
  generalize hk : mI - rP = k
  have hmIk : mI = rP + k := by omega
  let Δa : List AnnotTerm := List.replicate k (.sort 0) ++ pdoms.reverse
  have hΔlen : Δa.length = mI := by simp [Δa, hlenPd]; omega
  have hent : ∀ i, i < rP → Δa[mI - 1 - i]? = some (pdoms.getD i default) := by
    intro i hi
    simp only [Δa]
    rw [List.getElem?_append_right (by simp; omega), List.length_replicate,
      List.getElem?_reverse (by omega), hlenPd,
      show rP - 1 - (mI - 1 - i - k) = i from by omega, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem (by omega)]
    rfl
  have hwsP := (ConLeche.openPisAtFvars_WScoped _ _ 0 hopP hw0).1
  rw [Nat.zero_add] at hwsP
  have hCE : CtxOk mpC.base2 ψ mI Δa x :=
    ctxOk_of_openers mpC.base2.acval_closed (Aa := fun i => pdoms.getD i default) hΔlen
      (fun i y hy => by simpa using ConLeche.openPisAtFvars_index _ _ _ hopP i y hy)
      (fun y hy => (hwsP y hy).mono (by omega))
      (fun i y hy => by
        have hi : i < rP := by
          have := (List.getElem?_eq_some_iff.mp hy).1
          rw [List.length_take] at this; omega
        rw [List.getElem?_take, if_pos hi] at hy
        exact hAa i hi y hy)
      hleafP hlt hent
      (fun i hi ρ hρ => by
        have hs := Sat_drop hρ k
        have hdrop : Δa.drop k = pdoms.reverse := by
          simp only [Δa]; rw [List.drop_append_of_le_length (by simp), List.drop_replicate]
          simp
        rw [hdrop] at hs
        have hq := hokΔ i hi _ hs
        rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), hlenPd,
          show rP - 1 - (rP - 1 - i) = i from by omega] at hq
        rw [show (fun j => ρ (j + (mI - 1 - i) + 1))
            = (fun j => (fun j => ρ (j + k)) (j + (rP - 1 - i) + 1)) from by
          funext j; congr 1; omega]
        exact hq)
  -- its reading, graded
  have htx' : ConLeche.inferTypeCore .verified envC F mI x = .ok tx := htx
  obtain ⟨wa, hwa⟩ := acceptedReads_of mpC.base2 ψ htx' hwsX hbX hLX
  obtain ⟨-, -, -, -, hgr, -⟩ :=
    Rules.infer_sound (Rules.RulesInputs.ofSem mpC ψ) (Rules.inferTypeCore_bridge htx')
      ⟨hwsX, hbX, hLX⟩ hCE hwa
  -- the reading at the prefix
  have hwsR : Expr.WScoped rP x := ConLeche.WScoped.of_leaves_below hwsX hlt
  have hlift := denoteMeta_lift (env := envC) (φ := ψ) mpC.base2.acval_closed hwsR mI hle
  rw [hwa] at hlift
  obtain ⟨w, hw, rfl⟩ : ∃ w, denoteMeta mpC.base2.acval envC ψ rP x = some w ∧
      wa = w.liftN (mI - rP) 0 := by
    cases h0 : denoteMeta mpC.base2.acval envC ψ rP x with
    | none => rw [h0] at hlift; exact nomatch hlift
    | some w => rw [h0] at hlift; exact ⟨w, rfl, Option.some.inj hlift⟩
  refine ⟨w, hw, fun σ hσ => ?_⟩
  have hsat : Sat V Δa (consList (List.replicate k (truthVal True : V)) σ) := by
    have := sat_of_spineFit (Δ₀ := pdoms.reverse) hσ (spineFit_replicate_sort0 σ k)
    simpa [Δa] using this
  have hg := hgr _ hsat
  rw [hk, WellDenotedV_liftN, shiftE_zero_consList (by simp)] at hg
  exact hg

end Pins

end ConLeche.Model
