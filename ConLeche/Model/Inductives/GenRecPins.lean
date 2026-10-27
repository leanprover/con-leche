module

import ConLeche.Model.Inductives.BlockRecAssembly
import ConLeche.Model.Inductives.BlockRecLaw
public import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Capstone
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.Inductives.RecStage
import ConLeche.Verify.Inductives.TargetAuxFire
import ConLeche.Verify.Inductives.NestedRead
import ConLeche.Verify.Inductives.ClassGenMinorSyn
import ConLeche.Verify.InstSpine
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.Denote.IndFrame
import ConLeche.Verify.BridgeWfImp
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.BinderLoop
import ConLeche.Model.Inductives.NestedRecPins
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.BlockRecMem
import ConLeche.Model.Inductives.BlockRecPreRun
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.IndPinGrade
import ConLeche.Model.IndOpenRev
import ConLeche.Model.IndFrame
import ConLeche.Model.RecRulesCons
import ConLeche.Model.Levels
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Tiers
import ConLeche.Model.WellDenotedTransport
import ConLeche.Semantics.Tower.SumTower

public section

/-!
# The `.nested` pins' law, off the stored recursor type alone

`recStagePinsOk`: `RecRulePinsOk` at every stored rule of ANY recursor
stage (`RecStageG`) whose rules fire by `tgtFireOf` — in particular the
GENERATED stage (`genRecStage`'s `hpins`), given that a `.nested` firing
reads off the stored type (`NestedRead`).  Its pins are then the stored
type's major-domain parameters closed over the rule prefix
(`nestedRead_open`), so what the law asks
is that each parameter's reading is graded at every prefix spine.

That grading comes from the stored type's OWN inference
(`checkConstantVal`): inferring the telescope infers the major's domain
at the major's depth `mI`, hence every argument of it
(`storedMajorArg_graded`).  The argument mentions only prefix openers, so
it is scoped at the prefix depth, where it infers alike, and its typing
claim is taken in the prefix context itself (`storedMajorSub_ctx`) — no
spine of the stored index domains, which may be empty, is needed.
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
      obtain ⟨_tf, _ty, body', _h1, _h2, _h3, hrest⟩ := inferTypeCore_app_inv' hfa
      rcases hrest with hsk | ⟨ta, hta, -⟩
      · obtain ⟨F₀, rfl⟩ : ∃ F₀, F = F₀ + 1 := by
          cases F with
          | zero => rw [inferTypeCore_zero] at hfa; exact nomatch hfa
          | succ F₀ => exact ⟨F₀, rfl⟩
        exact inferTypeCore_bvSkip_arg hsk
      · exact ⟨ta, hta⟩
    · exact inferTypeCore_mkAppN_args as (f := .app f b) h a ha

/-- **An inferred `∀` infers its domain.** -/
theorem inferTypeCore_forallE_dom' {env : Env} {F d : Nat} {ty bd s : Expr}
    (h : inferTypeCore mode env F d (.forallE ty bd) = .ok s) :
    ∃ t, inferTypeCore mode env F d ty = .ok t := by
  cases F with
  | zero => rw [inferTypeCore_zero] at h; exact nomatch h
  | succ F₀ =>
    rw [inferTypeCore_forallE_eq] at h
    obtain ⟨tty, htty, -⟩ := exceptBind_ok h
    exact ⟨tty, inferTypeCore_mono (Nat.le_succ _) htty⟩

/-- **A term whose prefix abstraction is closed is scoped at the prefix**:
abstracting `fvar 0 … n-1` away leaves no free variable only if every
free variable (outside the annotations, which are scoped below their
own index) is below `n`. -/
theorem WScoped.of_abstractRange_noFvar {n : Nat} :
    ∀ {e : Expr} {D c : Nat}, Expr.WScoped D e → (e.abstractRange 0 n c).hasFvar = false →
      Expr.WScoped n e := by
  intro e
  induction e with
  | bvar i => intro D c _ _; simp [Expr.WScoped]
  | fvar idx ty _ =>
    intro D c hw hf
    simp only [Expr.WScoped] at hw ⊢
    simp only [Expr.abstractRange] at hf
    by_cases hi : 0 ≤ idx ∧ idx < 0 + n
    · exact ⟨by omega, hw.2⟩
    · rw [ite_eq_right hi] at hf; simp [Expr.hasFvar] at hf
  | sort u => intro D c _ _; simp [Expr.WScoped]
  | const n us => intro D c _ _; simp [Expr.WScoped]
  | lit l => intro D c _ _; simp [Expr.WScoped]
  | app f a ihf iha =>
    intro D c hw hf
    simp only [Expr.WScoped] at hw ⊢
    simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact ⟨ihf hw.1 hf.1, iha hw.2 hf.2⟩
  | lam ty b iht ihb =>
    intro D c hw hf
    simp only [Expr.WScoped] at hw ⊢
    simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact ⟨iht hw.1 hf.1, ihb hw.2 hf.2⟩
  | forallE ty b iht ihb =>
    intro D c hw hf
    simp only [Expr.WScoped] at hw ⊢
    simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact ⟨iht hw.1 hf.1, ihb hw.2 hf.2⟩
  | letE ty v b iht ihv ihb =>
    intro D c hw hf
    simp only [Expr.WScoped] at hw ⊢
    simp only [Expr.abstractRange, Expr.hasFvar, Bool.or_eq_false_iff] at hf
    exact ⟨iht hw.1 hf.1.1, ihv hw.2.1 hf.1.2, ihb hw.2.2 hf.2⟩
  | proj sn i e ih =>
    intro D c hw hf
    simp only [Expr.WScoped] at hw ⊢
    simp only [Expr.abstractRange, Expr.hasFvar] at hf
    exact ih hw hf

end ConLeche

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open SetTheory
open ConLeche.Term ConLeche.Verify

open ConLeche (CheckMode Env Expr Name Level ConstantVal ConstantInfo BlockParts TargetMajor)

universe w

variable {V : Type w} [SetTheory V] {μ : CheckMode}

section Pins

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))}
  {rs : List (ConstantVal × List Expr × Nat × List (ConstantVal × Nat))}

/-- An application spine's head is scoped where the spine is. -/
theorem WScoped.mkAppN_head {d : Nat} :
    ∀ (as : List Expr) {f : Expr}, Expr.WScoped d (Expr.mkAppN f as) → Expr.WScoped d f
  | [], _, h => h
  | a :: as, f, h => by
    have := WScoped.mkAppN_head as (f := .app f a) h
    simp only [Expr.WScoped] at this
    exact this.1

/-- An application spine's head is bounded where the spine is. -/
theorem looseBVarsBounded_mkAppN_head {k : Nat} :
    ∀ (as : List Expr) {f : Expr}, (Expr.mkAppN f as).looseBVarsBounded k = true →
      f.looseBVarsBounded k = true
  | [], _, h => h
  | a :: as, f, h => by
    have := looseBVarsBounded_mkAppN_head as (f := .app f a) h
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at this
    exact this.1

/-- A leaf of an application spine's head is a leaf of the spine. -/
theorem fvarLeaves_mkAppN_head' {l : Nat × Expr} :
    ∀ (as : List Expr) {f : Expr}, l ∈ f.fvarLeaves → l ∈ (Expr.mkAppN f as).fvarLeaves
  | [], _, h => h
  | a :: as, f, h => fvarLeaves_mkAppN_head' as (f := .app f a)
      (by simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl h)

set_option maxHeartbeats 2000000 in
/-- **A stored major-domain argument, or a head of its application spine,
over the prefix, in the prefix context**: inferred at the prefix depth
(the stored type's own inference infers the major's domain, hence its
spine's head and arguments; a term scoped at the prefix infers alike
there), scoped, and in the prefix context — the prefix openers' readings
are the prefix domains, graded types (see the module docstring). -/
theorem storedMajorSub_ctx (hμ : μ.isVerified = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageG μ F envC pp cvTas rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) (ψ : Name → Nat) {fvs : List Expr} {concl maj : Expr}
    (hop : openPisAtFvars (pp.toBlockShape.majorIdxAt j + 1) r.1.type 0 = some (fvs, concl))
    (hmaj : fvs[pp.toBlockShape.majorIdxAt j]? = some maj)
    {x : Expr} (hxA : x ∈ maj.fvarTypeD.getAppArgs ∨
      ∃ args, maj.fvarTypeD = Expr.mkAppN x args)
    (hlt : ∀ l ∈ x.fvarLeaves, l.1 < pp.toBlockShape.rulePrefixAt j) :
    (∃ tx, ConLeche.inferTypeCore .verified envC F (pp.toBlockShape.rulePrefixAt j) x = .ok tx) ∧
      Rules.Frame (pp.toBlockShape.rulePrefixAt j) x ∧
      CtxOk mpC.base2 ψ (pp.toBlockShape.rulePrefixAt j)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j).reverse x := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  generalize hmIdef : pp.toBlockShape.majorIdxAt j = mI at hop hmaj
  generalize hrPdef : pp.toBlockShape.rulePrefixAt j = rP at hlt ⊢
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  have hle : rP ≤ mI := by have := TE.hmI'; omega
  obtain ⟨stype, u0, hinfT, -⟩ := TE.hcv.sorted
  generalize hrty : r.1.type = tyA at hinfT
  obtain ⟨hw0, hb0⟩ := recStage_tyClosed h hr
  -- the major's domain, inferred at `mI`
  obtain ⟨fvsA, fvsB, o₀, hA, hB, hfe⟩ := openPisAtFvars_split mI (m := 1) hop
  obtain ⟨dom, bd, rfl⟩ : ∃ dom bd, o₀ = .forallE dom bd := by
    match o₀, hB with
    | .forallE dom bd, _ => exact ⟨dom, bd, rfl⟩
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
      exact ConLeche.inferTypeCore_forallE_dom' hinfT
    | succ n =>
      obtain ⟨bt, -, hbt, -⟩ := inferTypeCore_openPis_body rfl n hA hinfT
      rw [Nat.zero_add] at hbt
      exact ConLeche.inferTypeCore_forallE_dom' hbt
  obtain ⟨tdom, htdom⟩ := hdomInf
  rw [hmajE] at hxA
  simp only [Expr.fvarTypeD] at hxA
  have hwsDom : Expr.WScoped mI dom := by
    have := openPisAtFvars_typeWScoped (mI + 1) hop hw0 mI maj hmaj
    rw [hmajE, Nat.zero_add] at this; exact this
  have hbFvs := (openPisAtFvars_bounded _ hop hb0).2
  have hbDom : dom.looseBVarsBounded 0 = true := by
    have := hbFvs maj (List.mem_of_getElem? hmaj); rw [hmajE] at this; exact this
  -- the sub-term's inference, scoping and leaves
  obtain ⟨⟨tx, htx⟩, hwsX, hbX, hlD⟩ : (∃ tx, ConLeche.inferTypeCore .verified envC F mI x = .ok tx) ∧
      Expr.WScoped mI x ∧ x.looseBVarsBounded 0 = true ∧
      ∀ l ∈ x.fvarLeaves, l ∈ dom.fvarLeaves := by
    rcases hxA with hxA | ⟨args, hdE⟩
    · exact ⟨ConLeche.inferTypeCore_mkAppN_args _ (f := dom.getAppFn)
          (by rw [ConLeche.Expr.mkAppN_getApp]; exact htdom) x hxA,
        wscoped_of_getAppArgs hwsDom x hxA, ConLeche.looseBVarsBounded_getAppArgs hbDom x hxA,
        fun l hl => ConLeche.fvarLeaves_getAppArgs hxA l hl⟩
    · rw [hdE] at htdom hwsDom hbDom
      exact ⟨Model.inferTypeCore_mkAppN_fn_inv args htdom, WScoped.mkAppN_head args hwsDom,
        looseBVarsBounded_mkAppN_head args hbDom,
        fun l hl => by rw [hdE]; exact fvarLeaves_mkAppN_head' args hl⟩
  have hnil : r.1.type.fvarLeaves = [] := fvarLeaves_nil_of_wscoped_zero hw0
  have hleafF : ∀ l ∈ x.fvarLeaves, Expr.fvar l.1 l.2 ∈ fvs := by
    intro l hl
    have hlD : l ∈ dom.fvarLeaves := hlD l hl
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
      rw [List.getElem?_take, ite_eq_left (show pos < rP by have := hlt l hl; omega)]; exact hpos
    exact List.mem_of_getElem? hpt
  have hLX : Expr.LeavesBounded x :=
    leavesBounded_of_openers (fun y hy => hbFvs y (List.mem_of_mem_take hy)) hleafP
  -- the recursor type's reading: its prefix domains
  obtain ⟨fvs', concl', hop', -, hTyE, hlenRds, hdomsR, -, hwdTy⟩ :=
    recStage_tyPis (V := V) rfl mpC h hr ψ
  rw [hmIdef] at hop' hlenRds
  obtain ⟨hff, -⟩ := Prod.mk.inj (Option.some.inj (hop'.symm.trans hop))
  rw [hff] at hdomsR
  generalize hPd : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j = pdoms
  have hPdE : pdoms = (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape rs ψ j).take
      rP := by
    rw [← hPd, blockRulePdomsAV, hrPdef]
  have hlenPd : pdoms.length = rP := by
    rw [hPdE, List.length_take, hlenRds]; omega
  have hAa : ∀ i, i < rP → ∀ y, fvs[i]? = some y →
      denote mpC.base2.acval envC ψ i (Expr.fvarTypeD y) = some (pdoms.getD i default) := by
    intro i hi y hy
    obtain ⟨pd, hpd, hrd⟩ := hdomsR i y hy
    rw [hrd, hPdE, List.getD_eq_getElem?_getD, List.getElem?_take,
      ite_eq_left hi, hpd]
    rfl
  have hokTower : ∀ l, l < rP → ∀ (σ : Nat → V) (ys : List V),
      SpineFit σ ((pdoms ++ [] ++ []).take l) ys →
      WellDenotedTy V (consList ys σ) ((pdoms ++ [] ++ []).getD l default) := by
    intro l hl σ ys hys
    simp only [List.append_nil] at hys ⊢
    rw [hPdE] at hys ⊢
    exact prefixDoms_graded_of_tower
      (cc := blockRecConclAV mpC.base2.acval envC pp.toBlockShape rs ψ j)
      (by rw [hlenRds]; omega) (fun ρ' => by rw [← hTyE]; exact hwdTy ρ') hl hys
  have hokΔ := blockRuleHokΔ_of (V := V) (pdoms := pdoms) (fdoms := []) (ihdoms := [])
    (nF := 0) (nR := 0) hlenPd rfl rfl (by simpa using hokTower)
  simp only [List.reverse_nil, List.append_nil, List.nil_append, Nat.add_zero] at hokΔ
  -- the context at the prefix
  have hwsP := (ConLeche.openPisAtFvars_WScoped _ _ 0 hopP hw0).1
  rw [Nat.zero_add] at hwsP
  have hwsR : Expr.WScoped rP x := ConLeche.WScoped.of_leaves_below hwsX hlt
  have hent : ∀ i, i < rP → pdoms.reverse[rP - 1 - i]? = some (pdoms.getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by omega), hlenPd, show rP - 1 - (rP - 1 - i) = i from by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  have hCE : CtxOk mpC.base2 ψ rP pdoms.reverse x :=
    ctxOk_of_openers mpC.base2.acval_closed (Aa := fun i => pdoms.getD i default)
      (by rw [List.length_reverse, hlenPd])
      (fun i y hy => by simpa using ConLeche.openPisAtFvars_index _ _ _ hopP i y hy)
      hwsP
      (fun i y hy => by
        have hi : i < rP := by
          have := (List.getElem?_eq_some_iff.mp hy).1
          rw [List.length_take] at this; omega
        rw [List.getElem?_take, ite_eq_left hi] at hy
        exact hAa i hi y hy)
      hleafP hlt hent
      (fun i hi ρ hρ => by
        have hq := hokΔ i hi _ hρ
        rw [List.getD_eq_getElem?_getD, List.getElem?_reverse (by omega), hlenPd,
          show rP - 1 - (rP - 1 - i) = i from by omega] at hq
        exact hq)
  refine ⟨⟨tx, ?_⟩, ⟨hwsR, hbX, hLX⟩, hCE⟩
  rw [ConLeche.inferTypeCore_depth_inv mpC.base2.wf F (Expr.WScoped.to_wscopedB hwsR)
    (Expr.WScoped.to_wscopedB hwsX)]
  exact htx

/-- **A stored major-domain argument, or a head of its application spine,
over the prefix is graded at every prefix spine** (`storedMajorSub_ctx`,
then the inference's soundness). -/
theorem storedMajorSub_graded (hμ : μ.isVerified = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageG μ F envC pp cvTas rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) (ψ : Name → Nat) {fvs : List Expr} {concl maj : Expr}
    (hop : openPisAtFvars (pp.toBlockShape.majorIdxAt j + 1) r.1.type 0 = some (fvs, concl))
    (hmaj : fvs[pp.toBlockShape.majorIdxAt j]? = some maj)
    {x : Expr} (hxA : x ∈ maj.fvarTypeD.getAppArgs ∨
      ∃ args, maj.fvarTypeD = Expr.mkAppN x args)
    (hlt : ∀ l ∈ x.fvarLeaves, l.1 < pp.toBlockShape.rulePrefixAt j) :
    ∃ w, denote mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j) x = some w ∧
      ∀ σ : Nat → V,
        Sat V (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j).reverse σ →
        WellDenoted V σ w := by
  obtain rfl : μ = .verified := CheckMode.eq_verified hμ
  obtain ⟨⟨tx, htx⟩, hfr, hCE⟩ := storedMajorSub_ctx rfl mpC h hr ψ hop hmaj hxA hlt
  obtain ⟨wa, hwa⟩ := acceptedReads_of mpC.base2 ψ htx hfr.1 hfr.2.1 hfr.2.2
  obtain ⟨-, -, -, -, hgr, -⟩ :=
    Rules.InferSemFull.global
      (Rules.infer_sound (Rules.RulesInputs.ofSem mpC ψ) (Rules.inferTypeCore_bridge htx))
      hfr hCE hwa
  exact ⟨wa, hwa, fun σ hσ => hgr σ hσ⟩

/-- **A stored major-domain argument over the prefix is graded at every
prefix spine** (`storedMajorSub_graded` at an argument). -/
theorem storedMajorArg_graded (hμ : μ.isVerified = true) (mpC : EnvModelM V μ envC)
    (h : ConLeche.RecStageG μ F envC pp cvTas rs)
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : rs[j]? = some r) (ψ : Name → Nat) {fvs : List Expr} {concl maj : Expr}
    (hop : openPisAtFvars (pp.toBlockShape.majorIdxAt j + 1) r.1.type 0 = some (fvs, concl))
    (hmaj : fvs[pp.toBlockShape.majorIdxAt j]? = some maj)
    {x : Expr} (hxA : x ∈ maj.fvarTypeD.getAppArgs)
    (hlt : ∀ l ∈ x.fvarLeaves, l.1 < pp.toBlockShape.rulePrefixAt j) :
    ∃ w, denote mpC.base2.acval envC ψ (pp.toBlockShape.rulePrefixAt j) x = some w ∧
      ∀ σ : Nat → V,
        Sat V (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape rs ψ j).reverse σ →
        WellDenoted V σ w :=
  storedMajorSub_graded hμ mpC h hr ψ hop hmaj (.inl hxA) hlt

end Pins

section StagePins

variable {F : Nat} {envC : Env} {pp : BlockParts} {cvTas : List ConstantVal}
  {ctorsAs : List (List (ConstantVal × Nat))} {out : List (ConstantVal × TargetMajor × List Expr)}

set_option maxHeartbeats 2000000 in
/-- **The `.nested` pins' law at every stored rule, of ANY recursor
stage** (`tgtRecPinsOk` without the target check's run), given that a
`.nested` firing reads off the stored type (`hread`; the generated stage's
`GenRecRun.fire_nestedRead`).  The pins are the stored type's major-domain
parameters closed over the rule prefix (`nestedRead_open`), so opened
back at the prefix openers they are those parameters up to erasure
(`instSeq_abstractRange_open`), graded at every prefix spine by the
stored type's own inference (`storedMajorArg_graded`); `nestedPinGrade`
carries the grading to the chain of any graded fit of the recursor
type. -/
theorem recStagePinsOk (hμ : μ.isVerified = true) (mpC : EnvModelM V μ envC)
        (h : ConLeche.RecStageG μ F envC pp cvTas (tgtRs out))
    {Rr : Nat → ConstantVal × List Expr × Nat × List (ConstantVal × Nat) → List ConLeche.RecRule}
    {s : (Name → Nat) → Nat} {eqs : (Name → Nat) → List Term}
    (m₃ : EnvModel V (ConLeche.consBlockRecsR Rr pp.toBlockShape 0 (tgtRs out) envC))
    (hac : m₃.acval = blockRecAcv mpC.base2.acval envC (tgtRs out) s eqs)
    (φ : Name → Nat) (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat))
    (hr : (tgtRs out)[j]? = some r) (cA : ConstantVal × Nat) (rhs : Expr)
    (hread : ∀ lvls pins,
      ConLeche.tgtFireOf pp.toBlockShape (ConLeche.tgtMajorsOf out) j r = .nested lvls pins →
      ConLeche.NestedRead (·.constsResolve envC) r.1.levelParams r.1.type
        (pp.toBlockShape.majorIdxAt j) (pp.toBlockShape.rulePrefixAt j)
        (ConLeche.tgtMajorsOf out j).nPc lvls pins) :
    RecRulePinsOk m₃ φ r.1 (pp.toBlockShape.rulePrefixAt j)
      (ConLeche.recRuleBits envC.find?
          { ctor := cA.1.name, nfields := cA.2, ctorParams := (ConLeche.tgtMajorsOf out j).nPc,
            fire := (ConLeche.tgtFireOf pp.toBlockShape
              (ConLeche.tgtMajorsOf out)) j r, rhs := rhs }) := by
  intro us hus lvls pins hf q hq
  simp only [ConLeche.recRuleBits_fire] at hf
  simp only [ConLeche.recRuleBits_ctorParams] at hq
  have hsyn := hread lvls pins hf
  obtain ⟨-, -, hpinsWf, -⟩ := id hsyn
  -- the stored type's openers
  obtain ⟨_, _, -, ⟨TE⟩⟩ := ConLeche.recStageG_tyGen h hr
  have hopen := TE.hopen
  have hmaj := TE.hmaj
  have hle0 : pp.toBlockShape.rulePrefixAt j ≤ pp.toBlockShape.majorIdxAt j := by
    have := TE.hmI'; omega
  -- the parameter's grading, at the rule prefix
  have hgradeAt := fun (ψ : Name → Nat) {x : Expr} (hxA : x ∈ TE.maj.fvarTypeD.getAppArgs)
      (hlt : ∀ l ∈ x.fvarLeaves, l.1 < pp.toBlockShape.rulePrefixAt j) =>
    storedMajorArg_graded (V := V) hμ mpC h hr ψ hopen hmaj hxA hlt
  obtain ⟨rP, hRP⟩ : ∃ n, pp.toBlockShape.rulePrefixAt j = n := ⟨_, rfl⟩
  obtain ⟨mI, hMI⟩ : ∃ n, pp.toBlockShape.majorIdxAt j = n := ⟨_, rfl⟩
  rw [hRP, hMI] at hsyn
  rw [hRP] at hgradeAt hle0 ⊢
  rw [hMI] at hopen hmaj hle0
  obtain ⟨-, hpinsE⟩ := ConLeche.nestedRead_open hsyn hopen hmaj
  obtain ⟨-, -, -, -, -, -, -, -, -, -, hplen⟩ := hsyn
  -- the `q`-th pin is the `q`-th parameter, closed
  generalize hds : TE.maj.fvarTypeD.getAppArgs.take (ConLeche.tgtMajorsOf out j).nPc = ds
    at hpinsE
  have hqd : q < ds.length := by
    rw [← List.length_map (f := (·.abstractRange 0 rP)), hpinsE, hplen]; exact hq
  obtain ⟨x, hxdef⟩ : ∃ x, x = ds[q] := ⟨_, rfl⟩
  have hxA : x ∈ TE.maj.fvarTypeD.getAppArgs := by
    rw [hxdef]; exact List.mem_of_mem_take (by rw [hds]; exact List.getElem_mem hqd)
  have hpinq : (pins.getD q default) = x.abstractRange 0 rP := by
    rw [← hpinsE, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hqd,
      hxdef]
    rfl
  have hpinMem : pins.getD q default ∈ pins := by
    rw [hpinq, hxdef, ← hpinsE]
    exact List.mem_map_of_mem (List.getElem_mem hqd)
  obtain ⟨hpF, -, hpR, hpB⟩ := hpinsWf _ hpinMem
  rw [hRP] at hpB
  -- the prefix openers
  obtain ⟨hw0, hb0⟩ := recStage_tyClosed h hr
  obtain ⟨oP, hopP⟩ := ConLeche.openPisAtFvars_prefix rP (mI + 1) r.1.type 0
    (by omega) hopen
  have hoslen : (TE.fvs.take rP).length = rP := ConLeche.Verify.openPisAtFvars_length _ hopP
  have hshape : ∀ (k : Nat) (y : Expr), (TE.fvs.take rP)[k]? = some y →
      ∃ ty, y = Expr.fvar k ty := by
    intro k y hy
    simpa using ConLeche.openPisAtFvars_index _ _ _ hopP k y hy
  have hpre : ∀ k (hk : k < (TE.fvs.take rP).length), ∃ ty,
      (TE.fvs.take rP)[k] = .fvar k ty := by
    intro k hk
    obtain ⟨ty, hty⟩ := hshape k _ (List.getElem?_eq_getElem hk)
    exact ⟨ty, hty⟩
  have hwsOs : ∀ y ∈ TE.fvs.take rP, Expr.WScoped (rP + 0) y := by
    intro y hy
    have := (openPisAtFvars_WScoped _ _ 0 hopP hw0).1 y hy
    simpa using this
  have hbOs : ∀ y ∈ TE.fvs.take rP, y.looseBVarsBounded 0 = true := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    obtain ⟨ty, hty⟩ := hpre k hk
    rw [hty]; rfl
  -- the parameter's scoping at the prefix
  have hwsM : Expr.WScoped mI TE.maj.fvarTypeD := by
    have := openPisAtFvars_typeWScoped (mI + 1) hopen hw0 mI TE.maj hmaj
    rwa [Nat.zero_add] at this
  have hwsX : Expr.WScoped rP x := ConLeche.WScoped.of_abstractRange_noFvar
    (wscoped_of_getAppArgs hwsM x hxA) (by rw [← hpinq]; exact hpF)
  have hxb : x.looseBVarsBounded 0 = true :=
    ConLeche.looseBVarsBounded_getAppArgs
      ((openPisAtFvars_bounded _ hopen hb0).2 TE.maj (List.mem_of_getElem? hmaj)) x hxA
  have hxlt : ∀ l ∈ x.fvarLeaves, l.1 < rP :=
    fun l hl => ConLeche.Expr.fvarLeaves_lt_of_wscoped hwsX l hl
  -- the round trip: the pin opened at the prefix openers is the parameter, up to erasure
  have hround : Expr.ErasedEq (Expr.instSpine (TE.fvs.take rP) (rP - 1) (pins.getD q default))
      x := by
    rw [hpinq, Expr.instSpine_eq_instSeq]
    have := ConLeche.instSeq_abstractRange_open hpre x 0 hxb (by rw [hoslen]; exact hxlt)
    rw [hoslen, Nat.zero_add] at this
    exact this
  -- the level valuation the instantiation reads at
  obtain ⟨ψ, hψ⟩ : ∃ ψ, ψ = Level.substFn φ r.1.levelParams us := ⟨_, rfl⟩
  -- the parameter's reading and its grading
  obtain ⟨w, hw, hwGr⟩ := hgradeAt ψ hxA hxlt
  -- the opened pin's reading, at the constructors' environment
  have hacl := mpC.base2.acval_closed
  have hainst : ∀ (n : Name) (ψ' : Name → Nat) (y : Term) (k : Nat),
      (mpC.base2.acval n ψ').inst y k = mpC.base2.acval n ψ' :=
    fun n ψ' y k => AVExprSubst.inst_eq_self_of_closed (mpC.base2.acval_closed n ψ') y k
  have hw' : denote mpC.base2.acval envC ψ (rP + 0)
      (Expr.instSpine (TE.fvs.take rP) (rP - 1) (pins.getD q default)) = some w := by
    rw [denote_erasedEq hround, Nat.add_zero]; exact hw
  obtain ⟨vpa, hvpden⟩ := pinOpenRevReads (acval := mpC.base2.acval)
    (env := envC) (φ := ψ) hacl hainst mpC.base2.cval_closed hoslen hshape
    hwsOs hbOs hpF hpB hw'
  -- carried to the recursors' environment and valuation
  have hcbP : ConstsBound envC (pins.getD q default) := constsBound_of_constsResolve _ hpR
  refine ⟨vpa, ?_, ?_⟩
  · rw [ConLeche.openRev_instantiateLevelParams,
      denote_instLevels m₃.acval_params φ, ← hψ]
    exact blockRecDenote_cross h hac ψ rP _ (constsBound_openRev hcbP 0 rP) hvpden
  · intro ρ zs TVa restR hzslen hzsOk hTVa hfit
    obtain rfl := blockRuleTVa_run hμ mpC h hac hr φ us hTVa
    rw [← hψ] at hfit
    -- the recursor type's prefix telescope
    obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -⟩ := recStage_tyPis (V := V) hμ mpC h hr ψ
    rw [hMI] at hlenRds
    have hPdE : blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j
        = (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).take
            rP := by
      rw [blockRulePdomsAV, hRP]
    have htake : ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).take
        rP).length = rP := by
      rw [List.length_take, hlenRds]; omega
    have htower : PiTeleAV rP (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j)
        (blockRulePdomsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).reverse
        (mkPisAV ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j).drop
            rP)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j)) := by
      rw [hTyE, hPdE, ← List.take_append_drop rP
          (blockRecRdsAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j), mkPisAV_append,
        List.take_append_drop]
      have := piTeleAV_mkPisAV ((blockRecRdsAV mpC.base2.acval envC pp.toBlockShape
        (tgtRs out) ψ j).take rP) (mkPisAV ((blockRecRdsAV mpC.base2.acval envC
          pp.toBlockShape (tgtRs out) ψ j).drop rP)
          (blockRecConclAV mpC.base2.acval envC pp.toBlockShape (tgtRs out) ψ j))
      rwa [htake] at this
    refine nestedPinGrade (acval := mpC.base2.acval) (env := envC)
      (φ := ψ) (cnF := 0) hacl hainst mpC.base2.cval_closed hoslen hshape
      hwsOs hbOs hpF hpB hvpden htower ?_ hzslen hzsOk hfit
    intro w0 hw0' σ hσ
    rw [hw'] at hw0'
    obtain rfl := Option.some.inj hw0'
    exact hwGr σ (by simpa using hσ)

end StagePins

end ConLeche.Model
