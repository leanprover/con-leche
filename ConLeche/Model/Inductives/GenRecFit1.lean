module

public import ConLeche.Model.Inductives.GenRecFitBase
public import ConLeche.Model.Inductives.GenClsSem
import ConLeche.Verify.Inductives.GenRecRun
import ConLeche.Verify.Inductives.ClassGenScope
import ConLeche.Model.Rules.Sound
import ConLeche.Model.Inductives.StructFrameKit
import ConLeche.Model.Inductives.GenRecPins
import ConLeche.Model.Tiers
import ConLeche.Model.CtxOkKit
import ConLeche.Model.WellDenotedTransport
import ConLeche.Verify.Rules.Bridge
import ConLeche.Verify.InferLemmas
import ConLeche.Verify.InferLeaves
import ConLeche.Verify.Subst
import ConLeche.Model.Inductives.GenClsFrame
import ConLeche.Model.OpenedCtx
import ConLeche.Model.Env.BlockLfp
import ConLeche.Model.Inductives.GenRecFit2
import ConLeche.Model.Inductives.GenRecPreRun
import ConLeche.Semantics.Tower.TowerKit
import ConLeche.Model.Inductives.ContN2
import ConLeche.Model.Inductives.GenClsData
import ConLeche.Model.Inductives.GenRecParams
import ConLeche.Model.Inductives.ClassGenRead
import ConLeche.Model.Inductives.TargetOutSat
import ConLeche.Model.Inductives.BlockRecTyping
import ConLeche.Model.Inductives.BlockRecData
import ConLeche.Model.Inductives.BlockRecLaw
import ConLeche.Model.Inductives.StructRecKit
import ConLeche.Model.Inductives.TargetOutRow
import ConLeche.Model.Rules.RedSoundKit
import ConLeche.Model.Levels
import ConLeche.Verify.InstLevels
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Rules.InferBridge
import ConLeche.Verify.Denote.Closed
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Reading.Levels

public section

/-!
# The generated rules' parameter fit (`GenFit1`)

A rule's parameters fit its constructor's parameter binders because the stored recursor type's
own inference checks them there: the minor premise of the rule's constructor concludes in the
motive applied to the constructor at the class's parameters and the fields, and the kernel's
application rule compares each parameter's type with the constructor's binder
(`inferTypeCore_app_inv'`).  Read in the model (`teleFitPA_of_inferSpine`), an inferred
application spine of a head whose type is a Π-telescope fits that telescope: each argument
inhabits its inferred type's reading (`InferSemFull`), which the comparison makes the binder's
(`DefEqSem`).  The fit asks no fit of the fields, so it holds at every prefix fit, also where no
field fits.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel
open ConLeche.Term ConLeche.Verify SetTheory

open ConLeche (Env Expr Name Level ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]

/-! ## An inferred application spine fits its head's telescope -/

section Spine

variable {envC : Env}

set_option maxHeartbeats 4000000 in
/-- **An inferred application spine fits its head's type** at every valuation satisfying a
context the spine is in: where the head's inferred type has a Π-prefix as long as the spine, the
arguments' readings fit its reading — each argument inhabits its inferred type, which the
application rule's comparison identifies with the binder's domain. -/
theorem teleFitPA_of_inferSpine (mpC : EnvModelM V envC) (ψ : Name → Nat) {F D : Nat}
    {Δ : List Term} :
    ∀ (as : List Expr) {f tf t : Expr},
      ConLeche.inferTypeCore .verified false envC F D (Expr.mkAppN f as) = .ok t →
      ConLeche.inferTypeCore .verified false envC F D f = .ok tf →
      (tf.stripPis as.length).isSome →
      Rules.Frame D (Expr.mkAppN f as) →
      CtxOk mpC.base2 ψ D Δ (Expr.mkAppN f as) →
      ∃ asT : List Term, DenoteSpine mpC.base2.acval envC ψ D as asT ∧
        ∀ T : Term, denote mpC.base2.acval envC ψ D tf = some T →
        ∀ ρ : Nat → V, Sat V Δ ρ → ∃ r, TeleFitPA V ρ T asT r
  | [], _, _, _, _, _, _, _, _ => ⟨[], .nil, fun T _ _ _ => ⟨T, .nil⟩⟩
  | a :: as, f, tf, t, hinf, htf, hsp, hfr, hC => by
    have hin := Rules.RulesInputs.ofSem mpC ψ
    have hinf' : ConLeche.inferTypeCore .verified false envC F D
        (Expr.mkAppN (.app f a) as) = .ok t := hinf
    obtain ⟨hws, hb, hL⟩ := hfr
    -- the head application's frame and context
    have hwsA : Expr.WScoped D (.app f a) := WScoped.mkAppN_head as hws
    have hbA : (Expr.app f a).looseBVarsBounded 0 = true := looseBVarsBounded_mkAppN_head as hb
    have hsubA : ∀ l ∈ (Expr.app f a).fvarLeaves, l ∈ (Expr.mkAppN f (a :: as)).fvarLeaves :=
      fun l hl => fvarLeaves_mkAppN_head' as hl
    have hLA : Expr.LeavesBounded (.app f a) := fun l hl => hL l (hsubA l hl)
    have hCA : CtxOk mpC.base2 ψ D Δ (.app f a) := hC.of_subset hsubA
    simp only [Expr.WScoped] at hwsA
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbA
    have hsubF : ∀ l ∈ f.fvarLeaves, l ∈ (Expr.app f a).fvarLeaves := fun l hl => by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl
    have hsubX : ∀ l ∈ a.fvarLeaves, l ∈ (Expr.app f a).fvarLeaves := fun l hl => by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inr hl
    have hfrF : Rules.Frame D f := ⟨hwsA.1, hbA.1, fun l hl => hLA l (hsubF l hl)⟩
    have hfrX : Rules.Frame D a := ⟨hwsA.2, hbA.2, fun l hl => hLA l (hsubX l hl)⟩
    have hCF : CtxOk mpC.base2 ψ D Δ f := hCA.of_subset hsubF
    have hCX : CtxOk mpC.base2 ψ D Δ a := hCA.of_subset hsubX
    -- the application rule at the head
    obtain ⟨tfa, htfa⟩ := inferTypeCore_mkAppN_fn_inv as (f := .app f a) hinf'
    obtain ⟨tf', ty', body', hf', hw, rfl, ta, hta, hde⟩ := ConLeche.inferTypeCore_app_inv' htfa
    obtain rfl : tf = tf' := (Except.ok.inj (hf'.symm.trans htf)).symm
    obtain ⟨dom, bd, rfl⟩ : ∃ dom bd, tf = .forallE dom bd := by
      cases tf <;> first
        | exact ⟨_, _, rfl⟩
        | simp [Expr.stripPis] at hsp
    obtain ⟨rfl, rfl⟩ := Expr.forallE.inj (ConLeche.whnf_forallE_eq hw).symm
    -- the readings
    obtain ⟨fa, hfa⟩ := acceptedReads_of mpC.base2 ψ htf hfrF.1 hfrF.2.1 hfrF.2.2
    obtain ⟨aa, haa⟩ := acceptedReads_of mpC.base2 ψ hta hfrX.1 hfrX.2.1 hfrX.2.2
    obtain ⟨hfrT, hsubT, Tf, hTf, -, hTfTy, -⟩ :=
      Rules.InferSemFull.global (Rules.infer_sound hin (Rules.inferTypeCore_bridge htf))
        hfrF hCF hfa
    obtain ⟨hfrTa, hsubTa, taT, htaT, hgra, hgrTa, hmemA⟩ :=
      Rules.InferSemFull.global (Rules.infer_sound hin (Rules.inferTypeCore_bridge hta))
        hfrX hCX haa
    obtain ⟨A, B, hA, hB, rfl⟩ := denote_forallE_inv hTf
    obtain ⟨hwsT, hbT, hLT⟩ := hfrT
    simp only [Expr.WScoped] at hwsT
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbT
    have hsubDom : ∀ l ∈ dom.fvarLeaves, l ∈ (Expr.forallE dom bd).fvarLeaves := fun l hl => by
      simp only [Expr.fvarLeaves, List.mem_append]; exact Or.inl hl
    have hfrDom : Rules.Frame D dom := ⟨hwsT.1, hbT.1, fun l hl => hLT l (hsubDom l hl)⟩
    have hCDom : CtxOk mpC.base2 ψ D Δ dom := hCF.of_subset fun l hl => hsubT l (hsubDom l hl)
    have hCTa : CtxOk mpC.base2 ψ D Δ ta := hCX.of_subset hsubTa
    -- the comparison, in the model
    have hD : Rules.DefEq envC D ta dom := by
      unfold ConLeche.argEager at hde
      split at hde
      · exact (Rules.bridgeAt envC F true).2.2.1 hde
      · exact Rules.isDefEqCore_bridge hde
    have hdsem := Rules.defeq_sound hin hD
    have hmem : ∀ ρ : Nat → V, Sat V Δ ρ → interp V ρ aa ∈ˢ interp V ρ A := by
      intro ρ hρ
      have hpi := hTfTy ρ hρ
      have hAty : WellDenotedTy V ρ A :=
        ⟨(cast (WellDenoted_pi V ρ A B) hpi.1).1, (cast (WellDenoted_pi V ρ A B) hpi.1).2.1⟩
      have he := hdsem hfrTa hfrDom hCTa.toS hCDom.toS htaT hA ρ hρ (hCTa.leavesGr hρ)
        (hCDom.leavesGr hρ) (hgrTa ρ hρ).1 hAty.1 (hgrTa ρ hρ).2.ne_pt hAty.2.ne_pt
      rw [← he]
      exact hmemA ρ hρ
    -- the rest of the spine, at the instantiated body
    have hbody : denote mpC.base2.acval envC ψ D (bd.instantiate1 a) = some (B.inst aa) := by
      rw [denote_beta (ty := dom) mpC.base2.acval_closed (acval_inst_self mpC.base2)
        hwsT.2.fvarsBelow hwsA.2 hbA.2 haa 0, hB]
      rfl
    have hsp' : ((bd.instantiate1 a).stripPis as.length).isSome := by
      have h0 : (bd.stripPis as.length).isSome := by
        simpa [Expr.stripPis] using hsp
      exact Expr.stripPis_instantiate1_isSome as.length 0 h0
    obtain ⟨asT, hasT, hfit⟩ := teleFitPA_of_inferSpine mpC ψ as hinf' htfa hsp'
      ⟨hws, hb, hL⟩ hC
    refine ⟨aa :: asT, .cons haa hasT, fun T hT ρ hρ => ?_⟩
    obtain rfl : Term.pi A B = T := Option.some.inj (hTf.symm.trans hT)
    obtain ⟨r, hr⟩ := hfit _ hbody ρ hρ
    exact ⟨r, .cons (hmem ρ hρ) hr⟩

end Spine

/-! ## A graded frame of openers, cut and read as a context -/

section FrameKit

variable {envC : Env} {mpC : EnvModelM V envC} {ψ : Name → Nat}

/-- **A graded frame's first `D` openers are one.** -/
private theorem GradedFrame.take {D k : Nat} {fr : List Expr} {doms : List Term}
    (G : GradedFrame mpC ψ (D + k) fr doms) :
    GradedFrame mpC ψ D (fr.take D) (doms.take D) := by
  have hfl := G.frLen
  have hdl := G.len
  have hsh : ∀ (i : Nat) (x : Expr), (fr.take D)[i]? = some x → ∃ ty, x = Expr.fvar i ty := by
    intro i x hx
    rw [List.getElem?_take] at hx
    split at hx
    · exact G.shape i x hx
    · exact nomatch hx
  refine ⟨by rw [List.length_take]; omega, by rw [List.length_take]; omega, hsh, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
    obtain ⟨ty, hty⟩ := hsh i _ (List.getElem?_eq_getElem hi)
    have hw := G.ws _ (List.mem_of_mem_take hx)
    rw [hty] at hw ⊢
    have hiD : i < D := by rw [List.length_take] at hi; omega
    simp only [Expr.WScoped] at hw ⊢
    exact ⟨hiD, hw.2⟩
  · exact fun x hx => G.lb x (List.mem_of_mem_take hx)
  · intro i x hx
    have hiD : i < D := by
      have := (List.getElem?_eq_some_iff.mp hx).1
      rw [List.length_take] at this; omega
    rw [List.getElem?_take, ite_eq_left hiD] at hx
    rw [G.rd i x hx, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_take, ite_eq_left hiD]
  · intro l hl σ ys hys
    rw [List.take_take, Nat.min_eq_left (Nat.le_of_lt hl)] at hys
    rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_eq_left hl, ← List.getD_eq_getElem?_getD]
    exact G.ok l (by omega) σ ys hys

/-- **A graded frame is a context** for a term over its openers. -/
private theorem GradedFrame.ctxOk {D : Nat} {fr : List Expr} {doms : List Term}
    (G : GradedFrame mpC ψ D fr doms) {e : Expr} (hwsE : Expr.WScoped D e)
    (hleaf : ∀ l ∈ e.fvarLeaves, Expr.fvar l.1 l.2 ∈ fr) :
    CtxOk mpC.base2 ψ D doms.reverse e := by
  have hdl := G.len
  have hltE : ∀ l ∈ e.fvarLeaves, l.1 < D := fun l hl => Expr.fvarLeaves_lt_of_wscoped hwsE l hl
  have hent : ∀ i, i < D → doms.reverse[D - 1 - i]? = some (doms.getD i default) := by
    intro i hi
    rw [List.getElem?_reverse (by omega), hdl, show D - 1 - (D - 1 - i) = i by omega,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  exact ctxOk_of_openers mpC.base2.acval_closed (Aa := fun i => doms.getD i default)
    (by rw [List.length_reverse, hdl]) G.shape G.ws G.rd hleaf hltE hent
    (fun i hi ρ hρ => by
      have hs := Sat_drop hρ (D - i)
      have hdrop : doms.reverse.drop (D - i) = (doms.take i).reverse := by
        rw [List.drop_reverse, hdl, show D - (D - i) = i by omega]
      rw [hdrop] at hs
      have hsp := spineFit_frameIdx_of_sat hs
      have hc := consList_frameIdx (V := V) (doms.take i).length (fun j => ρ (j + (D - i)))
      have hw := G.ok i hi _ _ hsp
      rw [hc] at hw
      rw [show (fun j => ρ (j + (D - 1 - i) + 1)) = (fun j => ρ (j + (D - i))) by
        funext j; congr 1; omega]
      exact hw)

/-- A spine fitting a frame's domains satisfies its context. -/
private theorem sat_of_spineFit_rev {doms : List Term} {σ : Nat → V} {ys : List V}
    (h : SpineFit σ doms ys) : Sat V doms.reverse (consList ys σ) := by
  have := sat_of_spineFit (Δ₀ := ([] : List Term)) (Sat_nil V σ) h
  simpa using this

end FrameKit

/-! ## A value-level fit moves to another frame and spine -/

section Move

/-- **A fit of a closed telescope moves to a spine of the same values at another frame.** -/
private theorem teleFitPA_move {σ ρ : Nat → V} {T : Term} {as bs : List Term} {r : Term}
    (hcl : Term.bvarsBelow 0 T) (hpc : Rules.PiChain as.length T)
    (hfit : TeleFitPA V σ T as r) (hl : bs.length = as.length)
    (hv : ∀ q, q < as.length → interp V ρ (bs.getD q default) = interp V σ (as.getD q default)) :
    ∃ r', TeleFitPA V ρ T bs r' := by
  have h1 := Rules.teleFit_of_teleFitPA hpc hfit
  obtain ⟨X, hX⟩ := teleFit_congr_frame' (as.map (interp V σ)) (n := 0) (ρ' := ρ) hcl
    (fun k hk => absurd hk (Nat.not_lt_zero k)) h1
  have hvals : as.map (interp V σ) = bs.map (interp V ρ) := by
    refine List.ext_getElem (by simp [hl]) fun q h₁ h₂ => ?_
    rw [List.getElem_map, List.getElem_map]
    have hq : q < as.length := by simpa using h₁
    have := hv q hq
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega),
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hq] at this
    exact this.symm
  rw [hvals] at hX
  exact Rules.teleFitPA_of_teleFit bs (by rw [hl]; exact hpc) hX

/-- Two spines of one length pushing onto one frame alike are one. -/
theorem consList_inj_of_length {l₁ l₂ : List V} {σ : Nat → V} (hl : l₁.length = l₂.length)
    (h : consList l₁ σ = consList l₂ σ) : l₁ = l₂ := by
  refine list_eq_of_getD hl fun q hq => ?_
  have e := congrFun h (l₁.length - 1 - q)
  rw [consList_getD_of_lt _ _ _ (by omega), consList_getD_of_lt _ _ _ (by omega),
    show l₁.length - 1 - (l₁.length - 1 - q) = q by omega,
    show l₂.length - 1 - (l₁.length - 1 - q) = q by omega] at e
  exact e

end Move

/-! ## At a class -/

section Out

variable {F : Nat} {env₁ envC : Env} {pp : BlockShape} {nestedBit : Bool}
  {pos : ConLeche.NestState} {block : List ConstantInfo}
  {out : List (ConstantVal × ConLeche.TargetMajor × List Expr)}
  {mpC : EnvModelM V envC} {d : BlockData V} {Dc : Nat → LfpDatum V} {mc : Nat → Nat}
  {cvc : Nat → ConstantVal}

/-- An `instPisWith` instantiation of a parameter list exists only past as many `∀`s. -/
theorem stripPis_isSome_of_lfpCtor (hcov : LfpCover mpC []) {j : Nat} {cvI : ConstantVal}
    (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI) {i : Nat} {ctor : ConstantVal × Nat}
    (hcAM : (tgtMajor out j).ctors[i]? = some ctor) :
    (ctor.1.type.stripPis (tgtMajor out j).nPc).isSome = true := by
  obtain ⟨hiD, ⟨_, hfc0⟩, -, -⟩ := Rd.hctor i ctor hcAM
  obtain ⟨cv8, nPc8, nF8, iT8, hf8, bs, args, hstrip, -⟩ :=
    (hcov.own _ Rd.hD).ctorConcl _ Rd.hmm i hiD
  rw [hfc0] at hf8
  obtain ⟨rfl, rfl, rfl⟩ : ctor.1 = cv8 ∧ (tgtMajor out j).ds.length = nPc8 ∧ ctor.2 = nF8 := by
    injection hf8 with h; injection h with h1 h2 h3 h4; exact ⟨h1, h2, h3⟩
  rw [Rd.hnpc]
  exact ConLeche.stripPis_isSome_of_le (Nat.le_add_right _ _) (by rw [hstrip]; rfl)

set_option maxHeartbeats 16000000 in
/-- **`GenFit1` at a class**, at the class's level valuation and frame: the minor premise of the rule's constructor applies the
constructor to the class's parameters, an application the stored type's inference infers at the
rule prefix (it mentions no field), so the parameters' readings fit the constructor's parameter
binders there (`teleFitPA_of_inferSpine`); `GenPs` reads the rule's parameters as theirs. -/
theorem genFit1_core
    (R : GenRecRun .verified F (ConLeche.mkFEnv env₁) env₁ (ConLeche.mkFEnv envC) pp nestedBit
      pos block out) (hg : ConLeche.ClassGenScoped R.g) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        ∃ iT, envC.find? ctor.1.name
          = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2 iT))
    (hseam : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        ∃ iT, envC.find? ctor.1.name
            = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2 iT) ∧
        ConstsBound envC ctor.1.type ∧
        ∀ ψ : Name → Nat,
          denote mpC.base2.acval envC ψ 0 ctor.1.type
            = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ))
    {j : Nat} {r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)}
    (hr : (tgtRs out)[j]? = some r) {i : Nat} {ctor : ConstantVal × Nat}
    (hctor : r.2.2.2[i]? = some ctor)
    (hnP : pp.nP ≤ pp.rulePrefixAt j)
    {cvI : ConstantVal} (Rd : GenClsRd mpC d Dc mc cvc pp out j cvI)
    (ψ ψj : Name → Nat)
    (hlv' : ∀ q ∈ ctor.1.levelParams,
      ψj q = Level.substFn ψ ctor.1.levelParams (tgtMajor out j).lvls q)
    (ρ : Nat → V) (xs ps : List Term) (mid : Term)
    (hxl : xs.length = pp.rulePrefixAt j)
    (hmid : TeleFitPA V ρ (blockRecTyAV mpC.base2.acval envC (tgtRs out) ψ j) xs mid)
    (hpl : ps.length = (tgtMajor out j).nPc)
    (hpv : ∀ q, q < (tgtMajor out j).nPc → interp V ρ (ps.getD q default)
      = interp V (consList (xs.map (interp V ρ)) ρ)
        ((tgtOutDsa mpC.base2.acval envC pp out ψ j).getD q default)) :
    ∃ r, TeleFitPA V ρ (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) ps r := by
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  have hi : i < blockRecNCt (tgtRs out) j :=
    Nat.lt_of_lt_of_le (List.getElem?_eq_some_iff.mp hctor).1 (blockRecNCt_ge hr)
  have hcAM : (tgtMajor out j).ctors[i]? = some ctor := by rw [← tgtRs_ctors hr]; exact hctor
  have hct : tgtCtorOf out j i = ctor := by
    simp [tgtCtorOf, List.getD_eq_getElem?_getD, hcAM]
  obtain ⟨-, -, hlpC, -⟩ := Rd.hctor i ctor hcAM
  -- the minor premise, opened at the rule frame
  obtain ⟨cls, s, x, res, ws, ihs, fvs1, o1, xs', rest, hgc, hgx, hms, hxmem, hMaj, hrP, hmp,
    hopR, hCB, hnF, hcv, hwsR, hihl, hih, -, hop1, hle, hlenF, hshF, hwbF, hPd, hxl', hshX,
    hwbX, hdF, -, hrest, hbbS, hinfX, ⟨tR, hinfR⟩, hwsRest, hbRest, hleafs, -, -, -⟩ :=
    genMinorOpen R hg h mpC hfind ψ hj hi
  have G := genFieldFrame R hg h mpC hfind ψ hj hi hrP hopR hle hlenF hshF hwbF hPd hxl' hshX
    hwbX hdF hinfX hleafs
  have Gp := G.take
  have hpdl : (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ j).length
      = R.g.pre.length := by rw [blockRulePdomsAV_length mpC h hr ψ, hrP]
  have hf1l : (fvs1.take R.g.pre.length).length = R.g.pre.length := by
    rw [List.length_take]; omega
  rw [List.take_append_of_le_length (Nat.le_of_eq hf1l.symm), List.take_of_length_le
      (Nat.le_of_eq hf1l), List.take_append_of_le_length (Nat.le_of_eq hpdl.symm),
      List.take_of_length_le (Nat.le_of_eq hpdl)] at Gp
  rw [← hMaj, hcv.symm, hct] at hrest hbbS
  -- the constructor application's parameter spine, inside the minor premise's conclusion
  rw [Expr.mkAppN_append_one, mkAppN_append'] at hrest
  obtain ⟨r1, a, rfl, hEa⟩ : ∃ r1 a, rest = .app r1 a ∧
      Expr.ErasedEq a (Expr.mkAppN (Expr.mkAppN (.const ctor.1.name (tgtMajor out j).lvls)
        (tgtMajor out j).ds) (tgtFieldFvs pp out j i)) := by
    cases rest <;> simp only [Expr.ErasedEq] at hrest
    exact ⟨_, _, rfl, hrest.2⟩
  obtain ⟨-, -, -, -, -, -, ta, hta, -⟩ := ConLeche.inferTypeCore_app_inv' hinfR
  have hwsA : Expr.WScoped (R.g.pre.length + x.nF + ihs.length) a := by
    simp only [Expr.WScoped] at hwsRest; exact hwsRest.2
  have hbA : a.looseBVarsBounded 0 = true := by
    simp only [Expr.looseBVarsBounded, Bool.and_eq_true] at hbRest; exact hbRest.2
  obtain ⟨hd, bs', rfl, hhd, -⟩ := erasedEq_mkAppN_inv _ hEa
  obtain ⟨g, ds', rfl, hg', hdl'⟩ := erasedEq_mkAppN_inv _ hhd
  obtain ⟨-, hargs⟩ := erasedEq_mkAppN_args _ hdl' hhd
  obtain rfl : g = .const ctor.1.name (tgtMajor out j).lvls := by
    cases g <;> simp only [Expr.ErasedEq] at hg'
    obtain ⟨rfl, rfl⟩ := hg'; rfl
  -- the parameter spine is scoped at the rule prefix
  have hwsHd := WScoped.mkAppN_head bs' hwsA
  have hdsW : ∀ y ∈ ds', Expr.WScoped R.g.pre.length y := by
    intro y hy
    obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hy
    have hk' : k < (tgtMajor out j).ds.length := by omega
    have hE := hargs k _ _ (List.getElem?_eq_getElem hk') (List.getElem?_eq_getElem hk)
    refine WScoped.of_erasedEq _ hE (wscoped_of_getAppArgs hwsHd _ ?_)
      (((Rd.hds _ (List.getElem_mem hk')).1).mono (by omega))
    rw [Expr.getAppArgs_mkAppN]; exact List.mem_append_right _ (List.getElem_mem hk)
  have hwsP : Expr.WScoped R.g.pre.length
      (Expr.mkAppN (.const ctor.1.name (tgtMajor out j).lvls) ds') :=
    Expr.WScoped.mkAppN (by simp [Expr.WScoped]) hdsW
  obtain ⟨thd, hthd⟩ := inferTypeCore_mkAppN_fn_inv bs' hta
  rw [← ConLeche.inferTypeCore_depth_inv mpC.base2.wf F (Expr.WScoped.to_wscopedB hwsP)
    (Expr.WScoped.to_wscopedB hwsHd)] at hthd
  have hbP := looseBVarsBounded_mkAppN_head bs' hbA
  have hleafP : ∀ l ∈ (Expr.mkAppN (.const ctor.1.name (tgtMajor out j).lvls) ds').fvarLeaves,
      Expr.fvar l.1 l.2 ∈ fvs1.take R.g.pre.length := by
    intro l hl
    have hm := hleafs l (Or.inl (by
      simp only [Expr.fvarLeaves, List.mem_append]
      exact Or.inr (fvarLeaves_mkAppN_head' bs' hl)))
    have hlt : l.1 < R.g.pre.length := Expr.fvarLeaves_lt_of_wscoped hwsP l hl
    rcases List.mem_append.mp hm with hm | hm
    · exact hm
    · obtain ⟨k, hk⟩ := List.getElem?_of_mem hm
      obtain ⟨ty, hty⟩ := hshX k _ hk
      have : l.1 = R.g.pre.length + k := by injection hty
      omega
  have hLP : Expr.LeavesBounded (Expr.mkAppN (.const ctor.1.name (tgtMajor out j).lvls) ds') :=
    leavesBounded_of_openers Gp.lb hleafP
  have hCP := Gp.ctxOk hwsP hleafP
  -- the constructor's type, at the rule's levels
  obtain ⟨tc, htc⟩ := inferTypeCore_mkAppN_fn_inv ds' hthd
  have hF : 1 ≤ F := inferTypeCore_pos htc
  obtain ⟨F₀, rfl⟩ : ∃ F₀, F = F₀ + 1 := ⟨F - 1, by omega⟩
  obtain ⟨ci, hci, -, rfl⟩ := ConLeche.Rules.inferTypeCore_const_inv_full htc
  obtain ⟨iT, hfindC, -, hread⟩ := hseam j r hr i ctor hctor
  rw [hfindC] at hci
  obtain rfl := Option.some.inj hci
  have hsp : ((ctor.1.type.instantiateLevelParams ctor.1.levelParams
      (tgtMajor out j).lvls).stripPis ds'.length).isSome := by
    rw [hdl', ← Rd.hnpc]
    exact Expr.stripPis_instantiateLevelParams_isSome _ _ _ (stripPis_isSome_of_lfpCtor hcov Rd hcAM)
  obtain ⟨dsT, hdsT, hfitP⟩ := teleFitPA_of_inferSpine mpC ψ ds' hthd htc hsp
    ⟨hwsP, hbP, hLP⟩ hCP
  -- the reading of the constructor's type, at the class's levels
  have hcons := List.mem_of_find?_eq_some hfindC
  have hwfC := mpC.base2.wf.consts _ hcons
  have hT : denote mpC.base2.acval envC ψ R.g.pre.length
      (ctor.1.type.instantiateLevelParams ctor.1.levelParams (tgtMajor out j).lvls)
      = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) := by
    rw [denote_instLevels mpC.base2.acval_params ψ]
    have hr0 := hread (Level.substFn ψ ctor.1.levelParams (tgtMajor out j).lvls)
    have hψj : blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj
        = blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i
            (Level.substFn ψ ctor.1.levelParams (tgtMajor out j).lvls) := by
      have h1 := hread ψj
      rw [denote_params_ext mpC.base2 (φ₁ := ψj)
        (φ₂ := Level.substFn ψ ctor.1.levelParams (tgtMajor out j).lvls) hlv' 0 ctor.1.type
        hwfC.2.1, hr0] at h1
      exact (Option.some.inj h1).symm
    rw [hψj]
    exact denote_depth_of_closed mpC.base2.acval_closed hwfC.1
      (fun k => denote_liftN_eq_self mpC.base2.cval_closed hwfC.1 hwfC.2.2.2.1 hr0 1 k) hr0 _
  -- the prefix fits its domains
  obtain ⟨-, -, -, -, hTyE, hlenRds, -, -, -⟩ := recStage_tyPis (V := V) mpC h hr ψ
  rw [hTyE, ← List.take_append_drop (pp.rulePrefixAt j)
    (blockRecRdsAV mpC.base2.acval envC pp (tgtRs out) ψ j), mkPisAV_append] at hmid
  have hspX := spineFit_of_teleFitPA (by
    rw [List.length_take, hlenRds, hxl]; have := blockRecHrPle (p := pp) h hj; omega) hmid
  have hsat : Sat V (blockRulePdomsAV mpC.base2.acval envC pp (tgtRs out) ψ j).reverse
      (consList (xs.map (interp V ρ)) ρ) := sat_of_spineFit_rev hspX
  obtain ⟨r0, hr0⟩ := hfitP _ hT _ hsat
  -- the readings are the rule's parameters'
  have hdsTE : dsT = tgtOutDsa mpC.base2.acval envC pp out ψ j := by
    rw [denoteSpine_eq_map hdsT, tgtOutDsa, show tgtRP pp j = R.g.pre.length from hrP]
    refine List.ext_getElem (by simp [hdl']) fun q h₁ h₂ => ?_
    simp only [List.getElem_map]
    have hq : q < (tgtMajor out j).ds.length := by simpa using h₂
    rw [denote_erasedEq (hargs q _ _ (List.getElem?_eq_getElem hq)
      (List.getElem?_eq_getElem (by simpa using h₁)))]
  subst hdsTE
  have hcl : Term.bvarsBelow 0 (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) :=
    bvarsBelow_of_reading (m := mpC.base2) (Expr.WScoped.of_not_hasFvar hwfC.1) hwfC.2.2.2.1
      (hread ψj)
  have hdl2 : (tgtOutDsa mpC.base2.acval envC pp out ψ j).length = (tgtMajor out j).nPc := by
    rw [tgtOutDsa, List.length_map, Rd.hnpc]
  have hpc : Rules.PiChain (tgtOutDsa mpC.base2.acval envC pp out ψ j).length
      (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψj) :=
    Rules.piChain_of_stripPis _ (by rw [hdl2]; exact stripPis_isSome_of_lfpCtor hcov Rd hcAM)
      (hread ψj)
  exact teleFitPA_move hcl hpc hr0 (by rw [hpl, hdl2]) fun q hq => hpv q (by rw [← hdl2]; exact hq)

set_option maxHeartbeats 4000000 in
/-- **`GenFit1` at every generated rule**: `genFit1_core`, with the class's level valuation
read off `GenLv` and the parameters' readings off `GenPs` — the prefix's leading values at a
member class (the class's frame is the prefix's first `nP` values, `GenClsRd.hfr`), the pins
read at the prefix at an outside one. -/
theorem genRecFit1
    (R : GenRecRun .verified F (ConLeche.mkFEnv env₁) env₁ (ConLeche.mkFEnv envC) pp nestedBit
      pos block out) (hg : ConLeche.ClassGenScoped R.g) (hcov : LfpCover mpC [])
    (h : ConLeche.RecStageG .verified F envC pp (tgtRs out))
    (hfind : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        ∃ iT, envC.find? ctor.1.name
          = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2 iT))
    (hseam : ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat), r.2.2.2[i]? = some ctor →
        ∃ iT, envC.find? ctor.1.name
            = some (.ctorInfo ctor.1 (ConLeche.tgtMajorsOf out j).nPc ctor.2 iT) ∧
        ConstsBound envC ctor.1.type ∧
        ∀ ψ : Name → Nat,
          denote mpC.base2.acval envC ψ 0 ctor.1.type
            = some (blockRecCtorTy mpC.base2.acval envC (tgtRs out) j i ψ))
    {pk : Nat → BlockMemberPick} {uOfD : Nat → (Name → Nat) → Nat}
    {ppsOf : Nat → (Name → Nat) → List Term} (hdR : d = blockDataOf V pp pk uOfD ppsOf)
    (hrdAll : ∀ c, c < (tgtRs out).length → pp.nP ≤ pp.rulePrefixAt c ∧
      ∃ cvI, GenClsRd mpC d Dc mc cvc pp out c cvI) :
    ∀ (j : Nat) (r : ConstantVal × List Expr × Nat × List (ConstantVal × Nat)),
      (tgtRs out)[j]? = some r → ∀ (i : Nat) (ctor : ConstantVal × Nat),
      r.2.2.2[i]? = some ctor → GenFit1 mpC pp out j i ctor := by
  intro j r hr i ctor hctor ψ ψj hlvG ρ xs ps mid hxl _ hmid _ hps
  have hj : j < (tgtRs out).length := (List.getElem?_eq_some_iff.mp hr).1
  obtain ⟨hnP, cvI, Rd⟩ := hrdAll j hj
  have hcAM : (tgtMajor out j).ctors[i]? = some ctor := by rw [← tgtRs_ctors hr]; exact hctor
  obtain ⟨-, -, hlpC, -⟩ := Rd.hctor i ctor hcAM
  obtain ⟨hpl, hpv⟩ := hps
  have hxV : (xs.map (interp V ρ)).length = tgtRP pp j := by rw [List.length_map, hxl]; rfl
  have hdl : (tgtOutDsa mpC.base2.acval envC pp out ψ j).length = (tgtMajor out j).nPc := by
    rw [← DenoteSpine.length_eq (Rd.hdsa ψ), Rd.hnpc]
  have hfr := Rd.hfr ψ ρ _ hxV
  unfold keyFrame at hfr
  rw [show (fun k => consList (xs.map (interp V ρ)) ρ (k + tgtRP pp j)) = ρ by
    funext k; rw [← hxV]; exact consList_apply_add _ _ _] at hfr
  cases hmb : (tgtMajor out j).member with
  | some t =>
    have hmS : (tgtMajor out j).member.isSome = true := by rw [hmb]; rfl
    -- the class's parameter count is the block's
    obtain ⟨-, cls, -, -, -, -, -, -, -, hMj, hgc⟩ := genRun_at R hj
    have hi' : cls < R.Ms.length := by rw [← hgc]; exact genRun_cls_lt R hj
    obtain ⟨key, M₀, nfs, hMs, -, ⟨CR⟩⟩ := genRun_class R hi'
    have hget : R.Ms.getD cls default = { M₀ with nfs := nfs } := by
      rw [List.getD_eq_getElem?_getD, hMs, Option.getD_some]
    rw [hget] at hMj
    have hm0 : M₀.member = some t := by rw [hMj] at hmb; exact hmb
    obtain ⟨-, hnPc⟩ := CR.major.member_facts hm0
    have hnPc' : (tgtMajor out j).nPc = d.nP := by
      rw [hMj]; subst hdR; exact hnPc
    simp only [tgtClsFr, hmS, ite_true] at hfr
    have hdn : d.nP = pp.nP := by subst hdR; rfl
    have hvals := consList_inj_of_length (by
      simp only [List.length_take, List.length_map, hdl, hnPc', hxl, hdn]; omega) hfr
    refine genFit1_core R hg hcov h hfind hseam hr hctor hnP Rd ψ ψj (fun q hq => ?_) ρ xs ps
      mid hxl hmid hpl fun q hq => ?_
    · have := hlvG q hq
      simp only [hmS, ite_true] at this
      have h2 := congrFun (Rd.hψ ψ) q
      simp only [tgtClsψ, hmS, ite_true] at h2
      rw [this, h2, hlpC]
    · have := hpv q hq
      simp only [hmS, ite_true] at this
      have hqd : q < d.nP := by omega
      have e1 := congrArg (fun l => l.getD q pt) hvals
      rw [List.getD_eq_getElem?_getD, List.getElem?_take_of_lt hqd, ← List.getD_eq_getElem?_getD,
        getD_map_interp (by omega), getD_map_interp (by rw [hdl]; omega)] at e1
      rw [this, e1]
  | none =>
    have hmS : (tgtMajor out j).member.isSome = false := by rw [hmb]; rfl
    refine genFit1_core R hg hcov h hfind hseam hr hctor hnP Rd ψ ψj (fun q hq => ?_) ρ xs ps
      mid hxl hmid hpl fun q hq => ?_
    · have := hlvG q hq
      simp only [hmS, Bool.false_eq_true, ite_false] at this
      exact this
    · have := hpv q hq
      simp only [hmS, Bool.false_eq_true, ite_false] at this
      exact this

end Out

end ConLeche.Model
