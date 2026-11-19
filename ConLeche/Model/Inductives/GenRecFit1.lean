module

public import ConLeche.Model.Inductives.GenRecFitBase
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

end ConLeche.Model
