import Setlec.SetR.Interp2.Step2.IotaKitP

/-!
# The stuck-major rescues, P currency (task #161, iota tier)

`majorToCtor_stepR` (`Bridge/Major.lean`) at the validated-annotation
currency, plus the literal conversion that precedes it
(`litMajorToCtor`).  Together they are everything the ι clause does to
its major premise before the rule fires.

The v1 clause produces a `Red` derivation and therefore has to name
each rescue's rule (R12/R13/R14) with all its premises; the P clause
produces an `interp2` *equation*, so the three branches collapse to
their semantic content and nothing else:

* **R12, the K-flagged rescue** — the fabrication is certified against
  the major by proof irrelevance, and `ProofIrrelPQ` is the equation.
* **R13, the η rescue** — `structEtaCertWithP_step`
  (`Step2/CapsRowsP.lean`), the caps tier's own theorem at the
  certificate's shape.  This is the reuse the factoring was for: the
  rescue holds a certificate stated at the `tmaj` it already computed.
* **R14, the zero-field fallthrough** — `ProofIrrelPQ` again, on a
  fabrication whose spine is the reduced type's parameters verbatim.

## What the P currency charges, and what it refunds

It charges **grading**: `ProofIrrelPQ` and `structEtaCertWithP_step`
both want `AnnotOkP` of the fabricated spine, which v1 never had to
produce.  The refund is larger.  `InferClaims2P` *produces* a
subject's grading from its reading, so `certs_telePA` hands back the
gradings of every argument it certifies — and the fabrication's own
`iotaCerts` run is a certificate of exactly those arguments.  So one
`certs_telePA` call plus `annotOkP_mkAppN_of_fitA` grades each
fabrication outright, and in particular the caps tier's per-field
`hokProj` apparatus has **no counterpart here**: the projection spines
are graded because the certificate inferred them, not because their
own telescopes were re-walked.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps projFnName inferTypeCore whnf)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The `Nat`-literal major conversion -/

/-- **The `Nat`-literal major conversion is invisible to the validated
reading** (`denote_litToCtorIfNat`'s mirror; design §7.2's
"`litToCtorIfNat` contributes zero rules", one currency over). -/
theorem denoteP_litToCtorIfNat {acval : Name → (Name → Nat) → AVExpr}
    (d : Nat) (e : Expr) :
    denoteP acval env φ d (Setlec.litToCtorIfNat env e)
      = denoteP acval env φ d e := by
  match e with
  | .lit (.natVal n) =>
    rw [Setlec.litToCtorIfNat]
    by_cases hg : Setlec.natLitSupported env = true
    · rw [if_pos hg]
      match n with
      | 0 =>
        rw [Setlec.natLitToConstructor, denoteP_natZeroConst hg,
          denoteP_natLit hg]
        rfl
      | k + 1 =>
        rw [Setlec.natLitToConstructor, denoteP_app, denoteP_natSuccConst hg,
          denoteP_natLit hg, denoteP_natLit hg]
        rfl
    · rw [if_neg hg]
  | .lit (.strVal _) | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _
  | .app _ _ | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _
  | .proj _ _ _ => rfl

/-- The frame conditions survive the `Nat`-literal major conversion
(`frame_litToCtorIfNat`'s mirror; the constructor form is closed, so
all four are free). -/
theorem frame_litToCtorIfNatP {m : EnvS2Core V env} {d : Nat}
    {Δa : List AVExpr} {e : Expr}
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOkP m φ d Δa e) :
    Expr.WScoped d (Setlec.litToCtorIfNat env e) ∧
      (Setlec.litToCtorIfNat env e).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (Setlec.litToCtorIfNat env e) ∧
      CtxOkP m φ d Δa (Setlec.litToCtorIfNat env e) := by
  match e with
  | .lit (.natVal n) =>
    rw [Setlec.litToCtorIfNat]
    by_cases hg : Setlec.natLitSupported env = true
    · rw [if_pos hg]
      refine ⟨Setlec.natLitToConstructor_WScoped n,
        Setlec.natLitToConstructor_looseBVars n,
        fun l hl => ?_, ⟨hC.1, fun l hl => ?_⟩⟩ <;>
      · rw [Setlec.natLitToConstructor_fvarLeaves] at hl
        exact nomatch hl
    · rw [if_neg hg]; exact ⟨hws, hb, hLb, hC⟩
  | .lit (.strVal _) | .bvar _ | .fvar _ _ _ | .sort _ | .const _ _
  | .app _ _ | .lam _ _ _ _ | .forallE _ _ _ _ | .letE _ _ _ _
  | .proj _ _ _ => exact ⟨hws, hb, hLb, hC⟩

/-- **The literal major conversion's step.**  Two branches: the `Nat`
leg is invisible to the reading, the `String` leg expands the literal
to its constructor form (`denotePStrLit_of_guard`, the same reading)
and head-normalises it. -/
theorem litMajorToCtorP_stepP {m : EnvS2Core V env}
    (ihw : WhnfClaims2P μ m φ fuel) (hwreads : WhnfReadsP m μ φ fuel)
    {d : Nat} {Δa : List AVExpr} {e e₁ : Expr} {ea : AVExpr}
    (h : Setlec.litMajorToCtorP μ env fuel d e = .ok e₁)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOkP m φ d Δa e)
    (hea : denoteP m.acval env φ d e = some ea)
    (hok : ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea) :
    ∃ ea₁, denoteP m.acval env φ d e₁ = some ea₁ ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ ea₁) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ ea = interp2 V ρ ea₁) ∧
      Expr.WScoped d e₁ ∧ e₁.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₁ ∧ CtxOkP m φ d Δa e₁ := by
  rcases Setlec.litMajorToCtorP_inv h with rfl | ⟨s, rfl, hg, hred⟩
  · obtain ⟨hw', hb', hL', hC'⟩ := frame_litToCtorIfNatP hws hb hLb hC
    exact ⟨ea, by rw [denoteP_litToCtorIfNat]; exact hea, hok,
      fun _ _ => rfl, hw', hb', hL', hC'⟩
  · obtain ⟨hSC, hwc, hbc, hLc, hfv⟩ :=
      denotePStrLit_of_guard (m := m) d s hg hea
    have hCc : CtxOkP m φ d Δa (Setlec.strLitToConstructor s) :=
      ⟨hC.1, fun l hl => by rw [hfv] at hl; exact nomatch hl⟩
    obtain ⟨ea₁, hea₁⟩ := hwreads hred hwc hbc hLc hSC
    obtain ⟨hok₁, heq₁⟩ := ihw hred hwc hbc hLc hCc hSC hea₁ hok
    exact ⟨ea₁, hea₁, hok₁, heq₁,
      Setlec.whnf_WScoped m.base.wf fuel hred hwc,
      Setlec.whnf_looseBVars m.base.wf fuel hred hbc,
      fun l hl => hLc l (Setlec.whnf_fvarLeaves m.base.wf fuel hred l hl),
      hCc.of_subset (Setlec.whnf_fvarLeaves m.base.wf fuel hred)⟩

/-! ## The stuck-major rescue -/

/-- The stuck-major rescue's contract, P currency (`MajorStepR`'s
mirror: the `Red` derivation becomes an `interp2` equation plus the
reduct's grading). -/
def MajorStepP (μ : CheckMode) {env : Env} (m : EnvS2Core V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AVExpr} {recName : Name} {rules : List RecRule}
    {major major' : Expr} {vm : AVExpr},
    Setlec.majorToCtorP μ env fuel d recName rules major = .ok major' →
    Expr.WScoped d major → major.looseBVarsBounded 0 = true →
    Expr.LeavesBounded major → CtxOkP m φ d Δa major →
    denoteP m.acval env φ d major = some vm →
    (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ vm) →
    ∃ w, denoteP m.acval env φ d major' = some w ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ w) ∧
      (∀ ρ : Nat → V, Sat2 V Δa ρ → interp2 V ρ vm = interp2 V ρ w) ∧
      Expr.WScoped d major' ∧ major'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded major' ∧ CtxOkP m φ d Δa major'

/-- **`MajorStepP`, proved** (R12/R13/R14 and the identity
fallthrough). -/
theorem majorToCtorP_stepP {m : EnvS2Core V env}
    (hcaps : CapsOkP m) (hct : ConstTypeP m φ) (hav : AcvalValidP m)
    (ihw : WhnfClaims2P μ m φ fuel) (ihd : DefEqClaims2P μ m φ fuel)
    (ihi : InferClaims2P μ m φ fuel)
    (hreads : InferReadsP m μ φ fuel) (hwreads : WhnfReadsP m μ φ fuel) :
    MajorStepP μ m φ fuel := by
  intro d Δa recName rules major major' vm h hws hb hLb hC hvm hokm
  have hpi : ProofIrrelPQ μ m φ fuel :=
    proofIrrelPQ_of_claims ihw ihi hreads
      (unitIrrelPQ_of_claims ihw ihi hreads hwreads)
  rcases Setlec.majorToCtor_inv h with rfl | ⟨hwsB, hbB, hleafB, rl, cvj,
    cnP, cnF, tmaj₀, tmaj, T, us₀, ust, cvT, caps, hrules, hfcj, hpres,
    hfT, hitm, hwtm, hfnT, hcase⟩
  · exact ⟨vm, hvm, hokm, fun _ _ => rfl, hws, hb, hLb, hC⟩
  · -- the fabrication's frame conditions come with the inversion
    have hwF : Expr.WScoped d major' := Expr.WScoped.of_wscopedB hwsB
    have hLF : Expr.LeavesBounded major' := fun l hl =>
      hLb l (by
        have := List.all_eq_true.mp hleafB l hl
        simpa using this)
    have hCF : CtxOkP m φ d Δa major' :=
      hC.of_subset (fun l hl => by
        have := List.all_eq_true.mp hleafB l hl
        simpa using this)
    -- the major's type: inferred, read, graded, inhabited; then reduced
    have hwt0 : Expr.WScoped d tmaj₀ :=
      Setlec.inferTypeCore_WScoped m.base.wf fuel hitm hws
    have hbt0 : tmaj₀.looseBVarsBounded 0 = true :=
      Setlec.inferTypeCore_looseBVars m.base.wf fuel hitm hws hb hLb
    have hLt0 : Expr.LeavesBounded tmaj₀ := fun l hl =>
      hLb l (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel hitm hws l hl)
    have hCt0 : CtxOkP m φ d Δa tmaj₀ :=
      hC.of_subset (Setlec.inferTypeCore_fvarLeaves m.base.wf fuel hitm hws)
    obtain ⟨tmaj₀a, htmaj₀a⟩ :=
      hreads hitm hws hb hLb (LeafReadsP.of_ctxOkP hC) hvm
    obtain ⟨-, hokT0, hmemM⟩ := ihi hitm hws hb hLb hC hvm htmaj₀a
    obtain ⟨tmaja, htmaja⟩ := hwreads hwtm hwt0 hbt0 hLt0 htmaj₀a
    obtain ⟨hokTm, heqTm⟩ :=
      ihw hwtm hwt0 hbt0 hLt0 hCt0 htmaj₀a htmaja hokT0
    have hwr : Expr.WScoped d tmaj :=
      Setlec.whnf_WScoped m.base.wf fuel hwtm hwt0
    have hbr : tmaj.looseBVarsBounded 0 = true :=
      Setlec.whnf_looseBVars m.base.wf fuel hwtm hbt0
    have hLr : Expr.LeavesBounded tmaj := fun l hl =>
      hLt0 l (Setlec.whnf_fvarLeaves m.base.wf fuel hwtm l hl)
    have hCr : CtxOkP m φ d Δa tmaj :=
      hCt0.of_subset (Setlec.whnf_fvarLeaves m.base.wf fuel hwtm)
    have hmemMW : ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ vm ∈ˢ interp2 V ρ tmaja :=
      fun ρ hρ => (heqTm ρ hρ) ▸ hmemM ρ hρ
    -- the reduced type is the family applied to its parameters
    have hsave := htmaja
    rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
      (Setlec.Expr.mkAppN_getApp tmaj).symm, hfnT] at htmaja
    obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteP_mkAppN_inv htmaja
    -- the constructor's stored type, read and graded
    have hlenCj : ust.length = cvj.levelParams.length := by
      rcases hcase with ⟨-, -, hlpj, -⟩ | ⟨-, -, -, -, -, -, hlpj, -⟩
      · exact hlpj.symm
      · exact hlpj.symm
    obtain ⟨TVja, hTVja, hokTVja, hmemCj⟩ :=
      hct d rl.ctor _ ust hfcj (by exact hlenCj)
    dsimp only [Setlec.ConstantInfo.toConstantVal] at hTVja hmemCj
    have hwfj := m.base.wf _ (Setlec.SetR.Env.find?_mem hfcj)
    have hnfj : (cvj.type.instantiateLevelParams cvj.levelParams
        ust).hasFvar = false := by
      rw [Setlec.Expr.hasFvar_instantiateLevelParams]; exact hwfj.1
    have hbdj : (cvj.type.instantiateLevelParams cvj.levelParams
        ust).looseBVarsBounded 0 = true := by
      rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
      exact hwfj.2.2.2.1
    have hCj : CtxOkP m φ d Δa
        (cvj.type.instantiateLevelParams cvj.levelParams ust) :=
      ⟨hC.1, fun l hl => by
        rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfj] at hl
        exact nomatch hl⟩
    have hheadCj : denoteP m.acval env φ d (.const rl.ctor ust)
        = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) :=
      denoteP_const hfcj (by exact hlenCj)
    -- the fabricated spine's reading and grading, uniformly: the
    -- fabrication's own `iotaCerts` run certifies exactly its arguments,
    -- and `certs_telePA` returns their gradings with the fit
    have hfab : ∀ (fargs : List Expr) (fargsa : List AVExpr),
        Setlec.iotaCertsP μ env fuel d
            (cvj.type.instantiateLevelParams cvj.levelParams ust)
            fargs = .ok true →
        (∀ x ∈ fargs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x) →
        DenoteSpineP m.acval env φ d fargs fargsa →
        denoteP m.acval env φ d (Expr.mkAppN (.const rl.ctor ust) fargs)
            = some (AVExpr.mkAppN
              (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
              fargsa) ∧
          ∀ ρ : Nat → V, Sat2 V Δa ρ →
            AnnotOkP V ρ (AVExpr.mkAppN
              (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
              fargsa) := by
      intro fargs fargsa hcerts hframes hsp
      refine ⟨denoteP_mkAppN hsp hheadCj, fun ρ hρ => ?_⟩
      obtain ⟨resta, hfit, -, hokArgs⟩ :=
        certs_telePA ihd ihi hreads _ fargs fargsa TVja hcerts
          (Setlec.Expr.WScoped.of_not_hasFvar hnfj) hbdj
          (Setlec.Expr.LeavesBounded.of_not_hasFvar hnfj) hCj hTVja
          (fun σ _ => hokTVja σ) hframes hsp
      exact (annotOkP_mkAppN_of_fitA fargsa (hokTVja ρ)
        ⟨m.acval_ok2 _ _ ρ, hav _ _ ρ⟩
        (fun x hx => hokArgs x hx ρ hρ) (hmemCj ρ) (hfit ρ hρ)).1
    rcases hcase with ⟨hK, hcnF, hlpj, hcnP, hstrip, rfl, hcerts,
        ⟨tfab, hitfab, hdefab⟩, hirr⟩ |
      ⟨heta, hectr, hproj, hnz, hlenP, hlenU, hlpj, hstrip, rfl, hcerts,
        hetacase⟩
    · -- R12: the K-flagged rescue
      obtain ⟨hdF, hokF⟩ := hfab (tmaj.getAppArgs.take cnP) (tsa.take cnP)
        hcerts
        (fun x hx => frame_spineP hwr hbr hLr hCr x (List.mem_of_mem_take hx))
        (hspt.take cnP)
      exact ⟨_, hdF, hokF,
        fun ρ hρ => (hpi hirr hwF hbB hLF hws hb hLb hCF hC hdF hvm
          hokF hokm ρ hρ).symm,
        hwF, hbB, hLF, hCF⟩
    · -- R13/R14: the η-capable rescue
      have hspM : DenoteSpineP m.acval env φ d (tmaj.getAppArgs ++ [major])
          (tsa ++ [vm]) :=
        hspt.append (DenoteSpineP.cons hvm DenoteSpineP.nil)
      have hfrM : ∀ x ∈ tmaj.getAppArgs ++ [major],
          Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
            Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x := by
        intro x hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact frame_spineP hwr hbr hLr hCr x hx'
        · rcases List.mem_singleton.mp hx' with rfl
          exact ⟨hws, hb, hLb, hC⟩
      rcases hetacase with hcw | ⟨hnF0, hlpj', hirr⟩
      · -- R13: the η certificate identifies the fabrication with the major
        obtain ⟨c2, us2, cvc2, cnP2, cnF2, T2, ust2, cvT2, caps2, hfna2,
          hfc2, hlena2, hfnb2, hfT2, -, -, -, hefld2, -, -, -, hlenus2,
          hlpc2, -, -, -, hprojs, -, -, -⟩ := Setlec.structEtaCertWith_inv hcw
        have hTeq : T2 = T := by
          rw [hfnT] at hfnb2; exact (Setlec.Expr.const.inj hfnb2).1.symm
        have hUeq : ust2 = ust := by
          rw [hfnT] at hfnb2; exact (Setlec.Expr.const.inj hfnb2).2.symm
        rw [hTeq, hUeq] at hprojs
        rw [hTeq] at hfT2
        rw [hUeq] at hlenus2
        have hcvTeq : cvT2 = cvT := by
          rw [hfT] at hfT2
          exact ((ConstantInfo.indInfo.inj (Option.some.inj hfT2)).1).symm
        have hcapseq : caps2 = caps := by
          rw [hfT] at hfT2
          exact ((ConstantInfo.indInfo.inj (Option.some.inj hfT2)).2).symm
        rw [hcvTeq] at hprojs hlenus2
        rw [hcapseq] at hefld2
        -- the projection spines read (the certificate stores each
        -- projection function at the family's level arity)
        have hpfacts : ∀ j ∈ List.range caps.etaFields,
            denoteP m.acval env φ d
                (Expr.mkAppN (.const (projFnName T j) ust)
                  (tmaj.getAppArgs ++ [major]))
              = some (AVExpr.mkAppN
                  (m.acval (projFnName T j)
                    (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])) := by
          intro j hj
          obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp, -, -⟩ :=
            Setlec.structEtaProjCerts_inv _ hprojs j (by
              rw [List.mem_range] at hj ⊢; rw [← hefld2]; exact hj)
          refine denoteP_mkAppN hspM ?_
          rw [denoteP_const (acval := m.acval) (φ := φ) (d := d) hfp
            (show ust.length = (ConstantInfo.recInfo cvp mIp rPp
              rulesp).toConstantVal.levelParams.length from by
              show ust.length = cvp.levelParams.length
              rw [hlpp]; exact hlenus2)]
          show some (m.acval (projFnName T j)
            (Level.substFn φ cvp.levelParams ust)) = _
          rw [hlpp]
        have hspF : DenoteSpineP m.acval env φ d
            (Setlec.etaFabArgs T ust tmaj.getAppArgs major caps.etaFields)
            (tsa ++ (List.range caps.etaFields).map fun j =>
              AVExpr.mkAppN (m.acval (projFnName T j)
                (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])) := by
          rw [Setlec.etaFabArgs]
          exact hspt.append (DenoteSpineP.map_list _ hpfacts)
        have hfrF : ∀ x ∈ Setlec.etaFabArgs T ust tmaj.getAppArgs major
            caps.etaFields,
            Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
              Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x := by
          intro x hx
          rw [Setlec.etaFabArgs] at hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact frame_spineP hwr hbr hLr hCr x hx'
          · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
            refine ⟨Setlec.Expr.WScoped.mkAppN
                (Setlec.Expr.WScoped.of_not_hasFvar rfl)
                (fun y hy => (hfrM y hy).1),
              Setlec.looseBVarsBounded_mkAppN rfl
                (fun y hy => (hfrM y hy).2.1),
              fun l hl => ?_, ⟨hC.1, fun l hl => ?_⟩⟩ <;>
            · rcases Setlec.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
              · exact absurd hl' (by simp [Expr.fvarLeaves])
              · first
                | exact (hfrM y hy).2.2.1 l hly
                | exact (hfrM y hy).2.2.2.2 l hly
        obtain ⟨hdF0, hokF0⟩ := hfab _ _ hcerts hfrF hspF
        rw [hectr] at hdF0 hokF0
        refine ⟨_, hdF0, hokF0, fun ρ hρ => ?_, hwF, hbB, hLF, hCF⟩
        exact (structEtaCertWithP_step hcaps hct hav ihd ihi hreads hcw
          hwF hbB hLF hCF hws hb hLb hC hwr hbr hLr hCr hdF0 hvm hsave
          hokF0 hokm hokTm hmemMW ρ hρ).symm
      · -- R14: the zero-field fallthrough
        have hEmpty : Setlec.etaFabArgs T ust tmaj.getAppArgs major
            caps.etaFields = tmaj.getAppArgs := by
          rw [Setlec.etaFabArgs, hnF0]
          simp
        obtain ⟨hdF0, hokF0⟩ := hfab tmaj.getAppArgs tsa
          (by rw [← hEmpty]; exact hcerts)
          (frame_spineP hwr hbr hLr hCr) hspt
        have hdF : denoteP m.acval env φ d
            (Expr.mkAppN (.const caps.etaCtor ust)
              (Setlec.etaFabArgs T ust tmaj.getAppArgs major caps.etaFields))
            = some (AVExpr.mkAppN (m.acval caps.etaCtor
                (Level.substFn φ cvj.levelParams ust)) tsa) := by
          rw [hEmpty, ← hectr]; exact hdF0
        have hokF : ∀ ρ : Nat → V, Sat2 V Δa ρ →
            AnnotOkP V ρ (AVExpr.mkAppN (m.acval caps.etaCtor
              (Level.substFn φ cvj.levelParams ust)) tsa) := by
          rw [← hectr]; exact hokF0
        exact ⟨_, hdF, hokF,
          fun ρ hρ => (hpi hirr hwF hbB hLF hws hb hLb hCF hC hdF hvm
            hokF hokm ρ hρ).symm,
          hwF, hbB, hLF, hCF⟩

end Setlec.SetR.Interp2
