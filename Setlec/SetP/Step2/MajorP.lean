import Setlec.SetP.Step2.IotaKitP
import Setlec.SetP.Step2.ProjPinsP

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
    obtain ⟨ea₁, hea₁⟩ := hwreads hred hwc hbc hLc
      (fun l hl => by rw [hfv] at hl; exact nomatch hl) hSC
    obtain ⟨hok₁, heq₁⟩ := ihw hred hwc hbc hLc hCc hSC hea₁ hok
    exact ⟨ea₁, hea₁, hok₁, heq₁,
      Setlec.whnf_WScoped m.wf fuel hred hwc,
      Setlec.whnf_looseBVars m.wf fuel hred hbc,
      fun l hl => hLc l (Setlec.whnf_fvarLeaves m.wf fuel hred l hl),
      hCc.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hred)⟩

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

/-- **The rescue's fabrication reads — the reads-only walk** (task
#172 B4).  With the certificate runs io-graded, per-argument
readability can no longer be extracted from them (a skipped position
is not traversed); instead the fabrication's parts read because the
major's own io-inferred type does (`InferReadsIOP` + `WhnfReadsP`),
and the projection spines are stored constants applied to those same
parts.  The leaf package of the fabrication is the subject's. -/
theorem majorToCtorP_reads {m : EnvS2Core V env}
    (ihw : WhnfReadsP m μ φ fuel) (ihio : InferReadsIOP m μ φ fuel)
    {d : Nat} {recName : Name} {rules : List Setlec.RecRule}
    {e e' : Expr} {ea : AVExpr}
    (h : Setlec.majorToCtorP μ env fuel d recName rules e = .ok e')
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hlr : LeafReadsP m φ d e)
    (hea : denoteP m.acval env φ d e = some ea) :
    (∃ w, denoteP m.acval env φ d e' = some w) ∧
      LeafReadsP m φ d e' := by
  rcases Setlec.majorToCtor_inv h with rfl | ⟨hwsB, hbB, hleafB, rl, cvj,
    cnP, cnF, tmaj₀, tmaj, T, us₀, ust, cvT, caps, hrules, hfcj, hpres,
    hfT, hitm, hwtm, hfnT, hcase⟩
  · exact ⟨⟨ea, hea⟩, hlr⟩
  · -- the major's io-inferred type reads, then its reduct
    have hitmL := inferTypeCoreIO_of_slot hitm
    have hwt0 : Expr.WScoped d tmaj₀ :=
      Setlec.inferTypeIO_WScoped m.wf fuel hitm hws
    have hbt0 : tmaj₀.looseBVarsBounded 0 = true :=
      Setlec.inferTypeIO_looseBVars m.wf fuel hitm hws hb hLb
    have hLt0 : Expr.LeavesBounded tmaj₀ := fun l hl =>
      hLb l (Setlec.inferTypeIO_fvarLeaves m.wf fuel hitm hws l hl)
    have hlrt0 : LeafReadsP m φ d tmaj₀ :=
      hlr.of_subset (Setlec.inferTypeIO_fvarLeaves m.wf fuel hitm hws)
    obtain ⟨t0a, ht0a⟩ := ihio hitmL hws hb hLb hlr hea
    obtain ⟨tma, htma⟩ := ihw hwtm hwt0 hbt0 hLt0 hlrt0 ht0a
    have hlrtm : LeafReadsP m φ d tmaj :=
      hlrt0.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hwtm)
    -- the reduced type's parameter spine reads
    rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
      (Setlec.Expr.mkAppN_getApp tmaj).symm, hfnT] at htma
    obtain ⟨vT, tsa, hvT, hspt, -⟩ := denoteP_mkAppN_inv htma
    have hlrTargs : ∀ x ∈ tmaj.getAppArgs, LeafReadsP m φ d x :=
      fun x hx => hlrtm.of_subset
        (fun l hl => Setlec.fvarLeaves_getAppArgs hx l hl)
    rcases hcase with ⟨hK, hcnF, hlpj, hcnP, hstrip, rfl, hcerts,
        ⟨tfab, hitfab, hdefab⟩, hirr⟩ |
      ⟨heta, hectr, hproj, hnz, hlenP, hlenU, hlpj, hstrip, rfl, hcerts,
        hetacase⟩
    · -- K: the parameters-only constructor application
      refine ⟨⟨_, denoteP_mkAppN (hspt.take cnP)
        (denoteP_const hfcj (show ust.length
          = (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
          from hlpj.symm))⟩, ?_⟩
      intro l hl
      rcases Setlec.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · exact absurd hl' (by simp [Expr.fvarLeaves])
      · exact hlrTargs y (List.mem_of_mem_take hy) l hly
    · -- η: parameters plus the stored projection spines
      -- each fabricated argument reads
      have hallF : ∀ x ∈ Setlec.etaFabArgsE env T ust tmaj.getAppArgs e
          caps.etaFields,
          (∃ xa, denoteP m.acval env φ d x = some xa) ∧
            LeafReadsP m φ d x := by
        intro x hx
        rw [Setlec.etaFabArgsE] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · obtain ⟨xa, hxa⟩ := hspt.mem x hx'
          exact ⟨⟨xa, hxa⟩, hlrTargs x hx'⟩
        · -- a fabricated projection, by entry kind (task #175 W4c)
          unfold Setlec.etaProjs at hx'
          by_cases htow : Setlec.towerSlotsAll env T caps.etaFields = true
          · -- a `.proj` node at a tower entry reads to the tower reading
            rw [if_pos htow] at hx'
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
            obtain ⟨entry, hfe, htw⟩ :=
              Setlec.towerSlotsAll_slot htow j (List.mem_range.mp hj)
            refine ⟨⟨_, denoteP_proj_tower hfe htw hea⟩, ?_⟩
            intro l hl
            exact hlr l (by simpa [Expr.fvarLeaves] using hl)
          rw [if_neg htow] at hx'
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
          -- the projection function is stored (the R13 certificate
          -- pins it); at zero fields the range is empty
          rcases hetacase with hcw | ⟨hnF0, hlpj', hirr⟩
          · obtain ⟨c2, us2, cvc2, cnP2, cnF2, T2, ust2, cvT2, caps2,
              hfna2, hfc2, hlena2, hfnb2, hfT2, -, -, -, hefld2, -, -, -,
              hlenus2, hlpc2, -, hslots2, -, -, hprojs, -, -, -⟩ :=
              Setlec.structEtaCertWith_inv hcw
            have hTeq : T2 = T := by
              rw [hfnT] at hfnb2
              exact (Setlec.Expr.const.inj hfnb2).1.symm
            have hUeq : ust2 = ust := by
              rw [hfnT] at hfnb2
              exact (Setlec.Expr.const.inj hfnb2).2.symm
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
            rw [hTeq, ← hefld2] at hslots2
            obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp⟩ : ∃ cvp mIp rPp rulesp,
                env.find? (projFnName T j)
                  = some (.recInfo cvp mIp rPp rulesp) ∧
                cvp.levelParams = cvT.levelParams := by
              rcases Setlec.structEtaProjCerts_inv _ hprojs j (by
                  rw [List.mem_range] at hj ⊢; rw [← hefld2]; exact hj) with
                ⟨cvp, mIp, rPp, rulesp, hfp, hlpp, -, -⟩ |
                ⟨entry, hfp, -, -, -, -⟩
              · exact ⟨cvp, mIp, rPp, rulesp, hfp, hlpp⟩
              · exfalso
                have hrec : Setlec.recSlotsAll env T caps.etaFields = true := by
                  simpa [htow] using hslots2
                obtain ⟨cvp, mIp, rPp, rulesp, hfr⟩ :=
                  Setlec.recSlotsAll_slot hrec j (List.mem_range.mp hj)
                rw [hfp] at hfr
                exact nomatch hfr
            have hspM : DenoteSpineP m.acval env φ d
                (tmaj.getAppArgs ++ [e]) (tsa ++ [ea]) :=
              hspt.append (DenoteSpineP.cons hea DenoteSpineP.nil)
            refine ⟨⟨_, denoteP_mkAppN hspM
              (denoteP_const hfp (show ust.length
                = (ConstantInfo.recInfo cvp mIp rPp
                    rulesp).toConstantVal.levelParams.length from by
                show ust.length = cvp.levelParams.length
                rw [hlpp]; exact hlenus2))⟩, ?_⟩
            intro l hl
            rcases Setlec.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
            · exact absurd hl' (by simp [Expr.fvarLeaves])
            · rcases List.mem_append.mp hy with hy' | hy'
              · exact hlrTargs y hy' l hly
              · rcases List.mem_singleton.mp hy' with rfl
                exact hlr l hly
          · rw [List.mem_range, hnF0] at hj
            exact absurd hj (Nat.not_lt_zero j)
      -- assemble the spine
      have hspF : ∃ ys, DenoteSpineP m.acval env φ d
          (Setlec.etaFabArgsE env T ust tmaj.getAppArgs e caps.etaFields)
          ys := by
        have hall := fun x hx => (hallF x hx).1
        revert hall
        generalize Setlec.etaFabArgsE env T ust tmaj.getAppArgs e
          caps.etaFields = args
        intro hall
        induction args with
        | nil => exact ⟨[], .nil⟩
        | cons x xs ih =>
          obtain ⟨xa, hxa⟩ := hall x List.mem_cons_self
          obtain ⟨ys, hys⟩ :=
            ih (fun y hy => hall y (List.mem_cons_of_mem x hy))
          exact ⟨xa :: ys, .cons hxa hys⟩
      obtain ⟨ys, hspF⟩ := hspF
      refine ⟨⟨_, denoteP_mkAppN hspF
        (denoteP_const (hectr ▸ hfcj) (show ust.length
          = (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
          from hlpj.symm))⟩, ?_⟩
      intro l hl
      rcases Setlec.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · exact absurd hl' (by simp [Expr.fvarLeaves])
      · exact (hallF y hy).2 l hly

/-- **`MajorStepP`, proved** (R12/R13/R14 and the identity
fallthrough). -/
theorem majorToCtorP_stepP {m : EnvS2Core V env}
    (hcaps : CapsOkP m) (htower : TowerOkP m φ) (hct : ConstTypeP m φ) (hav : AcvalValidP m)
    (ihw : WhnfClaims2P μ m φ fuel) (ihd : DefEqClaims2P μ m φ fuel)
    (ihis : InferClaimsIOS2P μ m φ fuel)
    (hsss : SortSemAtIOSP m μ φ fuel)
    (hexi : InferExistsIOSP μ m φ fuel)
    (hreads_ios : InferReadsIOSP m μ φ fuel)
    (hwreads : WhnfReadsP m μ φ fuel) :
    MajorStepP μ m φ fuel := by
  intro d Δa recName rules major major' vm h hws hb hLb hC hvm hokm
  have hpi : ProofIrrelPQ μ m φ fuel :=
    proofIrrelPQ_of_claims ihis hsss hreads_ios
      (unitIrrelPQ_of_claims ihw ihis hreads_ios hwreads)
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
      Setlec.inferTypeIO_WScoped m.wf fuel hitm hws
    have hbt0 : tmaj₀.looseBVarsBounded 0 = true :=
      Setlec.inferTypeIO_looseBVars m.wf fuel hitm hws hb hLb
    have hLt0 : Expr.LeavesBounded tmaj₀ := fun l hl =>
      hLb l (Setlec.inferTypeIO_fvarLeaves m.wf fuel hitm hws l hl)
    have hCt0 : CtxOkP m φ d Δa tmaj₀ :=
      hC.of_subset (Setlec.inferTypeIO_fvarLeaves m.wf fuel hitm hws)
    obtain ⟨tmaj₀a, htmaj₀a⟩ :=
      hexi hitm hws hb hLb hC hvm
    obtain ⟨hokT0, hmemM⟩ := ihis hitm hws hb hLb hC hvm htmaj₀a hokm
    obtain ⟨tmaja, htmaja⟩ := hwreads hwtm hwt0 hbt0 hLt0
      (LeafReadsP.of_ctxOkP hCt0) htmaj₀a
    obtain ⟨hokTm, heqTm⟩ :=
      ihw hwtm hwt0 hbt0 hLt0 hCt0 htmaj₀a htmaja hokT0
    have hwr : Expr.WScoped d tmaj :=
      Setlec.whnf_WScoped m.wf fuel hwtm hwt0
    have hbr : tmaj.looseBVarsBounded 0 = true :=
      Setlec.whnf_looseBVars m.wf fuel hwtm hbt0
    have hLr : Expr.LeavesBounded tmaj := fun l hl =>
      hLt0 l (Setlec.whnf_fvarLeaves m.wf fuel hwtm l hl)
    have hCr : CtxOkP m φ d Δa tmaj :=
      hCt0.of_subset (Setlec.whnf_fvarLeaves m.wf fuel hwtm)
    have hmemMW : ∀ ρ : Nat → V, Sat2 V Δa ρ →
        interp2 V ρ vm ∈ˢ interp2 V ρ tmaja :=
      fun ρ hρ => (heqTm ρ hρ) ▸ hmemM ρ hρ
    -- the reduced type is the family applied to its parameters
    have hsave := htmaja
    rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
      (Setlec.Expr.mkAppN_getApp tmaj).symm, hfnT] at htmaja
    obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteP_mkAppN_inv htmaja
    obtain ⟨-, hoTs⟩ := hoistP_spine tsa hokTm
    -- the constructor's stored type, read and graded
    have hlenCj : ust.length = cvj.levelParams.length := by
      rcases hcase with ⟨-, -, hlpj, -⟩ | ⟨-, -, -, -, -, -, hlpj, -⟩
      · exact hlpj.symm
      · exact hlpj.symm
    obtain ⟨TVja, hTVja, hokTVja, hmemCj⟩ :=
      hct d rl.ctor _ ust hfcj (by exact hlenCj)
    dsimp only [Setlec.ConstantInfo.toConstantVal] at hTVja hmemCj
    have hwfj := m.wf _ (Setlec.SetR.Env.find?_mem hfcj)
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
        (∀ x ∈ fargsa, ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ x) →
        denoteP m.acval env φ d (Expr.mkAppN (.const rl.ctor ust) fargs)
            = some (AVExpr.mkAppN
              (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
              fargsa) ∧
          ∀ ρ : Nat → V, Sat2 V Δa ρ →
            AnnotOkP V ρ (AVExpr.mkAppN
              (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
              fargsa) := by
      intro fargs fargsa hcerts hframes hsp hoks
      refine ⟨denoteP_mkAppN hsp hheadCj, fun ρ hρ => ?_⟩
      obtain ⟨resta, hfit, -, hokArgs⟩ :=
        certs_telePA ihd ihis hexi _ fargs fargsa TVja hcerts
          (Setlec.Expr.WScoped.of_not_hasFvar hnfj) hbdj
          (Setlec.Expr.LeavesBounded.of_not_hasFvar hnfj) hCj hTVja
          (fun σ _ => hokTVja σ) hframes hsp hoks
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
        (fun x hx => hoTs x (List.mem_of_mem_take hx))
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
          hlpc2, -, hslots2, -, -, hprojs, -, -, -⟩ := Setlec.structEtaCertWith_inv hcw
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
        rw [hTeq, ← hefld2] at hslots2
        have hokMs : ∀ x ∈ tsa ++ [vm], ∀ ρ : Nat → V, Sat2 V Δa ρ →
            AnnotOkP V ρ x := by
          intro x hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact hoTs x hx'
          · rcases List.mem_singleton.mp hx' with rfl; exact hokm
        by_cases htow : Setlec.towerSlotsAll env T caps.etaFields = true
        · -- TOWER-BACKED SLOTS (task #175 W4c): the fabricated
          -- projections are `.proj T j major` nodes reading to the tower
          -- readings, graded by each entry's typing law
          have hvT' : vT = m.acval T (Level.substFn φ cvT.levelParams ust) := by
            rw [denoteP_const hfT (show ust.length
              = (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
              from hlenus2)] at hvT
            exact (Option.some.inj hvT).symm
          have hslotE : ∀ j, j < caps.etaFields → ∃ entry : ProjEntry,
              env.findProj? T j = some entry ∧ entry.tower = true ∧
              entry.levelParams = cvT.levelParams ∧
              (entry.ty.stripPis (tmaj.getAppArgs.length + 1)).isSome = true := by
            intro j hj
            rcases Setlec.structEtaProjCerts_inv _ hprojs j (by
                rw [List.mem_range, ← hefld2]; exact hj) with
              ⟨cvp, mIp, rPp, rulesp, hfp, -, -, -⟩ |
              ⟨entry, hfp, htw, hlpe, hstrpe, -⟩
            · exfalso
              obtain ⟨e, hfe, -⟩ := Setlec.towerSlotsAll_slot htow j hj
              have := Setlec.Env.findProj?_some hfe
              rw [hfp] at this
              exact nomatch this
            · exact ⟨entry, by unfold Setlec.Env.findProj?; rw [hfp], htw, hlpe,
                hstrpe⟩
          have hpfacts : ∀ j ∈ List.range caps.etaFields,
              denoteP m.acval env φ d (.proj T j major) = some (projAV j vm) := by
            intro j hj
            obtain ⟨entry, hfe, htw, -, -⟩ := hslotE j (List.mem_range.mp hj)
            exact denoteP_proj_tower hfe htw hvm
          have hokProj : ∀ j ∈ List.range caps.etaFields, ∀ ρ : Nat → V,
              Sat2 V Δa ρ → AnnotOkP V ρ (projAV j vm) := by
            intro j hj ρ hρ
            obtain ⟨entry, hfe, htw, hlpe, hstrpe⟩ :=
              hslotE j (List.mem_range.mp hj)
            obtain ⟨-, -, -, -, ⟨cvTj, capsTj, hfTj, -, hetaj, -, hparj, -⟩, hO5j,
              -, -, -, hlawj, -⟩ := htower T j entry hfe htw
            have hcapsTj : capsTj = caps := by
              rw [hfT] at hfTj
              exact (ConstantInfo.indInfo.inj (Option.some.inj hfTj)).2.symm
            rw [hcapsTj] at hparj hetaj
            have hgj : TowerGuardAt φ entry ust :=
              towerGuardAt_of hO5j
                (fun hp => by rw [heta, hp] at hetaj; exact nomatch hetaj)
            obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlawj ust (by rw [hlpe]; exact hlenus2)
            obtain ⟨hTad, -⟩ := towerEntry_ty_at_depth hfe hTa
            -- the entry type's reading is a ∀-chain of the subject
            -- list's length, so it peels along it
            have hpc : PiChainP (tsa ++ [vm]).length Ta := by
              rw [List.length_append, List.length_singleton, ← hspt.length]
              exact piChainP_of_stripPis _
                (Setlec.Expr.stripPis_instantiateLevelParams_isSome
                  entry.levelParams ust _ hstrpe) (hTad d)
            obtain ⟨restj, hpeel⟩ := peelPis_of_piChainP _ hpc
            have hlenVs : tsa.length = entry.numParams := by
              rw [← hspt.length, hlenP, hparj]
            rw [hlpe, ← hvT'] at hA
            exact (hA hgj ρ tsa vm restj hlenVs (hokTm ρ hρ) (hokm ρ hρ)
              (hmemMW ρ hρ) hpeel).1
          have hspF : DenoteSpineP m.acval env φ d
              (Setlec.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)
              (tsa ++ (List.range caps.etaFields).map fun j => projAV j vm) := by
            rw [Setlec.etaFabArgsE, Setlec.etaProjs, if_pos htow]
            exact hspt.append (DenoteSpineP.map_list _ hpfacts)
          have hfrF : ∀ x ∈ Setlec.etaFabArgsE env T ust tmaj.getAppArgs major
              caps.etaFields,
              Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
                Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x := by
            intro x hx
            rw [Setlec.etaFabArgsE, Setlec.etaProjs, if_pos htow] at hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact frame_spineP hwr hbr hLr hCr x hx'
            · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
              exact ⟨by simpa [Expr.WScoped] using hws,
                by simpa [Expr.looseBVarsBounded] using hb,
                fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl),
                ⟨hC.1, fun l hl => hC.2 l (by simpa [Expr.fvarLeaves] using hl)⟩⟩
          have hoksF : ∀ x ∈ (tsa ++ (List.range caps.etaFields).map fun j =>
              projAV j vm),
              ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ x := by
            intro x hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact hoTs x hx'
            · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
              exact hokProj j hj
          obtain ⟨hdF0, hokF0⟩ := hfab _ _ hcerts hfrF hspF hoksF
          rw [hectr] at hdF0 hokF0
          refine ⟨_, hdF0, hokF0, fun ρ hρ => ?_, hwF, hbB, hLF, hCF⟩
          exact (structEtaCertWithP_step hcaps htower hct hav ihd ihis hexi hcw
            hwF hbB hLF hCF hws hb hLb hC hwr hbr hLr hCr hdF0 hvm hsave
            hokF0 hokm hokTm hmemMW ρ hρ).symm
        · -- PROJECTION-FUNCTION SLOTS: the projection spines read (the
          -- certificate stores each projection function at the family's
          -- level arity)
          have hrec : Setlec.recSlotsAll env T caps.etaFields = true := by
            simpa [htow] using hslots2
          have hslotR : ∀ j ∈ List.range caps.etaFields, ∃ cvp mIp rPp rulesp,
              env.find? (projFnName T j) = some (.recInfo cvp mIp rPp rulesp) ∧
              cvp.levelParams = cvT.levelParams ∧
              (cvp.type.stripPis (tmaj.getAppArgs.length + 1)).isSome = true ∧
              Setlec.iotaCertsP μ env fuel d
                (cvp.type.instantiateLevelParams cvp.levelParams ust)
                (tmaj.getAppArgs ++ [major]) = .ok true := by
            intro j hj
            rcases Setlec.structEtaProjCerts_inv _ hprojs j (by
                rw [List.mem_range] at hj ⊢; rw [← hefld2]; exact hj) with
              ⟨cvp, mIp, rPp, rulesp, hfp, hlpj, hstrpj, hicj⟩ |
              ⟨entry, hfp, -, -, -, -⟩
            · exact ⟨cvp, mIp, rPp, rulesp, hfp, hlpj, hstrpj, hicj⟩
            · exfalso
              obtain ⟨cvp, mIp, rPp, rulesp, hfr⟩ :=
                Setlec.recSlotsAll_slot hrec j (List.mem_range.mp hj)
              rw [hfp] at hfr
              exact nomatch hfr
          have hpfacts : ∀ j ∈ List.range caps.etaFields,
              denoteP m.acval env φ d
                  (Expr.mkAppN (.const (projFnName T j) ust)
                    (tmaj.getAppArgs ++ [major]))
                = some (AVExpr.mkAppN
                    (m.acval (projFnName T j)
                      (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])) := by
            intro j hj
            obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp, -, -⟩ := hslotR j hj
            refine denoteP_mkAppN hspM ?_
            rw [denoteP_const (acval := m.acval) (φ := φ) (d := d) hfp
              (show ust.length = (ConstantInfo.recInfo cvp mIp rPp
                rulesp).toConstantVal.levelParams.length from by
                show ust.length = cvp.levelParams.length
                rw [hlpp]; exact hlenus2)]
            show some (m.acval (projFnName T j)
              (Level.substFn φ cvp.levelParams ust)) = _
            rw [hlpp]
          have hokProj : ∀ j ∈ List.range caps.etaFields, ∀ ρ : Nat → V,
              Sat2 V Δa ρ → AnnotOkP V ρ (AVExpr.mkAppN
                (m.acval (projFnName T j)
                  (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])) := by
            intro j hj ρ hρ
            obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp, hstrp, hicj⟩ := hslotR j hj
            have hlenp : ust.length = cvp.levelParams.length := by
              rw [hlpp]; exact hlenus2
            obtain ⟨tpa, htpa, hoktpa, hmemp⟩ :=
              hct d (projFnName T j) _ ust hfp hlenp
            have hwfp := m.wf _ (Setlec.SetR.Env.find?_mem hfp)
            have hnfp : (cvp.type.instantiateLevelParams cvp.levelParams
                ust).hasFvar = false := by
              rw [Setlec.Expr.hasFvar_instantiateLevelParams]; exact hwfp.1
            have hbdp : (cvp.type.instantiateLevelParams cvp.levelParams
                ust).looseBVarsBounded 0 = true := by
              rw [Setlec.Expr.looseBVarsBounded_instantiateLevelParams]
              exact hwfp.2.2.2.1
            obtain ⟨restp, hfitp, -, -⟩ :=
              certs_telePA ihd ihis hexi _ (tmaj.getAppArgs ++ [major])
                (tsa ++ [vm]) tpa hicj
                (Setlec.Expr.WScoped.of_not_hasFvar hnfp) hbdp
                (Setlec.Expr.LeavesBounded.of_not_hasFvar hnfp)
                ⟨hC.1, fun l hl => by
                  rw [Setlec.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfp]
                    at hl
                  exact nomatch hl⟩
                htpa (fun τ _ => hoktpa τ) hfrM hspM hokMs
            refine (annotOkP_mkAppN_of_fitA (tsa ++ [vm]) (hoktpa ρ)
              ⟨m.acval_ok2 _ _ ρ, hav _ _ ρ⟩
              (fun x hx => hokMs x hx ρ hρ) ?_ (hfitp ρ hρ)).1
            have := hmemp ρ
            dsimp only [Setlec.ConstantInfo.toConstantVal] at this
            rwa [hlpp] at this
          have hspF : DenoteSpineP m.acval env φ d
              (Setlec.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)
              (tsa ++ (List.range caps.etaFields).map fun j =>
                AVExpr.mkAppN (m.acval (projFnName T j)
                  (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])) := by
            rw [Setlec.etaFabArgsE, Setlec.etaProjs, if_neg htow]
            exact hspt.append (DenoteSpineP.map_list _ hpfacts)
          have hfrF : ∀ x ∈ Setlec.etaFabArgsE env T ust tmaj.getAppArgs major
              caps.etaFields,
              Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
                Expr.LeavesBounded x ∧ CtxOkP m φ d Δa x := by
            intro x hx
            rw [Setlec.etaFabArgsE, Setlec.etaProjs, if_neg htow] at hx
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
          have hoksF : ∀ x ∈ (tsa ++ (List.range caps.etaFields).map fun j =>
              AVExpr.mkAppN (m.acval (projFnName T j)
                (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])),
              ∀ ρ : Nat → V, Sat2 V Δa ρ → AnnotOkP V ρ x := by
            intro x hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact hoTs x hx'
            · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
              exact hokProj j hj
          obtain ⟨hdF0, hokF0⟩ := hfab _ _ hcerts hfrF hspF hoksF
          rw [hectr] at hdF0 hokF0
          refine ⟨_, hdF0, hokF0, fun ρ hρ => ?_, hwF, hbB, hLF, hCF⟩
          exact (structEtaCertWithP_step hcaps htower hct hav ihd ihis hexi hcw
            hwF hbB hLF hCF hws hb hLb hC hwr hbr hLr hCr hdF0 hvm hsave
            hokF0 hokm hokTm hmemMW ρ hρ).symm
      · -- R14: the zero-field fallthrough
        have hEmpty : Setlec.etaFabArgsE env T ust tmaj.getAppArgs major
            caps.etaFields = tmaj.getAppArgs := by
          rw [Setlec.etaFabArgsE, Setlec.etaProjs, hnF0]
          simp
        obtain ⟨hdF0, hokF0⟩ := hfab tmaj.getAppArgs tsa
          (by rw [← hEmpty]; exact hcerts)
          (frame_spineP hwr hbr hLr hCr) hspt hoTs
        have hdF : denoteP m.acval env φ d
            (Expr.mkAppN (.const caps.etaCtor ust)
              (Setlec.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
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
