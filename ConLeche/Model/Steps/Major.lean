module

public import ConLeche.Model.Steps.IotaKit
import ConLeche.Model.Steps.Stuck
import ConLeche.Verify.Denote
import ConLeche.Verify.Denote.OpenVars
import ConLeche.Verify.Denote.VClosed
public section

/-!
# The stuck-major rescues, P currency (task #161, iota tier)

`majorToCtor_stepR` (`Bridge/Major.lean`) at the validated-annotation
currency, plus the literal conversion that precedes it
(`litMajorToCtor`).  Together they are everything the ι clause does to
its major premise before the rule fires.

The v1 clause produces a `Red` derivation and therefore has to name
each rescue's rule (R12/R13/R14) with all its premises; the P clause
produces an `interp` *equation*, so the three branches collapse to
their semantic content and nothing else:

* **R12, the K-flagged rescue** — the fabrication is certified against
  the major by proof irrelevance, and `ProofIrrelPQ` is the equation.
* **R13, the η rescue** — `structEtaCertWithFueled_step`
  (`Steps/CapsRows.lean`), the caps tier's own theorem at the
  certificate's shape.  This is the reuse the factoring was for: the
  rescue holds a certificate stated at the `tmaj` it already computed.
* **R14, the zero-field fallthrough** — `ProofIrrelPQ` again, on a
  fabrication whose spine is the reduced type's parameters verbatim.

## What the P currency charges, and what it refunds

It charges **grading**: `ProofIrrelPQ` and `structEtaCertWithFueled_step`
both want `WellDenotedV` of the fabricated spine, which v1 never had to
produce.  The refund is larger.  `InferClaim` *produces* a
subject's grading from its reading, so `certs_telePA` hands back the
gradings of every argument it certifies — and the fabrication's own
`iotaCerts` run is a certificate of exactly those arguments.  So one
`certs_telePA` call plus `wellDenotedV_mkAppN_of_fitA` grades each
fabrication outright, and in particular the caps tier's per-field
`hokProj` apparatus has **no counterpart here**: the projection spines
are graded because the certificate inferred them, not because their
own telescopes were re-walked.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  RecRule IndCaps projFnName inferTypeCore whnf)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat} {fuel : Nat}

/-! ## The `Nat`-literal major conversion -/

/-- **The `Nat`-literal major conversion is invisible to the validated
reading** (`denote_litToCtorIfNat`'s mirror; design §7.2's
"`litToCtorIfNat` contributes zero rules", one currency over). -/
theorem denoteMeta_litToCtorIfNat {acval : Name → (Name → Nat) → AnnotTerm}
    (d : Nat) (e : Expr) :
    denoteMeta acval env φ d (ConLeche.litToCtorIfNat env e)
      = denoteMeta acval env φ d e := by
  match e with
  | .lit (.natVal n) =>
    rw [ConLeche.litToCtorIfNat]
    by_cases hg : ConLeche.natLitSupported env = true
    · rw [if_pos hg]
      match n with
      | 0 =>
        rw [ConLeche.natLitToConstructor, denoteMeta_natZeroConst hg,
          denoteMeta_natLit hg]
        rfl
      | k + 1 =>
        rw [ConLeche.natLitToConstructor, denoteMeta_app, denoteMeta_natSuccConst hg,
          denoteMeta_natLit hg, denoteMeta_natLit hg]
        rfl
    · rw [if_neg hg]
  | .lit (.strVal _) | .bvar _ | .fvar _ _ | .sort _ | .const _ _
  | .app _ _ | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _
  | .proj _ _ _ => rfl

/-- The frame conditions survive the `Nat`-literal major conversion
(`frame_litToCtorIfNat`'s mirror; the constructor form is closed, so
all four are free). -/
theorem frame_litToCtorIfNat {m : EnvModel V env} {d : Nat}
    {Δa : List AnnotTerm} {e : Expr}
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOk m φ d Δa e) :
    Expr.WScoped d (ConLeche.litToCtorIfNat env e) ∧
      (ConLeche.litToCtorIfNat env e).looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded (ConLeche.litToCtorIfNat env e) ∧
      CtxOk m φ d Δa (ConLeche.litToCtorIfNat env e) := by
  match e with
  | .lit (.natVal n) =>
    rw [ConLeche.litToCtorIfNat]
    by_cases hg : ConLeche.natLitSupported env = true
    · rw [if_pos hg]
      refine ⟨ConLeche.natLitToConstructor_WScoped n,
        ConLeche.natLitToConstructor_looseBVars n,
        fun l hl => ?_, ⟨hC.1, fun l hl => ?_⟩⟩ <;>
      · rw [ConLeche.natLitToConstructor_fvarLeaves] at hl
        exact nomatch hl
    · rw [if_neg hg]; exact ⟨hws, hb, hLb, hC⟩
  | .lit (.strVal _) | .bvar _ | .fvar _ _ | .sort _ | .const _ _
  | .app _ _ | .lam _ _ _ | .forallE _ _ _ | .letE _ _ _
  | .proj _ _ _ => exact ⟨hws, hb, hLb, hC⟩

/-- **The literal major conversion's step.**  Two branches: the `Nat`
leg is invisible to the reading, the `String` leg expands the literal
to its constructor form (`denotePStrLit_of_guard`, the same reading)
and head-normalises it. -/
theorem litMajorToCtorFueled_step {m : EnvModel V env}
    (ihw : WhnfClaim μ m φ fuel) (hwreads : WhnfReads m μ φ fuel)
    {d : Nat} {Δa : List AnnotTerm} {e e₁ : Expr} {ea : AnnotTerm}
    (h : ConLeche.litMajorToCtorFueled μ env fuel d e = .ok e₁)
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hC : CtxOk m φ d Δa e)
    (hea : denoteMeta m.acval env φ d e = some ea)
    (hok : ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea) :
    ∃ ea₁, denoteMeta m.acval env φ d e₁ = some ea₁ ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ ea₁) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ ea = interp V ρ ea₁) ∧
      Expr.WScoped d e₁ ∧ e₁.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded e₁ ∧ CtxOk m φ d Δa e₁ := by
  rcases ConLeche.litMajorToCtorFueled_inv h with rfl | ⟨s, rfl, hg, hred⟩
  · obtain ⟨hw', hb', hL', hC'⟩ := frame_litToCtorIfNat hws hb hLb hC
    exact ⟨ea, by rw [denoteMeta_litToCtorIfNat]; exact hea, hok,
      fun _ _ => rfl, hw', hb', hL', hC'⟩
  · obtain ⟨hSC, hwc, hbc, hLc, hfv⟩ :=
      denotePStrLit_of_guard (m := m) d s hg hea
    have hCc : CtxOk m φ d Δa (ConLeche.strLitToConstructor s) :=
      ⟨hC.1, fun l hl => by rw [hfv] at hl; exact nomatch hl⟩
    obtain ⟨ea₁, hea₁⟩ := hwreads hred hwc hbc hLc
      (fun l hl => by rw [hfv] at hl; exact nomatch hl) hSC
    obtain ⟨hok₁, heq₁⟩ := ihw hred hwc hbc hLc hCc hSC hea₁ hok
    exact ⟨ea₁, hea₁, hok₁, heq₁,
      ConLeche.whnf_WScoped m.wf fuel hred hwc,
      ConLeche.whnf_looseBVars m.wf fuel hred hbc,
      fun l hl => hLc l (ConLeche.whnf_fvarLeaves m.wf fuel hred l hl),
      hCc.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hred)⟩

/-! ## The stuck-major rescue -/

/-- The stuck-major rescue's contract, P currency (`MajorStepR`'s
mirror: the `Red` derivation becomes an `interp` equation plus the
reduct's grading). -/
@[expose] def MajorStep (μ : CheckMode) {env : Env} (m : EnvModel V env)
    (φ : Name → Nat) (fuel : Nat) : Prop :=
  ∀ {d : Nat} {Δa : List AnnotTerm} {recName : Name} {rules : List RecRule}
    {major major' : Expr} {vm : AnnotTerm},
    ConLeche.majorToCtorFueled μ env fuel d recName rules major = .ok major' →
    (∃ (cv : ConstantVal) (mI rP : Nat),
      env.find? recName = some (.recInfo cv mI rP rules)) →
    Expr.WScoped d major → major.looseBVarsBounded 0 = true →
    Expr.LeavesBounded major → CtxOk m φ d Δa major →
    denoteMeta m.acval env φ d major = some vm →
    (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ vm) →
    ∃ w, denoteMeta m.acval env φ d major' = some w ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ w) ∧
      (∀ ρ : Nat → V, Sat V Δa ρ → interp V ρ vm = interp V ρ w) ∧
      Expr.WScoped d major' ∧ major'.looseBVarsBounded 0 = true ∧
      Expr.LeavesBounded major' ∧ CtxOk m φ d Δa major'

/-- **The rescue's fabrication reads — the reads-only walk** (task
#172 B4).  With the certificate runs io-graded, per-argument
readability can no longer be extracted from them (a skipped position
is not traversed); instead the fabrication's parts read because the
major's own io-inferred type does (`InferReadsIO` + `WhnfReads`),
and the projection spines are stored constants applied to those same
parts.  The leaf package of the fabrication is the subject's. -/
theorem majorToCtorFueled_reads {m : EnvModel V env}
    (ihw : WhnfReads m μ φ fuel) (ihio : InferReadsIO m μ φ fuel)
    {d : Nat} {recName : Name} {rules : List ConLeche.RecRule}
    {e e' : Expr} {ea : AnnotTerm}
    (h : ConLeche.majorToCtorFueled μ env fuel d recName rules e = .ok e')
    (hfrec : ∃ (cv : ConstantVal) (mI rP : Nat),
      env.find? recName = some (.recInfo cv mI rP rules))
    (hws : Expr.WScoped d e) (hb : e.looseBVarsBounded 0 = true)
    (hLb : Expr.LeavesBounded e) (hlr : LeafReads m φ d e)
    (hea : denoteMeta m.acval env φ d e = some ea) :
    (∃ w, denoteMeta m.acval env φ d e' = some w) ∧
      LeafReads m φ d e' := by
  rcases ConLeche.majorToCtor_inv h with rfl | ⟨hwsB, hbB, hleafB, rl, cvj,
    cnP, cnF, tmaj₀, tmaj, T, us₀, ust, cvT, caps, hrules, hfcj, hpres,
    hfT, hitm, hwtm, hfnT, hcase⟩
  · exact ⟨⟨ea, hea⟩, hlr⟩
  · -- the major's io-inferred type reads, then its reduct
    have hitmL := inferTypeCoreIO_of_slot hitm
    have hwt0 : Expr.WScoped d tmaj₀ :=
      ConLeche.inferTypeIO_WScoped m.wf fuel hitm hws
    have hbt0 : tmaj₀.looseBVarsBounded 0 = true :=
      ConLeche.inferTypeIO_looseBVars m.wf fuel hitm hws hb hLb
    have hLt0 : Expr.LeavesBounded tmaj₀ := fun l hl =>
      hLb l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hitm hws l hl)
    have hlrt0 : LeafReads m φ d tmaj₀ :=
      hlr.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hitm hws)
    obtain ⟨t0a, ht0a⟩ := ihio hitmL hws hb hLb hlr hea
    obtain ⟨tma, htma⟩ := ihw hwtm hwt0 hbt0 hLt0 hlrt0 ht0a
    have hlrtm : LeafReads m φ d tmaj :=
      hlrt0.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hwtm)
    -- the reduced type's parameter spine reads
    rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
      (ConLeche.Expr.mkAppN_getApp tmaj).symm, hfnT] at htma
    obtain ⟨vT, tsa, hvT, hspt, -⟩ := denoteMeta_mkAppN_inv htma
    have hlrTargs : ∀ x ∈ tmaj.getAppArgs, LeafReads m φ d x :=
      fun x hx => hlrtm.of_subset
        (fun l hl => ConLeche.fvarLeaves_getAppArgs hx l hl)
    obtain ⟨cvR, mIR, rPR, hfrecE⟩ := hfrec
    obtain ⟨-, hEbits⟩ := ConLeche.recCtors_bits m.rec_ctors hfrecE
      (by rw [hrules]; exact List.mem_cons_self) hfcj hpres hfT
    rcases hcase with ⟨hK, hlpj, hcnP, rfl, hcerts,
        ⟨tfab, hitfab, hdefab⟩, hirr⟩ |
      ⟨hetab, hnz, hlenP, hlenU, hlpj, rfl, hcerts,
        hetacase⟩
    · -- K: the parameters-only constructor application
      refine ⟨⟨_, denoteMeta_mkAppN (hspt.take cnP)
        (denoteMeta_const hfcj (show ust.length
          = (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
          from hlpj.symm))⟩, ?_⟩
      intro l hl
      rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · exact absurd hl' (by simp [Expr.fvarLeaves])
      · exact hlrTargs y (List.mem_of_mem_take hy) l hly
    · -- η: parameters plus the stored projection spines
      obtain ⟨heta, hectr⟩ := hEbits hetab
      -- each fabricated argument reads
      have hallF : ∀ x ∈ ConLeche.etaFabArgsE env T ust tmaj.getAppArgs e
          caps.etaFields,
          (∃ xa, denoteMeta m.acval env φ d x = some xa) ∧
            LeafReads m φ d x := by
        intro x hx
        rw [ConLeche.etaFabArgsE] at hx
        rcases List.mem_append.mp hx with hx' | hx'
        · obtain ⟨xa, hxa⟩ := hspt.mem x hx'
          exact ⟨⟨xa, hxa⟩, hlrTargs x hx'⟩
        · -- a fabricated projection, by entry kind (task #175 W4c)
          unfold ConLeche.etaProjs at hx'
          by_cases htow : ConLeche.towerSlotsAll env T caps.etaFields = true
          · -- a `.proj` node at a tower entry reads to the tower reading
            rw [if_pos htow] at hx'
            obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
            obtain ⟨entry, hfe⟩ :=
              ConLeche.towerSlotsAll_slot htow j (List.mem_range.mp hj)
            refine ⟨⟨_, denoteMeta_proj_tower hfe hea⟩, ?_⟩
            intro l hl
            exact hlr l (by simpa [Expr.fvarLeaves] using hl)
          rw [if_neg htow] at hx'
          obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
          -- the projection function is stored (the R13 certificate
          -- pins it); at zero fields the range is empty
          rcases hetacase with hcw | ⟨hnF0, hlpj', hirr⟩
          · obtain ⟨c2, us2, cvc2, cnP2, cnF2, T2, ust2, cvT2, caps2,
              hfna2, hfc2, hlena2, hfnb2, hfT2, -, -, -, hefld2, -, -, -,
              hlenus2, hlpc2, hslots2, -, -, hprojs, -, -, -⟩ :=
              ConLeche.structEtaCertWith_inv hcw
            have hTeq : T2 = T := by
              rw [hfnT] at hfnb2
              exact (ConLeche.Expr.const.inj hfnb2).1.symm
            have hUeq : ust2 = ust := by
              rw [hfnT] at hfnb2
              exact (ConLeche.Expr.const.inj hfnb2).2.symm
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
            -- the per-slot certificates ran: not a tower family (task
            -- #175 S1)
            have htowF : ConLeche.towerSlotsAll env T cnF2 = false := by
              cases h : ConLeche.towerSlotsAll env T cnF2
              · rfl
              · exact absurd (by rw [hefld2]; exact h) htow
            obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp, -, -⟩ :=
              ConLeche.structEtaProjCerts_inv _ (hprojs htowF) j (by
                rw [List.mem_range] at hj ⊢; rw [← hefld2]; exact hj)
            have hspM : DenoteMetaSpine m.acval env φ d
                (tmaj.getAppArgs ++ [e]) (tsa ++ [ea]) :=
              hspt.append (DenoteMetaSpine.cons hea DenoteMetaSpine.nil)
            refine ⟨⟨_, denoteMeta_mkAppN hspM
              (denoteMeta_const hfp (show ust.length
                = (ConstantInfo.recInfo cvp mIp rPp
                    rulesp).toConstantVal.levelParams.length from by
                show ust.length = cvp.levelParams.length
                rw [hlpp]; exact hlenus2))⟩, ?_⟩
            intro l hl
            rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
            · exact absurd hl' (by simp [Expr.fvarLeaves])
            · rcases List.mem_append.mp hy with hy' | hy'
              · exact hlrTargs y hy' l hly
              · rcases List.mem_singleton.mp hy' with rfl
                exact hlr l hly
          · rw [List.mem_range, hnF0] at hj
            exact absurd hj (Nat.not_lt_zero j)
      -- assemble the spine
      have hspF : ∃ ys, DenoteMetaSpine m.acval env φ d
          (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs e caps.etaFields)
          ys := by
        have hall := fun x hx => (hallF x hx).1
        revert hall
        generalize ConLeche.etaFabArgsE env T ust tmaj.getAppArgs e
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
      refine ⟨⟨_, denoteMeta_mkAppN hspF
        (denoteMeta_const (hectr ▸ hfcj) (show ust.length
          = (ConstantInfo.ctorInfo cvj cnP cnF).toConstantVal.levelParams.length
          from hlpj.symm))⟩, ?_⟩
      intro l hl
      rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
      · exact absurd hl' (by simp [Expr.fvarLeaves])
      · exact (hallF y hy).2 l hly

/-- **`MajorStep`, proved** (R12/R13/R14 and the identity
fallthrough). -/
theorem majorToCtorFueled_step {m : EnvModel V env}
    (hcaps : CapsOk m) (htower : TowerOk m φ) (hct : ConstType m φ) (hav : AcvalValid m)
    (ihw : WhnfClaim μ m φ fuel) (ihd : DefEqClaim μ m φ fuel)
    (ihis : InferClaimIOS μ m φ fuel)
    (hsss : SortSemAtIOS m μ φ fuel)
    (hexi : InferExistsIOS μ m φ fuel)
    (hreads_ios : InferReadsIOS m μ φ fuel)
    (hwreads : WhnfReads m μ φ fuel) :
    MajorStep μ m φ fuel := by
  intro d Δa recName rules major major' vm h hfrec hws hb hLb hC hvm hokm
  have hpi : ProofIrrelPQ μ m φ fuel :=
    proofIrrelPQ_of_claims ihis hsss hreads_ios
      (unitIrrelPQ_of_claims ihw ihis hreads_ios hwreads)
  rcases ConLeche.majorToCtor_inv h with rfl | ⟨hwsB, hbB, hleafB, rl, cvj,
    cnP, cnF, tmaj₀, tmaj, T, us₀, ust, cvT, caps, hrules, hfcj, hpres,
    hfT, hitm, hwtm, hfnT, hcase⟩
  · exact ⟨vm, hvm, hokm, fun _ _ => rfl, hws, hb, hLb, hC⟩
  · -- the fabrication's frame conditions come with the inversion
    have hwF : Expr.WScoped d major' := Expr.WScoped.of_wscopedB hwsB
    have hLF : Expr.LeavesBounded major' := fun l hl =>
      hLb l (by
        have := List.all_eq_true.mp hleafB l hl
        simpa using this)
    have hCF : CtxOk m φ d Δa major' :=
      hC.of_subset (fun l hl => by
        have := List.all_eq_true.mp hleafB l hl
        simpa using this)
    -- the major's type: inferred, read, graded, inhabited; then reduced
    have hwt0 : Expr.WScoped d tmaj₀ :=
      ConLeche.inferTypeIO_WScoped m.wf fuel hitm hws
    have hbt0 : tmaj₀.looseBVarsBounded 0 = true :=
      ConLeche.inferTypeIO_looseBVars m.wf fuel hitm hws hb hLb
    have hLt0 : Expr.LeavesBounded tmaj₀ := fun l hl =>
      hLb l (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hitm hws l hl)
    have hCt0 : CtxOk m φ d Δa tmaj₀ :=
      hC.of_subset (ConLeche.inferTypeIO_fvarLeaves m.wf fuel hitm hws)
    obtain ⟨tmaj₀a, htmaj₀a⟩ :=
      hexi hitm hws hb hLb hC hvm
    obtain ⟨hokT0, hmemM⟩ := ihis hitm hws hb hLb hC hvm htmaj₀a hokm
    obtain ⟨tmaja, htmaja⟩ := hwreads hwtm hwt0 hbt0 hLt0
      (LeafReads.of_ctxOk hCt0) htmaj₀a
    obtain ⟨hokTm, heqTm⟩ :=
      ihw hwtm hwt0 hbt0 hLt0 hCt0 htmaj₀a htmaja hokT0
    have hwr : Expr.WScoped d tmaj :=
      ConLeche.whnf_WScoped m.wf fuel hwtm hwt0
    have hbr : tmaj.looseBVarsBounded 0 = true :=
      ConLeche.whnf_looseBVars m.wf fuel hwtm hbt0
    have hLr : Expr.LeavesBounded tmaj := fun l hl =>
      hLt0 l (ConLeche.whnf_fvarLeaves m.wf fuel hwtm l hl)
    have hCr : CtxOk m φ d Δa tmaj :=
      hCt0.of_subset (ConLeche.whnf_fvarLeaves m.wf fuel hwtm)
    have hmemMW : ∀ ρ : Nat → V, Sat V Δa ρ →
        interp V ρ vm ∈ˢ interp V ρ tmaja :=
      fun ρ hρ => (heqTm ρ hρ) ▸ hmemM ρ hρ
    -- the reduced type is the family applied to its parameters
    have hsave := htmaja
    rw [show tmaj = Expr.mkAppN tmaj.getAppFn tmaj.getAppArgs from
      (ConLeche.Expr.mkAppN_getApp tmaj).symm, hfnT] at htmaja
    obtain ⟨vT, tsa, hvT, hspt, rfl⟩ := denoteMeta_mkAppN_inv htmaja
    obtain ⟨-, hoTs⟩ := hoist_spine tsa hokTm
    -- the constructor's stored type, read and graded
    have hlenCj : ust.length = cvj.levelParams.length := by
      rcases hcase with ⟨-, hlpj, -⟩ | ⟨-, -, -, -, hlpj, -⟩
      · exact hlpj.symm
      · exact hlpj.symm
    obtain ⟨TVja, hTVja, hokTVja, hmemCj⟩ :=
      hct d rl.ctor _ ust hfcj rfl (by exact hlenCj)
    dsimp only [ConLeche.ConstantInfo.toConstantVal] at hTVja hmemCj
    have hwfj := m.wf _ (ConLeche.Semantics.Env.find?_mem hfcj)
    have hnfj : (cvj.type.instantiateLevelParams cvj.levelParams
        ust).hasFvar = false := by
      rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfj.1
    have hbdj : (cvj.type.instantiateLevelParams cvj.levelParams
        ust).looseBVarsBounded 0 = true := by
      rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
      exact hwfj.2.2.2.1
    have hCj : CtxOk m φ d Δa
        (cvj.type.instantiateLevelParams cvj.levelParams ust) :=
      ⟨hC.1, fun l hl => by
        rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfj] at hl
        exact nomatch hl⟩
    have hheadCj : denoteMeta m.acval env φ d (.const rl.ctor ust)
        = some (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust)) :=
      denoteMeta_const hfcj (by exact hlenCj)
    -- the fabricated spine's reading and grading, uniformly: the
    -- fabrication's own `iotaCerts` run certifies exactly its arguments,
    -- and `certs_telePA` returns their gradings with the fit
    have hfab : ∀ (fargs : List Expr) (fargsa : List AnnotTerm),
        ConLeche.iotaCertsFueled μ env fuel d false
            (cvj.type.instantiateLevelParams cvj.levelParams ust)
            fargs = .ok true →
        (∀ x ∈ fargs, Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
          Expr.LeavesBounded x ∧ CtxOk m φ d Δa x) →
        DenoteMetaSpine m.acval env φ d fargs fargsa →
        (∀ x ∈ fargsa, ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x) →
        denoteMeta m.acval env φ d (Expr.mkAppN (.const rl.ctor ust) fargs)
            = some (AnnotTerm.mkAppN
              (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
              fargsa) ∧
          ∀ ρ : Nat → V, Sat V Δa ρ →
            WellDenotedV V ρ (AnnotTerm.mkAppN
              (m.acval rl.ctor (Level.substFn φ cvj.levelParams ust))
              fargsa) := by
      intro fargs fargsa hcerts hframes hsp hoks
      refine ⟨denoteMeta_mkAppN hsp hheadCj, fun ρ hρ => ?_⟩
      obtain ⟨resta, hfit, -, hokArgs⟩ :=
        certs_telePA ihd ihis hexi _ fargs fargsa TVja hcerts
          (ConLeche.Expr.WScoped.of_not_hasFvar hnfj) hbdj
          (ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfj) hCj hTVja
          (fun σ _ => hokTVja σ) hframes hsp hoks
      exact (wellDenotedV_mkAppN_of_fitA fargsa (hokTVja ρ)
        ⟨m.acval_wellDenoted _ _ ρ, hav _ _ ρ⟩
        (fun x hx => hokArgs x hx ρ hρ) (hmemCj ρ) (hfit ρ hρ)).1
    obtain ⟨cvR, mIR, rPR, hfrecE⟩ := hfrec
    obtain ⟨-, hEbits⟩ := ConLeche.recCtors_bits m.rec_ctors hfrecE
      (by rw [hrules]; exact List.mem_cons_self) hfcj hpres hfT
    rcases hcase with ⟨hK, hlpj, hcnP, rfl, hcerts,
        ⟨tfab, hitfab, hdefab⟩, hirr⟩ |
      ⟨hetab, hnz, hlenP, hlenU, hlpj, rfl, hcerts,
        hetacase⟩
    · -- R12: the K-flagged rescue
      obtain ⟨hdF, hokF⟩ := hfab (tmaj.getAppArgs.take cnP) (tsa.take cnP)
        hcerts
        (fun x hx => frame_spine hwr hbr hLr hCr x (List.mem_of_mem_take hx))
        (hspt.take cnP)
        (fun x hx => hoTs x (List.mem_of_mem_take hx))
      exact ⟨_, hdF, hokF,
        fun ρ hρ => (hpi hirr hwF hbB hLF hws hb hLb hCF hC hdF hvm
          hokF hokm ρ hρ).symm,
        hwF, hbB, hLF, hCF⟩
    · -- R13/R14: the η-capable rescue
      obtain ⟨heta, hectr⟩ := hEbits hetab
      have hspM : DenoteMetaSpine m.acval env φ d (tmaj.getAppArgs ++ [major])
          (tsa ++ [vm]) :=
        hspt.append (DenoteMetaSpine.cons hvm DenoteMetaSpine.nil)
      have hfrM : ∀ x ∈ tmaj.getAppArgs ++ [major],
          Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
            Expr.LeavesBounded x ∧ CtxOk m φ d Δa x := by
        intro x hx
        rcases List.mem_append.mp hx with hx' | hx'
        · exact frame_spine hwr hbr hLr hCr x hx'
        · rcases List.mem_singleton.mp hx' with rfl
          exact ⟨hws, hb, hLb, hC⟩
      rcases hetacase with hcw | ⟨hnF0, hlpj', hirr⟩
      · -- R13: the η certificate identifies the fabrication with the major
        obtain ⟨c2, us2, cvc2, cnP2, cnF2, T2, ust2, cvT2, caps2, hfna2,
          hfc2, hlena2, hfnb2, hfT2, -, -, -, hefld2, -, -, -, hlenus2,
          hlpc2, hslots2, -, -, hprojs, -, -, -⟩ := ConLeche.structEtaCertWith_inv hcw
        have hTeq : T2 = T := by
          rw [hfnT] at hfnb2; exact (ConLeche.Expr.const.inj hfnb2).1.symm
        have hUeq : ust2 = ust := by
          rw [hfnT] at hfnb2; exact (ConLeche.Expr.const.inj hfnb2).2.symm
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
        have hokMs : ∀ x ∈ tsa ++ [vm], ∀ ρ : Nat → V, Sat V Δa ρ →
            WellDenotedV V ρ x := by
          intro x hx
          rcases List.mem_append.mp hx with hx' | hx'
          · exact hoTs x hx'
          · rcases List.mem_singleton.mp hx' with rfl; exact hokm
        by_cases htow : ConLeche.towerSlotsAll env T caps.etaFields = true
        · -- TOWER-BACKED SLOTS (task #175 W4c): the fabricated
          -- projections are `.proj T j major` nodes reading to the tower
          -- readings, graded by each entry's typing law
          have hvT' : vT = m.acval T (Level.substFn φ cvT.levelParams ust) := by
            rw [denoteMeta_const hfT (show ust.length
              = (ConstantInfo.indInfo cvT caps).toConstantVal.levelParams.length
              from hlenus2)] at hvT
            exact (Option.some.inj hvT).symm
          -- (task #175 S1: the slots are the table's, whose head data
          -- carries the former's level parameters)
          have hslotE : ∀ j, j < caps.etaFields → ∃ entry : ProjEntry,
              env.findProj? T j = some entry ∧
              entry.levelParams = cvT.levelParams := by
            intro j hj
            obtain ⟨entry, hfe⟩ := ConLeche.towerSlotsAll_slot htow j hj
            obtain ⟨-, -, -, ⟨cvT', capsT', hfT', hlpsT', -⟩, -⟩ :=
              htower T j entry hfe
            have hcvT' : cvT' = cvT := by
              rw [hfT] at hfT'
              exact (ConstantInfo.indInfo.inj (Option.some.inj hfT')).1.symm
            exact ⟨entry, hfe, by rw [← hlpsT', hcvT']⟩
          have hpfacts : ∀ j ∈ List.range caps.etaFields,
              denoteMeta m.acval env φ d (.proj T j major)
                = some (projAV (j + env.projOff T) vm) := by
            intro j hj
            obtain ⟨entry, hfe, -⟩ := hslotE j (List.mem_range.mp hj)
            rw [← ConLeche.Env.findProj?_off hfe]
            exact denoteMeta_proj_tower hfe hvm
          have hokProj : ∀ j ∈ List.range caps.etaFields, ∀ ρ : Nat → V,
              Sat V Δa ρ → WellDenotedV V ρ (projAV (j + env.projOff T) vm) := by
            intro j hj ρ hρ
            obtain ⟨entry, hfe, hlpe⟩ :=
              hslotE j (List.mem_range.mp hj)
            rw [← ConLeche.Env.findProj?_off hfe]
            obtain ⟨-, -, -, ⟨cvTj, capsTj, hfTj, -, himpj⟩, hO5j,
              _, -, -, hlawj, -⟩ := htower T j entry hfe
            have hcapsTj : capsTj = caps := by
              rw [hfT] at hfTj
              exact (ConstantInfo.indInfo.inj (Option.some.inj hfTj)).2.symm
            obtain ⟨hnpj, -, hparj, -⟩ := himpj (by rw [hcapsTj]; exact heta)
            rw [hcapsTj] at hparj
            have hgj : TowerGuardAt φ entry ust :=
              towerGuardAt_of hO5j
                (fun hp => by rw [hp] at hnpj; exact nomatch hnpj)
            obtain ⟨⟨Ta, hTa, hA⟩, -⟩ := hlawj ust (by rw [hlpe]; exact hlenus2)
            obtain ⟨hTad, -⟩ := towerEntry_tele_at_depth hfe hTa
            have hlenVs : tsa.length = entry.numParams := by
              rw [← hspt.length, hlenP, hparj]
            -- the body telescope's reading is a ∀-chain of the subject
            -- list's length, so it peels along it
            have hpc : PiChain (tsa ++ [vm]).length Ta := by
              rw [List.length_append, List.length_singleton, hlenVs]
              exact piChain_of_stripPis _
                (by rw [ConLeche.projTele_stripPis]; rfl) (hTad d)
            obtain ⟨restj, hpeel⟩ := peelPis_of_piChain _ hpc
            rw [hlpe, ← hvT'] at hA
            exact (hA hgj ρ tsa vm restj hlenVs (hokTm ρ hρ) (hokm ρ hρ)
              (hmemMW ρ hρ) hpeel).1
          have hspF : DenoteMetaSpine m.acval env φ d
              (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)
              (tsa ++ (List.range caps.etaFields).map fun j =>
                projAV (j + env.projOff T) vm) := by
            rw [ConLeche.etaFabArgsE, ConLeche.etaProjs, if_pos htow]
            exact hspt.append (DenoteMetaSpine.map_list _ hpfacts)
          have hfrF : ∀ x ∈ ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major
              caps.etaFields,
              Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
                Expr.LeavesBounded x ∧ CtxOk m φ d Δa x := by
            intro x hx
            rw [ConLeche.etaFabArgsE, ConLeche.etaProjs, if_pos htow] at hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact frame_spine hwr hbr hLr hCr x hx'
            · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
              exact ⟨by simpa [Expr.WScoped] using hws,
                by simpa [Expr.looseBVarsBounded] using hb,
                fun l hl => hLb l (by simpa [Expr.fvarLeaves] using hl),
                ⟨hC.1, fun l hl => hC.2 l (by simpa [Expr.fvarLeaves] using hl)⟩⟩
          have hoksF : ∀ x ∈ (tsa ++ (List.range caps.etaFields).map fun j =>
              projAV (j + env.projOff T) vm),
              ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x := by
            intro x hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact hoTs x hx'
            · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
              exact hokProj j hj
          obtain ⟨hdF0, hokF0⟩ := hfab _ _ hcerts hfrF hspF hoksF
          rw [hectr] at hdF0 hokF0
          refine ⟨_, hdF0, hokF0, fun ρ hρ => ?_, hwF, hbB, hLF, hCF⟩
          exact (structEtaCertWithFueled_step hcaps htower hct hav ihd ihis hexi hcw
            hwF hbB hLF hCF hws hb hLb hC hwr hbr hLr hCr hdF0 hvm hsave
            hokF0 hokm hokTm hmemMW ρ hρ).symm
        · -- PROJECTION-FUNCTION SLOTS: the projection spines read (the
          -- certificate stores each projection function at the family's
          -- level arity)
          have hrec : ConLeche.recSlotsAll env T caps.etaFields = true := by
            simpa [htow] using hslots2
          have hslotR : ∀ j ∈ List.range caps.etaFields, ∃ cvp mIp rPp rulesp,
              env.find? (projFnName T j) = some (.recInfo cvp mIp rPp rulesp) ∧
              cvp.levelParams = cvT.levelParams ∧
              (cvp.type.stripPis (tmaj.getAppArgs.length + 1)).isSome = true ∧
              ConLeche.iotaCertsFueled μ env fuel d false
                (cvp.type.instantiateLevelParams cvp.levelParams ust)
                (tmaj.getAppArgs ++ [major]) = .ok true := by
            intro j hj
            have htowF : ConLeche.towerSlotsAll env T cnF2 = false := by
              cases h : ConLeche.towerSlotsAll env T cnF2
              · rfl
              · exact absurd (by rw [hefld2]; exact h) htow
            exact ConLeche.structEtaProjCerts_inv _ (hprojs htowF) j (by
              rw [List.mem_range] at hj ⊢; rw [← hefld2]; exact hj)
          have hpfacts : ∀ j ∈ List.range caps.etaFields,
              denoteMeta m.acval env φ d
                  (Expr.mkAppN (.const (projFnName T j) ust)
                    (tmaj.getAppArgs ++ [major]))
                = some (AnnotTerm.mkAppN
                    (m.acval (projFnName T j)
                      (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])) := by
            intro j hj
            obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp, -, -⟩ := hslotR j hj
            refine denoteMeta_mkAppN hspM ?_
            rw [denoteMeta_const (acval := m.acval) (φ := φ) (d := d) hfp
              (show ust.length = (ConstantInfo.recInfo cvp mIp rPp
                rulesp).toConstantVal.levelParams.length from by
                show ust.length = cvp.levelParams.length
                rw [hlpp]; exact hlenus2)]
            show some (m.acval (projFnName T j)
              (Level.substFn φ cvp.levelParams ust)) = _
            rw [hlpp]
          have hokProj : ∀ j ∈ List.range caps.etaFields, ∀ ρ : Nat → V,
              Sat V Δa ρ → WellDenotedV V ρ (AnnotTerm.mkAppN
                (m.acval (projFnName T j)
                  (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])) := by
            intro j hj ρ hρ
            obtain ⟨cvp, mIp, rPp, rulesp, hfp, hlpp, hstrp, hicj⟩ := hslotR j hj
            have hlenp : ust.length = cvp.levelParams.length := by
              rw [hlpp]; exact hlenus2
            obtain ⟨tpa, htpa, hoktpa, hmemp⟩ :=
              hct d (projFnName T j) _ ust hfp rfl hlenp
            have hwfp := m.wf _ (ConLeche.Semantics.Env.find?_mem hfp)
            have hnfp : (cvp.type.instantiateLevelParams cvp.levelParams
                ust).hasFvar = false := by
              rw [ConLeche.Expr.hasFvar_instantiateLevelParams]; exact hwfp.1
            have hbdp : (cvp.type.instantiateLevelParams cvp.levelParams
                ust).looseBVarsBounded 0 = true := by
              rw [ConLeche.Expr.looseBVarsBounded_instantiateLevelParams]
              exact hwfp.2.2.2.1
            obtain ⟨restp, hfitp, -, -⟩ :=
              certs_telePA ihd ihis hexi _ (tmaj.getAppArgs ++ [major])
                (tsa ++ [vm]) tpa hicj
                (ConLeche.Expr.WScoped.of_not_hasFvar hnfp) hbdp
                (ConLeche.Expr.LeavesBounded.of_not_hasFvar hnfp)
                ⟨hC.1, fun l hl => by
                  rw [ConLeche.Expr.fvarLeaves_eq_nil_of_not_hasFvar hnfp]
                    at hl
                  exact nomatch hl⟩
                htpa (fun τ _ => hoktpa τ) hfrM hspM hokMs
            refine (wellDenotedV_mkAppN_of_fitA (tsa ++ [vm]) (hoktpa ρ)
              ⟨m.acval_wellDenoted _ _ ρ, hav _ _ ρ⟩
              (fun x hx => hokMs x hx ρ hρ) ?_ (hfitp ρ hρ)).1
            have := hmemp ρ
            dsimp only [ConLeche.ConstantInfo.toConstantVal] at this
            rwa [hlpp] at this
          have hspF : DenoteMetaSpine m.acval env φ d
              (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields)
              (tsa ++ (List.range caps.etaFields).map fun j =>
                AnnotTerm.mkAppN (m.acval (projFnName T j)
                  (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])) := by
            rw [ConLeche.etaFabArgsE, ConLeche.etaProjs, if_neg htow]
            exact hspt.append (DenoteMetaSpine.map_list _ hpfacts)
          have hfrF : ∀ x ∈ ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major
              caps.etaFields,
              Expr.WScoped d x ∧ x.looseBVarsBounded 0 = true ∧
                Expr.LeavesBounded x ∧ CtxOk m φ d Δa x := by
            intro x hx
            rw [ConLeche.etaFabArgsE, ConLeche.etaProjs, if_neg htow] at hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact frame_spine hwr hbr hLr hCr x hx'
            · obtain ⟨j, -, rfl⟩ := List.mem_map.mp hx'
              refine ⟨ConLeche.Expr.WScoped.mkAppN
                  (ConLeche.Expr.WScoped.of_not_hasFvar rfl)
                  (fun y hy => (hfrM y hy).1),
                ConLeche.looseBVarsBounded_mkAppN rfl
                  (fun y hy => (hfrM y hy).2.1),
                fun l hl => ?_, ⟨hC.1, fun l hl => ?_⟩⟩ <;>
              · rcases ConLeche.fvarLeaves_mkAppN hl with hl' | ⟨y, hy, hly⟩
                · exact absurd hl' (by simp [Expr.fvarLeaves])
                · first
                  | exact (hfrM y hy).2.2.1 l hly
                  | exact (hfrM y hy).2.2.2.2 l hly
          have hoksF : ∀ x ∈ (tsa ++ (List.range caps.etaFields).map fun j =>
              AnnotTerm.mkAppN (m.acval (projFnName T j)
                (Level.substFn φ cvT.levelParams ust)) (tsa ++ [vm])),
              ∀ ρ : Nat → V, Sat V Δa ρ → WellDenotedV V ρ x := by
            intro x hx
            rcases List.mem_append.mp hx with hx' | hx'
            · exact hoTs x hx'
            · obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hx'
              exact hokProj j hj
          obtain ⟨hdF0, hokF0⟩ := hfab _ _ hcerts hfrF hspF hoksF
          rw [hectr] at hdF0 hokF0
          refine ⟨_, hdF0, hokF0, fun ρ hρ => ?_, hwF, hbB, hLF, hCF⟩
          exact (structEtaCertWithFueled_step hcaps htower hct hav ihd ihis hexi hcw
            hwF hbB hLF hCF hws hb hLb hC hwr hbr hLr hCr hdF0 hvm hsave
            hokF0 hokm hokTm hmemMW ρ hρ).symm
      · -- R14: the zero-field fallthrough
        have hEmpty : ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major
            caps.etaFields = tmaj.getAppArgs := by
          rw [ConLeche.etaFabArgsE, ConLeche.etaProjs, hnF0]
          simp
        obtain ⟨hdF0, hokF0⟩ := hfab tmaj.getAppArgs tsa
          (by rw [← hEmpty]; exact hcerts)
          (frame_spine hwr hbr hLr hCr) hspt hoTs
        have hdF : denoteMeta m.acval env φ d
            (Expr.mkAppN (.const caps.etaCtor ust)
              (ConLeche.etaFabArgsE env T ust tmaj.getAppArgs major caps.etaFields))
            = some (AnnotTerm.mkAppN (m.acval caps.etaCtor
                (Level.substFn φ cvj.levelParams ust)) tsa) := by
          rw [hEmpty, ← hectr]; exact hdF0
        have hokF : ∀ ρ : Nat → V, Sat V Δa ρ →
            WellDenotedV V ρ (AnnotTerm.mkAppN (m.acval caps.etaCtor
              (Level.substFn φ cvj.levelParams ust)) tsa) := by
          rw [← hectr]; exact hokF0
        exact ⟨_, hdF, hokF,
          fun ρ hρ => (hpi hirr hwF hbB hLF hws hb hLb hCF hC hdF hvm
            hokF hokm ρ hρ).symm,
          hwF, hbB, hLF, hCF⟩

end ConLeche.Model
