module

import ConLeche.Model.Steps.Reads
public import ConLeche.Model.Steps.ReadsIO
import ConLeche.Model.Steps.CapsRows
import ConLeche.Model.Steps.StrLit
public import ConLeche.Model.Steps.ProjRows
import ConLeche.Model.Steps.IotaRows
import ConLeche.Model.Steps.IrrelFast
public section

/-!
# The tiers assembly (task #161, P4): one env-fixed bundle, one induction

`checkSoundP_of_inputs` (`AssemblyP.lean`) closes the induction over
the three quarters' ∀-environment input structures.  The declaration
fold cannot inhabit those: it holds an `EnvModelM` for **one**
environment at a time.  This file is the env-fixed re-assembly:

* `TierInputsAt` — every residue the P ladder still routes, at one
  `(env, m, φ)`, sorted by discharge tier (install / iota / literal /
  caps).  The env-tier entries are `EnvModelM` consequences
  (`TierInputsAt.ofEnvModelM`); the rest are the semantic-content bill
  the frontier-transformation table records.
* `checkSoundAt` — the four claims at every fuel, at the fixed
  environment, with the of_claims discharges (batches 6/7) **wired
  in**: proof irrelevance, the spine congruences, η, `stuckIrrel`'s
  cascade, the string expansion, the delta identity, the totality
  factors, and the derived sort fact are all supplied from the
  induction hypotheses at each step — none of them appears in the
  bundle.

The quarter-level ∀-env assemblies (`AssemblyP.lean`) remain the
frozen quarter statements; this file is what the fold consumes.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics (AnnotTerm)
open ConLeche (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- **The routed residues, at one environment** (see the module
docstring).  Field order groups the tiers: the `reads` bundle carries
the install/iota/proj/literal *readability* leaves inside it. -/
structure TierInputsAt (V : Type w) [SetTheory V] (μ : CheckMode)
    {env : Env} (m : EnvModel V env) (φ : Name → Nat) : Prop where
  /-- install tier: the readability bundle (its own four leaves are
  iota/proj/literal reads) -/
  reads : ReadsInputs μ m φ
  /-- install tier: leaf bit-validity -/
  acval_valid : AcvalValid m
  /-- install tier: the numeral heads -/
  nat_heads : NatHeads m φ
  /-- iota tier: the stored recursors' fired contracts — an `EnvModelM`
  field (`rec_rules`), which with the claims discharges both ι rows
  (`iotaStep_of`, `iotaReads_of`) -/
  rec_rules : RecRules m φ
  /-- literal tier: the two acceleration rows, each taking the whnf
  claims at the same fuel (`reduceNat` head-normalises its arguments
  before reading them as literals) -/
  nat_step : ∀ fuel, WhnfClaim μ m φ fuel → ReduceNatStep μ m φ fuel
  nat_stepQ : ∀ fuel,
    WhnfClaim μ m φ fuel → ReduceNatStepPQ μ m φ fuel
  /-- caps tier: the stored families' fired capability laws — an
  `EnvModelM` field (`caps_ok`), which is what discharges the stored
  structure's η and unit fallbacks (`structEtaIrrel_of_claims`,
  `structUnitIrrel_of_claims` — the latter after the ratified
  one-premise repair of the unit half; all four capability rows are
  now discharged) -/
  caps_ok : CapsOk m

/-- **The P soundness ladder at one environment — the five-way joint
induction** (task #172 B4), with every of_claims discharge wired in.
The io claim joined the induction the moment the first converted call
site (the β certificate) made the head-normalisation quarter consume
the slot claim at the same fuel; the four-way form survives as the
projection `checkSoundAt` below, so every landed consumer stands
verbatim. -/
theorem checkSoundAtP5 (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (h : TierInputsAt V μ m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel ∧
          InferClaimIO μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d e e' Δa hrun
      rw [ConLeche.whnfCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e e' Δa hrun
      rw [ConLeche.whnf_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d a b Δa hrun
      rw [ConLeche.isDefEqCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e t Δa hrun
      rw [ConLeche.inferTypeCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e t Δa hrun
      rw [ConLeche.inferTypeCoreIO_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi, ihio⟩ := ih
    -- the totality factors, from the reads bundle
    have hreads : InferReads m μ φ fuel := inferReads_of h.reads
    have hwreads : WhnfReads m μ φ fuel := whnfReads_of h.reads
    have hex : WhnfCoreExists μ m φ fuel := whnfCoreExists_of h.reads
    have hexi : InferExists μ m φ fuel := inferExists_of h.reads
    have hreads_io : InferReadsIO m μ φ fuel :=
      inferReadsIO_of h.reads fuel
    -- the slot facts (task #172 B4): existence and the premise-form
    -- claim at the knot's io slot, from the two lanes
    have hexis : InferExistsIOS μ m φ fuel := by
      intro d e t Δa hrun hws hb hLb ea hC hea
      cases hg : μ.betaGate with
      | false =>
        rw [ConLeche.inferTypeIO_off hg] at hrun
        exact hexi hrun hws hb hLb hC hea
      | true =>
        rw [ConLeche.inferTypeIO_on hg] at hrun
        exact hreads_io hrun hws hb hLb (LeafReads.of_ctxOk hC) hea
    have ihis : InferClaimIOS μ m φ fuel :=
      inferClaimIOS_of ihi ihio
    -- the derived sort facts
    have hss : SortSemAt m μ φ fuel :=
      sortSemAt_of_claims ihw ihi hreads
    have hssio : SortSemAtIO m μ φ fuel :=
      sortSemAtIO_of_claims ihw ihio hreads_io
    have hsss : SortSemAtIOS m μ φ fuel :=
      sortSemAtIOS_of hss hssio
    have hreads_ios : InferReadsIOS m μ φ fuel :=
      inferReadsIOS_of hreads hreads_io
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- the head-normalisation quarter
      exact whnfCore_claims m hex
        (betaCert_of_claims m hexis ihd ihis)
        (iotaStep_of h.rec_rules h.caps_ok h.reads.tower_ok h.reads.const_ty
          h.acval_valid ihw ihd ihis hsss hexis hreads_ios hwreads)
        (projStep_of_claims hμ h.reads.tower_ok h.reads.const_ty ihwc ihw ihd ihis
          hexis hwreads) ihwc
    · -- the reduction loop
      exact whnf_claims m hex ihwc (h.nat_step fuel ihw)
        (delta_of m h.reads.defn)
    · -- the defeq quarter, of_claims discharges wired
      have hsi : StuckIrrelPQ μ m φ fuel :=
        stuckIrrelFueled_of_claims ihis hsss hreads_ios
          (unitIrrelPQ_of_claims ihw ihis hreads_ios hwreads)
          (structEtaIrrel_of_claims h.caps_ok h.reads.tower_ok h.reads.const_ty
            h.acval_valid ihw ihd ihis hexis hwreads)
          (structUnitIrrel_of_claims h.caps_ok ihw ihd ihis hexis
            hwreads)
      have hstep : DefEqStepAt μ m φ fuel :=
        defeqStep_claim (whnfCoreReductExists_of' h.reads) ihwc ihw
          (denoteMetaDelta_of h.reads) (h.nat_stepQ fuel ihw)
          (propIrrelPQ_of_claims h.reads.const_ty ihis hsss hreads_ios)
          (defeqStuck_claim hμ ihd hsi denotePStrLit_of_guard
            (acvalParams m) (appCongrStuck_of_claims ihd)
            (etaCertStep_of_claims hμ ihw ihd ihis hreads_ios hwreads))
          (defEqSpine_of_claims ihd (acvalParams m))
      -- (`defeq_claims hstep` trips an implicit-eta unification
      -- wrinkle at the `DefEqStepAt` unfolding; its two-line body is
      -- inlined instead)
      intro d a b Δa hrun hwa hba' hLa hwb hbb hLb aa ba hCa hCb
        hda hdb
      rw [ConLeche.isDefEqCore_succ, defeqBody] at hrun
      exact defeqLoop_cont hstep defeqLoopFuel d true hrun hwa hba' hLa
        hwb hbb hLb hCa hCb hda hdb
    · -- the infer quarter (the eleven-arm dispatcher, env-fixed)
      intro d e t Δa hrun hws hb hLb ea ta hC hea hta
      match e, hrun, hws, hb, hLb, hC, hea with
      | .sort u, hrun, _, _, _, _, hea =>
        exact infer_sort_claim m hrun hea hta
      | .bvar i, hrun, _, _, _, _, hea =>
        exact infer_bvar_claim m hrun hea hta
      | .fvar idx ty, hrun, _, _, _, hC, hea =>
        exact infer_fvar_claim m hC hrun hea hta
      | .const nm us, hrun, _, _, _, _, hea =>
        exact infer_const_claim m h.reads.const_ty h.acval_valid
          hrun hea hta
      | .lit (.natVal k), hrun, _, _, _, _, hea =>
        exact infer_natLit_claim m h.nat_heads h.acval_valid
          hrun hea hta
      | .lit (.strVal s), hrun, _, _, _, _, hea =>
        exact inferStrLitStep_of_claims h.reads.const_ty h.acval_valid
          h.nat_heads hrun hea hta
      | .forallE ty body mb, hrun, hws, hb, hLb, hC, hea =>
        exact infer_forallE_claim m hμ hss hrun hws hb hLb hC hea hta
      | .lam ty body mb, hrun, hws, hb, hLb, hC, hea =>
        exact infer_lam_claim m hμ hss hsss ihi hrun hws hb hLb hC hea
          hta
      | .app fe ae, hrun, hws, hb, hLb, hC, hea =>
        exact infer_app_claim m hreads hwreads ihw ihd ihi hrun
          hws hb hLb hC hea hta
      | .letE ty val bd, hrun, hws, hb, hLb, hC, hea =>
        exact (ConLeche.inferTypeCore_letE_inv hrun).elim
      | .proj sn i pe, hrun, hws, hb, hLb, hC, hea =>
        exact inferProjStep_of_claims h.reads.tower_ok ihw ihi hreads
          hwreads hrun hws hb
          hLb hC hea hta
    · -- the io quarter (the eleven-arm dispatcher, env-fixed;
      -- task #172 B4)
      intro d e t Δa hrun hws hb hLb ea ta hC hea hta hok
      match e, hrun, hws, hb, hLb, hC, hea, hok with
      | .sort u, hrun, _, _, _, _, hea, _ =>
        exact infer_sort_claimIO m hrun hea hta
      | .bvar i, hrun, _, _, _, _, hea, _ =>
        exact infer_bvar_claimIO m hrun hea hta
      | .fvar idx ty, hrun, _, _, _, hC, hea, _ =>
        exact infer_fvar_claimIO m hC hrun hea hta
      | .const nm us, hrun, _, _, _, _, hea, _ =>
        exact infer_const_claimIO m (h.reads.const_ty) hrun hea hta
      | .lit (.natVal k), hrun, _, _, _, _, hea, _ =>
        exact infer_natLit_claimIO m h.nat_heads h.acval_valid hrun
          hea hta
      | .lit (.strVal str), hrun, _, _, _, _, hea, _ =>
        exact infer_strLit_claimIO m
          (inferStrLitStep_of_claims h.reads.const_ty h.acval_valid
            h.nat_heads) hrun hea hta
      | .forallE ty body mb, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_forallE_claimIO m hμ hssio hrun hws hb hLb hC hea
          hta hok
      | .lam ty body mb, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_lam_claimIO m hμ hssio ihio hrun hws hb hLb hC hea
          hta hok
      | .app fe ae, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_app_claimIO m hreads_io hwreads ihw ihd ihio hrun
          hws hb hLb hC hea hta hok
      | .letE ty val bd, hrun, hws, hb, hLb, hC, hea, hok =>
        exact (ConLeche.inferTypeCoreIO_letE_inv hrun).elim
      | .proj sn i pe, hrun, hws, hb, hLb, hC, hea, hok =>
        exact inferProjStepIO_of_claims h.reads.tower_ok ihw ihio hreads_io
          hwreads hrun
          hws hb hLb hC hea hta hok

/-- The four sealed claims at every fuel — the joint induction's first
four conjuncts, kept under the landed name so every consumer stands
verbatim. -/
theorem checkSoundAt (hμ : μ.verifiedChecks = true)
    {m : EnvModel V env} (h : TierInputsAt V μ m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaim μ m φ fuel ∧ WhnfClaim μ m φ fuel ∧
        DefEqClaim μ m φ fuel ∧ InferClaim μ m φ fuel := fun fuel =>
  ⟨(checkSoundAtP5 hμ h fuel).1, (checkSoundAtP5 hμ h fuel).2.1,
    (checkSoundAtP5 hμ h fuel).2.2.1, (checkSoundAtP5 hμ h fuel).2.2.2.1⟩

/-- **The env-tier entries, from the fold's invariant**: an `EnvModelM`
supplies the readability bundle, the leaf validity, and the numeral
heads; what remains as arguments is exactly the semantic-content bill
(iota / proj / literal / caps / the two infer clause rows), each named
by its tier in the frontier-transformation table. -/
theorem TierInputsAt.ofEnvModelM (mp : EnvModelM V μ env)
    (hnat_r : ∀ fuel, ReduceNatReads μ mp.base2 φ fuel)
    (hnat : ∀ fuel,
      WhnfClaim μ mp.base2 φ fuel → ReduceNatStep μ mp.base2 φ fuel)
    (hnatQ : ∀ fuel,
      WhnfClaim μ mp.base2 φ fuel →
        ReduceNatStepPQ μ mp.base2 φ fuel) :
    TierInputsAt V μ mp.base2 φ where
  reads := ReadsInputs.ofEnvModelM mp
    (fun _fuel ihw ihio => iotaReads_of (mp.rec_rules φ) ihw ihio)
    hnat_r
  acval_valid := mp.acvalValid
  nat_heads := mp.nat_heads φ
  rec_rules := mp.rec_rules φ
  nat_step := hnat
  nat_stepQ := hnatQ
  caps_ok := mp.caps_ok

end ConLeche.Model
