import Setlec.SetP.Step2.ReadsP
import Setlec.SetP.Step2.ReadsIOP
import Setlec.SetP.Step2.CapsRowsP
import Setlec.SetP.Step2.StrLitP
import Setlec.SetP.Step2.ProjRowsP
import Setlec.SetP.Step2.IotaRowsP

/-!
# The tiers assembly (task #161, P4): one env-fixed bundle, one induction

`checkSoundP_of_inputs` (`AssemblyP.lean`) closes the induction over
the three quarters' ∀-environment input structures.  The declaration
fold cannot inhabit those: it holds an `EnvS2PM` for **one**
environment at a time.  This file is the env-fixed re-assembly:

* `TierInputsAtP` — every residue the P ladder still routes, at one
  `(env, m, φ)`, sorted by discharge tier (install / iota / literal /
  caps).  The env-tier entries are `EnvS2PM` consequences
  (`TierInputsAtP.ofEnvS2PM`); the rest are the semantic-content bill
  the frontier-transformation table records.
* `checkSoundAtP` — the four claims at every fuel, at the fixed
  environment, with the of_claims discharges (batches 6/7) **wired
  in**: proof irrelevance, the spine congruences, η, `stuckIrrel`'s
  cascade, the string expansion, the delta identity, the totality
  factors, and the derived sort fact are all supplied from the
  induction hypotheses at each step — none of them appears in the
  bundle.

The quarter-level ∀-env assemblies (`AssemblyP.lean`) remain the
frozen quarter statements; this file is what the fold consumes.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR (AVExpr)
open Setlec (CheckMode Env Expr Name)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode} {env : Env} {φ : Name → Nat}

/-- **The routed residues, at one environment** (see the module
docstring).  Field order groups the tiers: the `reads` bundle carries
the install/iota/proj/literal *readability* leaves inside it. -/
structure TierInputsAtP (V : Type w) [SetTheory V] (μ : CheckMode)
    {env : Env} (m : EnvS2Core V env) (φ : Name → Nat) : Prop where
  /-- install tier: the readability bundle (its own four leaves are
  iota/proj/literal reads) -/
  reads : ReadsInputsP μ m φ
  /-- install tier: leaf bit-validity -/
  acval_valid : AcvalValidP m
  /-- install tier: the numeral heads -/
  nat_heads : NatHeadsP m φ
  /-- iota tier: the stored recursors' fired contracts — an `EnvS2PM`
  field (`rec_rules`), which with the claims discharges both ι rows
  (`iotaStepP_of`, `iotaReadsP_of`) -/
  rec_rules : RecRulesP m φ
  /-- literal tier: the two acceleration rows, each taking the whnf
  claims at the same fuel (`reduceNat` head-normalises its arguments
  before reading them as literals) -/
  nat_step : ∀ fuel, WhnfClaims2P μ m φ fuel → ReduceNatStepP μ m φ fuel
  nat_stepQ : ∀ fuel,
    WhnfClaims2P μ m φ fuel → ReduceNatStepPQ μ m φ fuel
  /-- caps tier: the stored families' fired capability laws — an
  `EnvS2PM` field (`caps_ok`), which is what discharges the stored
  structure's η and unit fallbacks (`structEtaIrrelP_of_claims`,
  `structUnitIrrelP_of_claims` — the latter after the ratified
  one-premise repair of the unit half; all four capability rows are
  now discharged) -/
  caps_ok : CapsOkP m

/-- **The P soundness ladder at one environment — the five-way joint
induction** (task #172 B4), with every of_claims discharge wired in.
The io claim joined the induction the moment the first converted call
site (the β certificate) made the head-normalisation quarter consume
the slot claim at the same fuel; the four-way form survives as the
projection `checkSoundAtP` below, so every landed consumer stands
verbatim. -/
theorem checkSoundAtP5 (hμ : μ.verified = true)
    {m : EnvS2Core V env} (h : TierInputsAtP V μ m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaims2P μ m φ fuel ∧ WhnfClaims2P μ m φ fuel ∧
        DefEqClaims2P μ m φ fuel ∧ InferClaims2P μ m φ fuel ∧
          InferClaimsIO2P μ m φ fuel := by
  intro fuel
  induction fuel with
  | zero =>
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro d e e' Δa hrun
      rw [Setlec.whnfCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e e' Δa hrun
      rw [Setlec.whnf_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d a b Δa hrun
      rw [Setlec.isDefEqCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e t Δa hrun
      rw [Setlec.inferTypeCore_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
    · intro d e t Δa hrun
      rw [Setlec.inferTypeCoreIO_zero] at hrun
      simp [throw, throwThe, MonadExceptOf.throw] at hrun
  | succ fuel ih =>
    obtain ⟨ihwc, ihw, ihd, ihi, ihio⟩ := ih
    -- the totality factors, from the reads bundle
    have hreads : InferReadsP m μ φ fuel := inferReadsP_of h.reads
    have hwreads : WhnfReadsP m μ φ fuel := whnfReadsP_of h.reads
    have hex : WhnfCoreExistsP μ m φ fuel := whnfCoreExistsP_of h.reads
    have hexi : InferExistsP μ m φ fuel := inferExistsP_of h.reads
    have hreads_io : InferReadsIOP m μ φ fuel :=
      inferReadsIOP_of h.reads fuel
    -- the slot facts (task #172 B4): existence and the premise-form
    -- claim at the knot's io slot, from the two lanes
    have hexis : InferExistsIOSP μ m φ fuel := by
      intro d e t Δa hrun hws hb hLb ea hC hea
      cases hg : μ.betaGate with
      | false =>
        rw [Setlec.inferTypeIO_off hg] at hrun
        exact hexi hrun hws hb hLb hC hea
      | true =>
        rw [Setlec.inferTypeIO_on hg] at hrun
        exact hreads_io hrun hws hb hLb (LeafReadsP.of_ctxOkP hC) hea
    have ihis : InferClaimsIOS2P μ m φ fuel :=
      inferClaimsIOS2P_of ihi ihio
    -- the derived sort facts
    have hss : SortSemAtP m μ φ fuel :=
      sortSemAtP_of_claims ihw ihi hreads
    have hssio : SortSemAtIOP m μ φ fuel :=
      sortSemAtIOP_of_claims ihw ihio hreads_io
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · -- the head-normalisation quarter
      exact whnfCore_claimsP m hex
        (betaCertP_of_claims m hexis ihd ihis)
        (iotaStepP_of h.rec_rules h.caps_ok h.reads.const_ty
          h.acval_valid ihw ihd ihi hreads hwreads)
        (projStepP_of_claims ihwc ihw ihd ihi hreads hwreads) ihwc
    · -- the reduction loop
      exact whnf_claimsP m hex ihwc (h.nat_step fuel ihw)
        (deltaP_of m h.reads.defn)
    · -- the defeq quarter, of_claims discharges wired
      have hsi : StuckIrrelPQ μ m φ fuel :=
        stuckIrrelP_of_claims ihw ihi hreads
          (unitIrrelPQ_of_claims ihw ihi hreads hwreads)
          (pairEtaIrrelP_of_claims ihw ihd ihi hreads hwreads)
          (structEtaIrrelP_of_claims h.caps_ok h.reads.const_ty
            h.acval_valid ihw ihd ihi hreads hwreads)
          (structUnitIrrelP_of_claims h.caps_ok ihw ihd ihi hreads
            hwreads)
      have hstep : DefEqStepAtP μ m φ fuel :=
        defeqStep_claimP (whnfCoreReductExistsP_of' h.reads) ihwc
          (denotePDeltaP_of h.reads) (h.nat_stepQ fuel ihw)
          (proofIrrelPQ_of_claims ihw ihi hreads
            (unitIrrelPQ_of_claims ihw ihi hreads hwreads))
          (defeqStuck_claimP hμ ihd hsi denotePStrLit_of_guard
            (acvalParamsP m) (appCongrStuckP_of_claims ihd)
            (etaCertStepP_of_claims hμ ihw ihd ihi hreads hwreads))
          (defEqSpineP_of_claims ihd (acvalParamsP m))
      -- (`defeq_claimsP hstep` trips an implicit-eta unification
      -- wrinkle at the `DefEqStepAtP` unfolding; its two-line body is
      -- inlined instead)
      intro d a b Δa hrun hwa hba' hLa hwb hbb hLb aa ba hCa hCb
        hda hdb
      rw [Setlec.isDefEqCore_succ, defeqBody] at hrun
      exact defeqLoop_contP hstep defeqLoopFuel d hrun hwa hba' hLa
        hwb hbb hLb hCa hCb hda hdb
    · -- the infer quarter (the eleven-arm dispatcher, env-fixed)
      intro d e t Δa hrun hws hb hLb ea ta hC hea hta
      match e, hrun, hws, hb, hLb, hC, hea with
      | .sort u, hrun, _, _, _, _, hea =>
        exact infer_sort_claimP m hrun hea hta
      | .bvar i, hrun, _, _, _, _, hea =>
        exact infer_bvar_claimP m hrun hea hta
      | .fvar idx nm ty, hrun, _, _, _, hC, hea =>
        exact infer_fvar_claimP m hC hrun hea hta
      | .const nm us, hrun, _, _, _, _, hea =>
        exact infer_const_claimP m h.reads.const_ty h.acval_valid
          hrun hea hta
      | .lit (.natVal k), hrun, _, _, _, _, hea =>
        exact infer_natLit_claimP m h.nat_heads h.acval_valid
          hrun hea hta
      | .lit (.strVal s), hrun, _, _, _, _, hea =>
        exact inferStrLitStepP_of_claims h.reads.const_ty h.acval_valid
          h.nat_heads hrun hea hta
      | .forallE nm ty body mb, hrun, hws, hb, hLb, hC, hea =>
        exact infer_forallE_claimP m hμ hss hrun hws hb hLb hC hea hta
      | .lam nm ty body mb, hrun, hws, hb, hLb, hC, hea =>
        exact infer_lam_claimP m hμ hss ihi hrun hws hb hLb hC hea hta
      | .app fe ae, hrun, hws, hb, hLb, hC, hea =>
        exact infer_app_claimP m hreads hwreads ihw ihd ihi hrun
          hws hb hLb hC hea hta
      | .letE nm ty val bd, hrun, hws, hb, hLb, hC, hea =>
        exact infer_letE_claimP m hss hreads ihi hrun hws hb hLb
          hC hea hta
      | .proj sn i pe, hrun, hws, hb, hLb, hC, hea =>
        exact inferProjStepP_of_claims ihw ihi hreads hwreads hrun hws hb
          hLb hC hea hta
    · -- the io quarter (the eleven-arm dispatcher, env-fixed;
      -- task #172 B4)
      intro d e t Δa hrun hws hb hLb ea ta hC hea hta hok
      match e, hrun, hws, hb, hLb, hC, hea, hok with
      | .sort u, hrun, _, _, _, _, hea, _ =>
        exact infer_sort_claimIOP m hrun hea hta
      | .bvar i, hrun, _, _, _, _, hea, _ =>
        exact infer_bvar_claimIOP m hrun hea hta
      | .fvar idx nm ty, hrun, _, _, _, hC, hea, _ =>
        exact infer_fvar_claimIOP m hC hrun hea hta
      | .const nm us, hrun, _, _, _, _, hea, _ =>
        exact infer_const_claimIOP m (h.reads.const_ty) hrun hea hta
      | .lit (.natVal k), hrun, _, _, _, _, hea, _ =>
        exact infer_natLit_claimIOP m h.nat_heads h.acval_valid hrun
          hea hta
      | .lit (.strVal str), hrun, _, _, _, _, hea, _ =>
        exact infer_strLit_claimIOP m
          (inferStrLitStepP_of_claims h.reads.const_ty h.acval_valid
            h.nat_heads) hrun hea hta
      | .forallE nm ty body mb, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_forallE_claimIOP m hμ hssio hrun hws hb hLb hC hea
          hta hok
      | .lam nm ty body mb, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_lam_claimIOP m hμ hssio ihio hrun hws hb hLb hC hea
          hta hok
      | .app fe ae, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_app_claimIOP m hreads_io hwreads ihw ihd ihio hrun
          hws hb hLb hC hea hta hok
      | .letE nm ty val bd, hrun, hws, hb, hLb, hC, hea, hok =>
        exact infer_letE_claimIOP m ihio hrun hws hb hLb hC hea hta hok
      | .proj sn i pe, hrun, hws, hb, hLb, hC, hea, hok =>
        exact inferProjStepIOP_of_claims ihw ihio hreads_io hwreads hrun
          hws hb hLb hC hea hta hok

/-- The four sealed claims at every fuel — the joint induction's first
four conjuncts, kept under the landed name so every consumer stands
verbatim. -/
theorem checkSoundAtP (hμ : μ.verified = true)
    {m : EnvS2Core V env} (h : TierInputsAtP V μ m φ) :
    ∀ fuel : Nat,
      WhnfCoreClaims2P μ m φ fuel ∧ WhnfClaims2P μ m φ fuel ∧
        DefEqClaims2P μ m φ fuel ∧ InferClaims2P μ m φ fuel := fun fuel =>
  ⟨(checkSoundAtP5 hμ h fuel).1, (checkSoundAtP5 hμ h fuel).2.1,
    (checkSoundAtP5 hμ h fuel).2.2.1, (checkSoundAtP5 hμ h fuel).2.2.2.1⟩

/-- The io claim at every fuel — the joint induction's fifth
conjunct. -/
theorem checkSoundAtIOP (hμ : μ.verified = true)
    {m : EnvS2Core V env} (h : TierInputsAtP V μ m φ) :
    ∀ fuel : Nat, InferClaimsIO2P μ m φ fuel := fun fuel =>
  (checkSoundAtP5 hμ h fuel).2.2.2.2

/-- **The env-tier entries, from the fold's invariant**: an `EnvS2PM`
supplies the readability bundle, the leaf validity, and the numeral
heads; what remains as arguments is exactly the semantic-content bill
(iota / proj / literal / caps / the two infer clause rows), each named
by its tier in the frontier-transformation table. -/
theorem TierInputsAtP.ofEnvS2PM (mp : EnvS2PM V μ env)
    (hacc : ∀ {F d : Nat} {x t : Expr},
      Setlec.inferTypeCore μ env F d x = .ok t →
      Expr.WScoped d x → x.looseBVarsBounded 0 = true →
      Expr.LeavesBounded x →
      ∃ xa, denoteP mp.base2.acval env φ d x = some xa)
    (hnat_r : ∀ fuel, ReduceNatReadsP μ mp.base2 φ fuel)
    (hnat : ∀ fuel,
      WhnfClaims2P μ mp.base2 φ fuel → ReduceNatStepP μ mp.base2 φ fuel)
    (hnatQ : ∀ fuel,
      WhnfClaims2P μ mp.base2 φ fuel →
        ReduceNatStepPQ μ mp.base2 φ fuel) :
    TierInputsAtP V μ mp.base2 φ where
  reads := ReadsInputsP.ofEnvS2PM mp
    (fun _fuel => iotaReadsP_of (mp.rec_rules φ) hacc) hnat_r
  acval_valid := mp.acvalValidP
  nat_heads := mp.nat_heads φ
  rec_rules := mp.rec_rules φ
  nat_step := hnat
  nat_stepQ := hnatQ
  caps_ok := mp.caps_ok

end Setlec.SetR.Interp2
