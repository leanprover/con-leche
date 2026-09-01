import Setlec.SetR.Interp2.HarvestP
import Setlec.SetR.Bridge.Sound

/-!
# The P declaration fold, and the conditional capstone (task #161, P4)

`foldPM` carries `EnvSPOk` — the P invariant plus the η-family
closure — through an accepted stream, and
`no_proof_of_Empty_P_of` is the **milestone-shaped** capstone: the
frozen final statement (`CapstoneP.lean`) conditional on exactly the
named tier bundles.  The conditional form is a milestone, never the
close (the standing ruling); the final `no_proof_of_Empty_P` is this
theorem with the bundles replaced by the tiers' theorems.

The v1 half of the invariant rides the *discharged* v1 fold
machinery verbatim (`declStepS` at the concrete instances
`divModPinS`/`reducePinS`/`stdAxiomKeyS`/`declBasisS`/
`declIndS memberKeyS` — the same instances `foldlM_R` consumes), so
the η closure and the v1 base at every prefix cost nothing new.

The routed bundles, by tier:

* `SemTierInputsP` — the four semantic tiers (`CapstoneP.lean`);
* `LitStabilityP` — the literal guards' stability at a fresh
  value-kind cons.  NOT free in general: a `def` named
  `String.ofList` or `Char.ofNat` can complete string support and
  flip the guard upward; the literal tier discharges the generic
  case by name-disequality and the two pin installs bespoke
  (where it establishes the heads anyway);
* `AxiomStepPB` / `BasisStepPB` / `IndStepPB` — the whole-kind steps
  for the pin/basis/inductive installs (the pin tier's aid is
  `harvestAxiomP`; the basis/inductive tiers mirror the v1
  `declBasisS`/`declIndS` machinery at the P fields).
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  Declaration checkDecl checkDecls fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- The literal guards survive a fresh value-kind cons (see the
module docstring for why this is the literal tier's, not free). -/
def LitStabilityP : Prop :=
  ∀ (env : Env) (c₀ : ConstantInfo),
    ((∃ cv value hint, c₀ = .defnInfo cv value hint) ∨
      (∃ cv value, c₀ = .thmInfo cv value) ∨
      (∃ cv, c₀ = .axiomInfo cv)) →
    env.find? c₀.name = none →
    LitGuardsAgree env ⟨c₀ :: env.consts⟩

/-- The axiom kind's whole step, routed (pin tier; assembly aid:
`harvestAxiomP`). -/
def AxiomStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env} (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {env₂ : Env},
    DeclAxiomR μ F env mp.base2.base.cval cv env₂ →
    Nonempty (EnvS2PM V μ env₂)

/-- The basis kind's whole step, routed (basis tier). -/
def BasisStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {env : Env}, EnvS2PM V μ env →
    ∀ {kind : Setlec.BasisKind} {env₂ : Env},
      DeclBasisR env kind env₂ →
      Nonempty (EnvS2PM V μ env₂)

/-- The inductive kind's whole step, routed (inductive tier). -/
def IndStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env} (mp : EnvS2PM V μ env)
    {block : List ConstantInfo} {env₂ : Env},
    DeclIndR μ F env mp.base2.base.cval block env₂ →
    Nonempty (EnvS2PM V μ env₂)

/-- **The P fold invariant**: the P environment invariant plus the
η-family closure (the v1 fold's second half, reused verbatim). -/
def EnvSPOk (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env) :
    Prop :=
  Nonempty (EnvS2PM V μ env) ∧ EtaFamiliesClosed env

/-- **The per-declaration P step, by dispatch.** -/
theorem declStepPM (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ) (hstab : LitStabilityP)
    (hax : AxiomStepPB V μ) (hbas : BasisStepPB V μ)
    (hind : IndStepPB V μ)
    {F : Nat} {env env₂ : Env} {d : Declaration}
    (mp : EnvS2PM V μ env) (hE : EtaFamiliesClosed env)
    (h : DeclR μ F mp.base2.base.cval env d env₂) :
    EnvSPOk V μ env₂ := by
  have hv1 : Nonempty (EnvS V env₂) ∧ EtaFamiliesClosed env₂ :=
    declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
      (declIndS memberKeyS) mp.base2.base hE h
  refine ⟨?_, hv1.2⟩
  cases d with
  | defnDecl cv value hint =>
    have hsh := h
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hsh
    subst henv2
    exact harvestDefnP hμ hsem divModPinS mp h
      (hstab env
        (.defnInfo ⟨cv.name, cv.levelParams, type'⟩ value' hint)
        (.inl ⟨_, _, _, rfl⟩)
        (Option.isNone_iff_eq_none.mp hcv.1))
  | thmDecl cv value =>
    have hsh := h
    obtain ⟨type', value', hcv, -, -, -, henv2⟩ := hsh
    subst henv2
    exact harvestThmP hμ hsem mp h
      (hstab env (.thmInfo ⟨cv.name, cv.levelParams, type'⟩ value')
        (.inr (.inl ⟨_, _, rfl⟩))
        (Option.isNone_iff_eq_none.mp hcv.1))
  | opaqueDecl cv value =>
    have hsh := h
    obtain ⟨type', value', hcv, -, henv2, -⟩ := hsh
    subst henv2
    exact harvestOpaqueP hμ hsem reducePinS mp h
      (hstab env (.axiomInfo ⟨cv.name, cv.levelParams, type'⟩)
        (.inr (.inr ⟨_, rfl⟩))
        (Option.isNone_iff_eq_none.mp hcv.1))
  | axiomDecl cv => exact hax mp h
  | basisDecl kind => exact hbas mp h
  | indDecl block => exact hind mp h

/-- **The P fold**: `foldlM_R`'s recursion at the P invariant. -/
theorem foldPM (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ) (hstab : LitStabilityP)
    (hax : AxiomStepPB V μ) (hbas : BasisStepPB V μ)
    (hind : IndStepPB V μ) {F : Nat} :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvSPOk V μ env →
      ds.foldlM (checkDecl μ (fueledOps μ F)) env = .ok env' →
      EnvSPOk V μ env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (fueledOps μ F) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨mp⟩, hE⟩ := hm
      exact foldPM hμ hsem hstab hax hbas hind ds env1
        (declStepPM hμ hsem hstab hax hbas hind mp hE
          (checkDeclR_sound mp.base2.base hE hd)) h

/-- **The acceptance theorem, P route — milestone shape** (conditional
on the tier bundles; the final form replaces them with the tiers'
theorems). -/
theorem checkDecls_sound_P_of (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ) (hstab : LitStabilityP)
    (hax : AxiomStepPB V μ) (hbas : BasisStepPB V μ)
    (hind : IndStepPB V μ) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env') :
    Nonempty (EnvS2PM V μ env') :=
  (foldPM hμ hsem hstab hax hbas hind ds Env.empty
    ⟨⟨EnvS2PM.empty V μ⟩, EtaFamiliesClosed.empty⟩ h).1

/-- **The capstone, milestone shape**: no proof of `Empty` is ever
accepted — the collapse-free model of the validated annotations, at
the frozen final statement's hypotheses plus the named tier
bundles. -/
theorem no_proof_of_Empty_P_of (hμ : μ.verified = true)
    (hsem : SemTierInputsP V μ) (hstab : LitStabilityP)
    (hax : AxiomStepPB V μ) (hbas : BasisStepPB V μ)
    (hind : IndStepPB V μ) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨mp⟩ := checkDecls_sound_P_of (V := V) hμ hsem hstab hax
    hbas hind h
  exact no_constant_of_Empty_P mp c hc hty

end Setlec.SetR.Interp2
