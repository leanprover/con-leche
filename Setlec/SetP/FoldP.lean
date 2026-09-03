import Setlec.SetP.AxiomReduceP
import Setlec.SetP.BasisPSigmaP
import Setlec.SetP.DeclIndP
import Setlec.SetR.Bridge.Sound

/-!
# The P declaration fold, and the conditional capstone (task #161, P4)

`foldPM` carries `EnvSPOk` — the P invariant plus the η-family
closure — through an accepted stream, and
`no_proof_of_Empty_P` is the campaign's **close**, at the frozen letter
(`CapstoneP.lean`'s docstring): input-level hypotheses only.  The
milestone-shaped `no_proof_of_Empty_P_of` is kept beside it, now
carrying no bundle at all — every tier step is discharged.

The η half of the fold invariant is `declEtaStep` (`SetR/DeclEta.lean`,
task #161 S3): model-free at five of the six declaration kinds, and at
`indDecl` premised on `declIndS memberKeyS` — the one kind whose
η-closure is still proved interleaved with the `EnvS` member/recursor
folds.  `declStepS` and its four other install obligations
(`divModPinS`/`reducePinS`/`stdAxiomKeyS`/`declBasisS`) are no longer
consulted for it; the harvests keep their own uses of `divModPinS` and
`reducePinS`, which are value-kind obligations, not fold ones.  The v1
base at every prefix is `EnvS2PM.base`, the S3 residue.

The routed bundles, by tier:

* (`LitStabilityP` is GONE: the guard equality it asserted is
  refutable at a support-completing install, and the monotone
  crossing + `natLitSupported_cons_back` made the harvests
  premise-free on the literal guards — the census shrank here);
* nothing.  `AxiomStepPB` (ENDGAME D, `axiomStepPB_of`),
  `BasisStepPB` (ENDGAME H, `basisStepPB_of`) and `IndStepPB`
  (IND TIER part 10, `indStepPB_of`) are all discharged; the census
  is `hμ` alone.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  Declaration checkDecl checkDecls fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-- The axiom kind's whole step — **no longer routed** (ENDGAME D):
`axiomStepPB_of` below discharges it.  The definition is kept because
the pin tier's four branches are stated against it and the census is
read off these signatures. -/
def AxiomStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env} (mp : EnvS2PM V μ env)
    {cv : ConstantVal} {env₂ : Env},
    DeclAxiomR μ F env mp.base.cval cv env₂ →
    Nonempty (EnvS2PM V μ env₂)

/-- **`AxiomStepPB`, discharged — THE PIN BUNDLE IS CLOSED.**  All four
`DeclAxiomR` branches: the two standard axioms (`axiomStdP`, ENDGAME
C), `Lean.trustCompiler` (`axiomTrustCompilerP`, ENDGAME A part 2),
`ofReduceNat`/`ofReduceBool` (`axiomOfReduceP`, ENDGAME D, on the new
`ReduceOpsP` field), and the tolerated skip (`axiomSkipP`, which stores
nothing). -/
theorem axiomStepPB_of (hμ : μ.verified = true) : AxiomStepPB V μ := by
  intro _F _env mp _cv _env₂ hR
  obtain ⟨type', hcv, hbranch⟩ := hR
  rcases hbranch with ⟨hok, rfl⟩ | ⟨hname, hok, rfl⟩ |
    ⟨hor, hok, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · exact axiomStdP hμ mp hcv hok
  · exact axiomTrustCompilerP hμ mp hcv hname hok
  · exact axiomOfReduceP hμ mp hcv hor hok
  · exact axiomSkipP mp

/-- The basis kind's whole step, routed (basis tier). -/
def BasisStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {env : Env}, EnvS2PM V μ env →
    ∀ {kind : Setlec.BasisKind} {env₂ : Env},
      DeclBasisR env kind env₂ →
      Nonempty (EnvS2PM V μ env₂)

/-- **`BasisStepPB`, discharged** (task #161, ENDGAME H): all six
pinned basis blocks install at the P tier.  Exactly `declBasisS`'s
dispatch shape, and — as there — `quotK` is the one branch whose
`DeclBasisR` guard is not vacuous: it needs `Eq` in the prefix, which
is what the block's `Eq` bridge consumes. -/
theorem basisStepPB_of : BasisStepPB V μ := by
  intro env mp kind env₂ h
  obtain ⟨hEq, hchain⟩ := h
  cases kind with
  | eqK => exact declBasisPB_eqK mp hchain
  | natK => exact declBasisPB_natK mp hchain
  | psigmaK => exact declBasisPB_psigmaK mp hchain
  | punitK => exact declBasisPB_punitK mp hchain
  | emptyK => exact declBasisPB_emptyK mp hchain
  | quotK => exact declBasisPB_quotK mp (hEq rfl) hchain

/-- The inductive kind's whole step — **no longer routed** (task #161,
IND TIER part 10): `indStepPB_of` below discharges it.  The definition
is kept because the census is read off these signatures.

The `EtaFamiliesClosed` premise is part of the bundle's *shape*, not a
residue: `declStepPM` carries it as the v1 fold's second half and hands
it over at the call site, and the inductive install genuinely consumes
it (`EtaFamiliesClosedO` at the block, the member fold's η side
condition).  It is an environment fact the fold already owns, never a
hypothesis of the capstone. -/
def IndStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env} (mp : EnvS2PM V μ env)
    {block : List ConstantInfo} {env₂ : Env},
    Setlec.EtaFamiliesClosed env →
    DeclIndR μ F env mp.base.cval block env₂ →
    Nonempty (EnvS2PM V μ env₂)

/-- **`IndStepPB`, discharged — THE INDUCTIVE TIER IS CLOSED**
(`declIndP`, `Interp2/DeclIndP.lean`): the member fold, the recursor
group (provision/fire/swap), the projection functions and the
elimination templates, all four at the reading. -/
theorem indStepPB_of (hμ : μ.verified = true) : IndStepPB V μ := by
  intro _F _env mp _block _env₂ hE h
  exact declIndP hμ mp hE h

/-- **The P fold invariant**: the P environment invariant plus the
η-family closure (the v1 fold's second half, reused verbatim). -/
def EnvSPOk (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env) :
    Prop :=
  Nonempty (EnvS2PM V μ env) ∧ EtaFamiliesClosed env

/-- **The per-declaration P step, by dispatch.** -/
theorem declStepPM (hμ : μ.verified = true) {F : Nat} {env env₂ : Env} {d : Declaration}
    (mp : EnvS2PM V μ env) (hE : EtaFamiliesClosed env)
    (h : DeclR μ F mp.base.cval env d env₂) :
    EnvSPOk V μ env₂ := by
  -- the η half: `declEtaStep` (task #161 S3, the census's C4), which
  -- reads `DeclR`'s freshness guards and needs the collapsed lane at
  -- ONE kind only — `indDecl`, whose η-closure is still proved
  -- interleaved with the `EnvS` member/recursor folds (the finding
  -- recorded in `SetR/DeclEta.lean`).  `declStepS`'s four other
  -- obligations are not consulted here any more.
  refine ⟨?_, Setlec.SetR.declEtaStep
    (fun h' => (declIndS memberKeyS mp.base hE h').2) hE h⟩
  cases d with
  | defnDecl cv value hint =>
    have hsh := h
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hsh
    subst henv2
    obtain ⟨m', hag⟩ := declDefnS divModPinS mp.base h
    exact harvestDefnP hμ mp m' hag (DeclDefnR.toRun h)
  | thmDecl cv value =>
    have hsh := h
    obtain ⟨type', value', hcv, -, -, -, henv2⟩ := hsh
    subst henv2
    obtain ⟨m', hag⟩ := declThmS mp.base h
    exact harvestThmP hμ mp m' hag (DeclThmR.toRun h)
  | opaqueDecl cv value =>
    have hsh := h
    obtain ⟨type', value', hcv, -, henv2, -⟩ := hsh
    subst henv2
    obtain ⟨m', hag, value'', hannv2, hleafEq⟩ :=
      declOpaqueS reducePinS mp.base h
    exact harvestOpaqueP hμ mp m' hag hannv2 hleafEq
      (DeclOpaqueR.toRun h)
  | axiomDecl cv => exact axiomStepPB_of hμ mp h
  | basisDecl kind => exact basisStepPB_of mp h
  | indDecl block => exact indStepPB_of hμ mp hE h

/-- **The P fold**: `foldlM_R`'s recursion at the P invariant. -/
theorem foldPM (hμ : μ.verified = true) {F : Nat} :
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
      exact foldPM hμ ds env1
        (declStepPM hμ mp hE
          (checkDeclR_sound mp.base hE hd)) h

/-- **The acceptance theorem, P route — milestone shape** (conditional
on the tier bundles; the final form replaces them with the tiers'
theorems). -/
theorem checkDecls_sound_P_of (hμ : μ.verified = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env') :
    Nonempty (EnvS2PM V μ env') :=
  (foldPM hμ ds Env.empty
    ⟨⟨EnvS2PM.empty V μ⟩, EtaFamiliesClosed.empty⟩ h).1

/-- **The capstone, milestone shape**: no proof of `Empty` is ever
accepted — the collapse-free model of the validated annotations, at
the frozen final statement's hypotheses plus the named tier
bundles. -/
theorem no_proof_of_Empty_P_of (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verified = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨mp⟩ := checkDecls_sound_P_of (V := V) hμ h
  exact no_constant_of_Empty_P mp c hc hty

/-- **THE CAPSTONE, at the frozen letter** (`CapstoneP.lean`'s
docstring, checked against the goal's own words): *the checker,
running in a validating mode, never accepts a declaration stream in
which some stored constant has type `Empty`.*

Hypotheses are **input-level only** — the accepted run, the stored
constant, its type, plus the validating mode, which is part of the
goal's letter (the annotated checker *is* the verified mode;
`--no-model` ignores annotations by design).  No residue: every tier
step is discharged (`axiomStepPB_of`, `basisStepPB_of`,
`indStepPB_of`), so the conditional milestone form
`no_proof_of_Empty_P_of` above now carries nothing either.  The #16
hypothesis-minimal precedent, met.

`SetTheory V` is the standing parametricity of the consistency
argument (project rule: consistency proofs stay parametric in the
`SetTheory` interface), not a hypothesis about the input. -/
theorem no_proof_of_Empty_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verified = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False :=
  fun c hc hty => no_proof_of_Empty_P_of V hμ h c hc hty

end Setlec.SetR.Interp2
