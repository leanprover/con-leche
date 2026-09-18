module

import ConLeche.Model.StepAgree
public import ConLeche.Model.Inductives.NestedPremise
import ConLeche.Model.Inductives.BasisBlocksFold
import ConLeche.Model.Harvest
import ConLeche.Model.DeclInd
import ConLeche.Model.Inductives.DeclStruct
import ConLeche.Semantics.IndBlockFacts
public import ConLeche.Semantics.Bridge.Sound
import ConLeche.Semantics.Inductives.DeclSumEta
import ConLeche.Model.Inductives.DeclSum
import ConLeche.Model.Inductives.DeclNative
import ConLeche.Model.Inductives.DeclInductive
public section

/-!
# The P declaration fold, and the conditional capstone (task #161, P4)

`foldPM` carries `EnvModelOk` — the P invariant plus the η-family
closure — through an accepted stream, and
`no_proof_of_Empty_pure` is the campaign's **close**, at the frozen letter
(`CapstoneP.lean`'s docstring): input-level hypotheses only.  The
milestone-shaped `no_proof_of_Empty_pure_of` is kept beside it, now
carrying no bundle at all — every tier step is discharged.

The η half of the fold invariant is `declEtaStepRun`
(`SetBase/DeclEta.lean`, task #161 S3) and is now **model-free at every
kind**: S3 left `indDecl` premised on `declIndS memberKeyS mp.base` —
the one kind whose η-closure was proved interleaved with the `EnvS`
member/recursor folds — and S5's ind unit (`declIndEtaClosed`,
`SetBase/IndBlockR.lean`) proves it from `DeclIndRun` alone.  No install
obligation is consulted for the η half; the harvests keep their own
uses of `divModPinS` and `reducePinS`, which are value-kind
obligations, not fold ones.  The v1 base at every prefix is
`EnvModelM.base`, the S3 residue.

The routed bundles, by tier:

* (`LitStabilityP` is GONE: the guard equality it asserted is
  refutable at a support-completing install, and the monotone
  crossing + `natLitSupported_cons_back` made the harvests
  premise-free on the literal guards — the census shrank here);
* nothing.  `AxiomStepPB` (ENDGAME D, `axiomStepPB_of`),
  `BasisStepPB` (ENDGAME H, `basisStepPB_of`) and `IndStepPB`
  (IND TIER part 10, `indStepPB_of`) are all discharged; the census
  is `hμ` alone.

The axiom and basis steps' CARRIER AGREEMENTS (`axiomStepAgree_of`,
`basisStepAgree_of`) live in `Model/StepAgree.lean`, below this module
(task #315 M8 step 1, DESIGN §U.67 (g) 1): the environment model's
block field is maintained by them, so the modules that maintain it
read them — and while they lived here, every theorem of the flip sat
above this module.  The two bundles below are their `Nonempty`
projections.
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche.Semantics ConLeche.SetModel
open ConLeche (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  Declaration checkDecl checkDeclsPure fueledOps)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}
variable {pins : List ConLeche.NatOpPinSet}

/-- The axiom kind's whole step — **no longer routed** (ENDGAME D):
`axiomStepPB_of` below discharges it.  The definition is kept because
the pin tier's four branches are stated against it and the census is
read off these signatures. -/
def AxiomStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  -- task #161 S4: the relation premise is now the run projection
  -- (`DeclAxiomRun`), which names no valuation — so the carrier `_mp`
  -- no longer appears in the premise's *type*.  It stays as the
  -- invariant the four branches consume.
  ∀ {F : Nat} {env : Env} (_mp : EnvModelM V μ env)
    {cv : ConstantVal} {env₂ : Env},
    DeclAxiomRun μ F env cv env₂ →
    Nonempty (EnvModelM V μ env₂)

/-- **`AxiomStepPB`, discharged — THE PIN BUNDLE IS CLOSED.**  All four
`DeclAxiomR` branches: the two standard axioms (`axiomStd`, ENDGAME
C), `Lean.trustCompiler` (`axiomTrustCompiler`, ENDGAME A part 2),
`ofReduceNat`/`ofReduceBool` (`axiomOfReduce`, ENDGAME D, on the new
`ReduceOps` field), and the tolerated skip (`axiomSkip`, which stores
nothing). -/
theorem axiomStepPB_of (hμ : μ.verifiedChecks = true) : AxiomStepPB V μ := by
  intro _F _env mp _cv _env₂ hR
  exact ⟨(axiomStepAgree_of hμ mp hR).choose⟩

/-- The basis kind's whole step, routed (basis tier). -/
def BasisStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {env : Env}, EnvModelM V μ env →
    ∀ {kind : ConLeche.BasisKind} {env₂ : Env},
      DeclBasisRun μ env kind env₂ →
      Nonempty (EnvModelM V μ env₂)

/-- **`BasisStepPB`, discharged** (task #161, ENDGAME H; the `False` block
at task #181): all pinned basis blocks install at the P tier —
`basisStepAgree_of` forgetting its agreement. -/
theorem basisStepPB_of : BasisStepPB V μ := by
  intro env mp kind env₂ h
  exact ⟨(basisStepAgree_of mp h).choose⟩

/-- The inductive kind's whole step — **no longer routed** (task #161,
IND TIER part 10): `indStepPB_of` below discharges it.  The definition
is kept because the census is read off these signatures.

The `EtaFamiliesClosed` premise is part of the bundle's *shape*, not a
residue: `declStep_preserves` carries it as the v1 fold's second half and hands
it over at the call site, and the inductive install genuinely consumes
it (`EtaFamiliesClosedO` at the block, the member fold's η side
condition).  It is an environment fact the fold already owns, never a
hypothesis of the capstone. -/
def IndStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  -- the input carrier is the bundle's *subject*, not a datum the
  -- premise mentions: since S11b the ind premise is the **run**
  -- record, which names no valuation, so `_mp` appears only in the
  -- conclusion's shape ("a carrier here gives a carrier there").
  ∀ {F : Nat} {env : Env} (_mp : EnvModelM V μ env)
    {block : List ConstantInfo} {env₂ : Env},
    ConLeche.EtaFamiliesClosed env →
    DeclIndRun μ F env block env₂ →
    Nonempty (EnvModelM V μ env₂)

/-- **`IndStepPB`, discharged — THE INDUCTIVE TIER IS CLOSED**
(`declInd`, `Interp/DeclIndP.lean`): the member fold, the recursor
group (provision/fire/swap) and the projection functions, all three at
the reading. -/
theorem indStepPB_of (hμ : μ.verifiedChecks = true) : IndStepPB V μ := by
  intro _F _env mp _block _env₂ hE h
  exact declInd hμ mp hE h

/-- **The P fold invariant**: the P environment invariant plus the
η-family closure (the v1 fold's second half, reused verbatim). -/
@[expose] def EnvModelOk (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env) :
    Prop :=
  Nonempty (EnvModelM V μ env) ∧ EtaFamiliesClosed env

/-- **The per-declaration P step, by dispatch.**

**Task #161 S11a — the premise is the RUN record, not `DeclR`.**  Since
S4 this theorem took `DeclR` and projected (`DeclR.toRun`) on its first
line, which made every P step's *statement* valuation-free while its
*proof path* still ran through the derivation bridge: the S10 seal's
residual B ("a projection composed with a bridge is not a projection").
The projection is now done by the *producer* instead — the five
non-`ind` kinds have run-only bridges (`checkDeclRun_of`,
`SetBase/Bridge/DeclRun.lean`) and the `ind` kind arrives through
`DeclRun`'s `Ind` parameter — so this step consumes exactly what it
reads, and no step below changed a line. -/
theorem declStep_preserves (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env} {d : Declaration}
    (mp : EnvModelM V μ env) (hE : EtaFamiliesClosed env)
    (hrun : DeclRun μ F (ConLeche.Semantics.DeclIndRunDispatch μ F env)
      env d env₂) :
    EnvModelOk V μ env₂ := by
  -- the η half: `declEtaStepRun` (task #161 S3, the census's C4), now
  -- MODEL-FREE at every kind.  S3's stop-and-name left `indDecl`'s
  -- η-closure premised on `declIndS memberKeyS mp.base`; S5's ind unit
  -- (`SetBase/IndBlockR.lean`) proves it from `DeclIndRun` alone, so the
  -- fold consults no install obligation for its η half at all.
  -- task #175 wiring W5: the η half is FLAG-AGNOSTIC — the `.indDecl`
  -- dispatch's own case split (`declIndRunDispatchEtaClosed`)
  refine ⟨?_, ConLeche.Semantics.declEtaStepRun
    (fun h' => ConLeche.Semantics.declIndRunDispatchEtaClosed hE h') hE hrun⟩
  cases d with
  | defnDecl cv value hint =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hsh
    subst henv2
    exact ⟨(harvestDefn hμ mp hrun).choose⟩
  | thmDecl cv value =>
    have hsh := hrun
    -- one dash fewer than the `DeclR` pattern: the run record has no
    -- is-a-proposition derivation row (task #161 S11a)
    obtain ⟨type', value', hcv, -, -, henv2⟩ := hsh
    subst henv2
    exact ⟨(harvestThm hμ mp hrun).choose⟩
  | opaqueDecl cv value =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -⟩ := hsh
    subst henv2
    exact ⟨(harvestOpaque hμ mp hrun).choose⟩
  | axiomDecl cv => exact axiomStepPB_of hμ mp hrun
  | basisDecl kind => exact basisStepPB_of mp hrun
  | quotDecl k cv =>
    -- task #293: the quotient package's `type` record installs the
    -- pinned block; its other records install nothing
    cases k with
    | type => exact basisStepPB_of mp hrun
    | _ => exact (show env₂ = env from hrun) ▸ ⟨mp⟩
  | indDecl block nP =>
    -- task #293: a block the fold recognises as one of the five pinned
    -- ones installs the PIN; everything else takes the `.indDecl`
    -- dispatch — a RECOGNISED block directly (ONE ROUTE, task #210),
    -- the rest through the modeled path, the kernel's own two-way case
    -- split (task #219)
    simp only [ConLeche.Semantics.DeclRun] at hrun
    split at hrun
    · exact basisStepPB_of mp hrun
    · -- task #315: ONE statement for every block kind (`declInductive`,
      -- `Model/Inductives/DeclInductive.lean`); the two-way case split
      -- lives there
      exact declInductive hμ mp hE hrun

/-- **The P fold**: `foldlM_R`'s recursion at the P invariant. -/
theorem foldPM (hμ : μ.verifiedChecks = true) {F : Nat} :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvModelOk V μ env →
      ds.foldlM (checkDecl μ (fueledOps μ F) pins) env = .ok env' →
      EnvModelOk V μ env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (fueledOps μ F) pins env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨mp⟩, hE⟩ := hm
      exact foldPM hμ ds env1
        (declStep_preserves hμ mp hE
          -- **the RUN bridge, from the P carrier's own `EnvFacts`**
          -- (task #161 S11a).  S7 (Wall C step (e)) made the bridge
          -- model-free, so the fold's last v1 round trip became the
          -- projection `EnvModelM.toEnvFacts`; S11a makes it
          -- *derivation*-free at the five non-`ind` kinds, so the only
          -- route from here into the relation tier is the `Ind`
          -- premise `checkDeclRun_ofEnvFactsE` fills with `declIndRR`.
          (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hd)) h

/-- **The acceptance theorem, P route — milestone shape** (conditional
on the tier bundles; the final form replaces them with the tiers'
theorems). -/
theorem checkDeclsPure_sound_of (hμ : μ.verifiedChecks = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
    Nonempty (EnvModelM V μ env') :=
  (foldPM hμ ds Env.empty
    ⟨⟨EnvModelM.empty V μ⟩, EtaFamiliesClosed.empty⟩ h).1

/-- **The capstone, milestone shape**: no proof of `Empty` is ever
accepted — the collapse-free model of the validated annotations, at
the frozen final statement's hypotheses plus the named tier
bundles. -/
theorem no_proof_of_Empty_pure_of (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨mp⟩ := checkDeclsPure_sound_of (V := V) hμ h
  exact no_constant_of_Empty mp c hc hty

/-- **THE CAPSTONE, at the frozen letter** (`CapstoneP.lean`'s
docstring, checked against the goal's own words): *the checker,
running in a validating mode, never accepts a declaration stream in
which some stored constant has type `Empty`.*

Hypotheses are **input-level only** — the accepted run, the stored
constant, its type, plus the validating mode, which is part of the
goal's letter (the annotated checker *is* the verified mode;
`--trusted` ignores annotations by design).  No residue: every tier
step is discharged (`axiomStepPB_of`, `basisStepPB_of`,
`indStepPB_of`), so the conditional milestone form
`no_proof_of_Empty_pure_of` above now carries nothing either.  The #16
hypothesis-minimal precedent, met.

`SetTheory V` is the standing parametricity of the consistency
argument (project rule: consistency proofs stay parametric in the
`SetTheory` interface), not a hypothesis about the input. -/
theorem no_proof_of_Empty_pure (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False :=
  fun c hc hty => no_proof_of_Empty_pure_of V hμ h c hc hty

/-- **THE CAPSTONE ABOUT `False`** (task #181): *the checker, running
in a validating mode, never accepts a declaration stream in which some
stored constant has type `False`.*  The same letter as
`no_proof_of_Empty_pure`, at the pinned `False` block
(`ConLeche/Kernel/Basis/False.lean`): `False` is a reserved basis name
whose stored declaration and leaf are fixed by the pin, so — exactly as
for `Empty` — the statement carries no hypothesis about how the stream
declared `False`.  Hypotheses are input-level only: the validating
mode, the accepted run, the stored constant, its type. -/
theorem no_proof_of_False_pure (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := checkDeclsPure_sound_of (V := V) hμ h
  exact fun c hc hty => no_constant_of_False mp c hc hty

/-! ## THE SAME FOLD AT THE MODEL WITH ITS BLOCKS (task #315, M8)

Every arm of `declStep_preserves` but one is a name swap at
`EnvModelB` (DESIGN §U.66 (c)); the exception is the MODELED arm,
which is not to be proved but DELETED once the kernel's `.indDecl`
dispatch takes the nested route.  Until then it stands as ONE
hypothesis, `ModeledStepB`, and nothing else in the fold is open.

The B fold lives HERE, with the A fold, and inherits its consumers:
`EnvModelB` EXTENDS `EnvModelM`, so `checkDeclsPure_sound_of` stays
stated at `EnvModelM` and the capstones, `ConLeche/MainTheorem.lean`
included, see nothing of the flip (DESIGN §U.66 (c) 5).  What kept it
out of this module until now was the value kinds' carrier agreements,
which the B route's own modules import — they are one module down
since M8's first step (`Model/StepAgree.lean`). -/

/-- **THE MODELED ARM, as a hypothesis** (task #315 M8's single hole):
`declInd` installs an arbitrary stream block through the model
artifacts and builds NO block model, and `DeclIndRun` carries no K.34
read-back to tie one to the reading `containerInfo?` makes of its
output — DESIGN §U.66 (c).  The arm is not to be discharged: when the
kernel's `.indDecl` dispatch takes the nested route, `DeclIndRun`
leaves `DeclIndRunDispatch` with `declInd`, and this hypothesis and its
consumer's third case go with it. -/
def ModeledStepB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env}, EnvModelB V μ env → ∀ {block : List ConstantInfo} {env₂ : Env},
    ConLeche.EtaFamiliesClosed env → ConLeche.Semantics.DeclIndRun μ F env block env₂ →
    Nonempty (EnvModelB V μ env₂)

/-- **The model WITH ITS BLOCKS survives an inductive block** —
`declInductive`'s twin at `EnvModelB`, the same case split over the
dispatch's three arms: `declNativeB` (§U.52), `declMutualB` (§U.66 (a))
and the hypothesis. -/
theorem declInductiveB (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {block : List ConstantInfo} {nP : Nat} (mb : EnvModelB V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hmod : ModeledStepB V μ)
    (h : ConLeche.Semantics.DeclIndRunDispatch μ F env block nP env₂) :
    Nonempty (EnvModelB V μ env₂) := by
  unfold ConLeche.Semantics.DeclIndRunDispatch at h
  cases hdf : ConLeche.nativeParts? nP block with
  | some p =>
    rw [hdf] at h
    exact declNativeB hμ mb hE hdf h
  | none =>
    rw [hdf] at h
    cases hmf : ConLeche.mutualParts? nP block with
    | some q =>
      rw [hmf] at h
      exact declMutualB hμ mb hE (by rw [← ConLeche.mutualParts?_recPinned hmf]; exact h.1) h
    | none =>
      rw [hmf] at h
      exact hmod mb hE h

/-- **The P fold invariant WITH THE BLOCKS**: `EnvModelOk`'s twin.  The
η half does not move — it has been model-free since task #161 S3. -/
@[expose] def EnvModelOkB (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env) : Prop :=
  Nonempty (EnvModelB V μ env) ∧ ConLeche.EtaFamiliesClosed env

/-- **The per-declaration step at the model WITH ITS BLOCKS** —
`declStep_preserves` arm by arm, every one of them a name swap. -/
theorem declStepB_preserves (hμ : μ.verifiedChecks = true) {F : Nat} {env env₂ : Env}
    {d : ConLeche.Declaration} (mb : EnvModelB V μ env)
    (hE : ConLeche.EtaFamiliesClosed env) (hmod : ModeledStepB V μ)
    (hrun : ConLeche.Semantics.DeclRun μ F (ConLeche.Semantics.DeclIndRunDispatch μ F env)
      env d env₂) :
    EnvModelOkB V μ env₂ := by
  refine ⟨?_, ConLeche.Semantics.declEtaStepRun
    (fun h' => ConLeche.Semantics.declIndRunDispatchEtaClosed hE h') hE hrun⟩
  cases d with
  | defnDecl cv value hint =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hsh
    subst henv2
    exact envModelB_defn hμ mb hrun
  | thmDecl cv value =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, -, henv2⟩ := hsh
    subst henv2
    exact envModelB_thm hμ mb hrun
  | opaqueDecl cv value =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -⟩ := hsh
    subst henv2
    exact envModelB_opaque hμ mb hrun
  | axiomDecl cv => exact envModelB_axiom hμ mb hrun
  | basisDecl kind => exact basisStepB_of hμ mb hrun
  | quotDecl k cv =>
    cases k with
    | type => exact basisStepB_of hμ mb hrun
    | _ => exact (show env₂ = env from hrun) ▸ ⟨mb⟩
  | indDecl block nP =>
    simp only [ConLeche.Semantics.DeclRun] at hrun
    split at hrun
    · exact basisStepB_of hμ mb hrun
    · exact declInductiveB hμ mb hE hmod hrun

/-- **The P fold at the model WITH ITS BLOCKS**: `foldPM`'s twin, the
base case `EnvModelB.empty`. -/
theorem foldPMB (hμ : μ.verifiedChecks = true) (hmod : ModeledStepB V μ) {F : Nat} :
    ∀ (ds : List ConLeche.Declaration) (env : Env) {env' : Env},
      EnvModelOkB V μ env →
      ds.foldlM (ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pins) env = .ok env' →
      EnvModelOkB V μ env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : ConLeche.checkDecl μ (ConLeche.fueledOps μ F) pins env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨mb⟩, hE⟩ := hm
      exact foldPMB hμ hmod ds env1
        (declStepB_preserves hμ mb hE hmod
          (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hd)) h

/-- **The acceptance theorem at the model WITH ITS BLOCKS**, modulo the
modeled arm: `checkDeclsPure_sound_of`'s twin.  Its `.toEnvModelM`
projection IS `checkDeclsPure_sound_of`, which is why the capstones see
nothing of the flip (DESIGN §U.66 (c) 5). -/
theorem checkDeclsPure_soundB_of (hμ : μ.verifiedChecks = true) (hmod : ModeledStepB V μ)
    {F : Nat} {ds : List ConLeche.Declaration} {env' : Env}
    (h : ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F) pins ds = .ok env') :
    Nonempty (EnvModelB V μ env') :=
  (foldPMB hμ hmod ds ConLeche.Env.empty
    ⟨⟨EnvModelB.empty V μ⟩, ConLeche.EtaFamiliesClosed.empty⟩ h).1

end ConLeche.Model
