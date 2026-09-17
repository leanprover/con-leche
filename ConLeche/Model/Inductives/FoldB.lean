module

public import ConLeche.Model.Inductives.NestedPremise
public import ConLeche.Semantics.Inductives.DeclNative
import ConLeche.Model.Inductives.BasisBlocksFold
import ConLeche.Semantics.Bridge.Sound
import ConLeche.Semantics.Inductives.DeclSumEta
public section

/-!
# The declaration fold at the model WITH ITS BLOCKS (task #315, M8's mechanical half)

Every arm of `declStep_preserves` (`Model/Fold.lean`) but one is a name
swap at `EnvModelB`; the exception is the MODELED arm, which is not to
be proved but DELETED once the kernel's `.indDecl` dispatch takes the
nested route (DESIGN §U.55 (c)).  Until then it stands here as ONE
hypothesis, `ModeledStepB`, and nothing else in the fold is open.

**Why this is a module of its own.**  The B fold cannot live in
`Model/Fold.lean`: the value kinds' carrier agreements
(`axiomStepAgree_of`, `basisStepAgree_of`) live there, and both
`Model/Inductives/EnvModelBStages.lean` and
`Model/Inductives/BasisBlocksFold.lean` import that module for them —
so the flip's own theorems sit ABOVE it.  M8 either moves those two
theorems down or keeps this module; nothing else in the tree cares,
because `EnvModelB` EXTENDS `EnvModelM` and the capstones read the
`.toEnvModelM` projection (DESIGN §U.55 (c) 5).
-/

namespace ConLeche.Model
open ConLeche.Semantics
open ConLeche.SetModel

open ConLeche.Term ConLeche.Verify SetTheory
open ConLeche (Env Name ConstantInfo ConstantVal)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}
variable {pins : List ConLeche.NatOpPinSet}

/-- **THE MODELED ARM, as a hypothesis** (task #315 M8's single hole):
`declInd` installs an arbitrary stream block through the model
artifacts and builds NO block model, and `DeclIndRun` carries no K.34
read-back to tie one to the reading `containerInfo?` makes of its
output — DESIGN §U.55 (c).  The arm is not to be discharged: when the
kernel's `.indDecl` dispatch takes the nested route, `DeclIndRun`
leaves `DeclIndRunDispatch` with `declInd`, and this hypothesis and its
consumer's third case go with it. -/
def ModeledStepB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {F : Nat} {env : Env}, EnvModelB V μ env → ∀ {block : List ConstantInfo} {env₂ : Env},
    ConLeche.EtaFamiliesClosed env → ConLeche.Semantics.DeclIndRun μ F env block env₂ →
    Nonempty (EnvModelB V μ env₂)

/-- **The model WITH ITS BLOCKS survives an inductive block** —
`declInductive`'s twin at `EnvModelB`, the same case split over the
dispatch's three arms: `declNativeB` (§U.52), `declMutualB` (§U.55 (a))
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
  | basisDecl kind => exact basisStepB_of mb hrun
  | quotDecl k cv =>
    cases k with
    | type => exact basisStepB_of mb hrun
    | _ => exact (show env₂ = env from hrun) ▸ ⟨mb⟩
  | indDecl block nP =>
    simp only [ConLeche.Semantics.DeclRun] at hrun
    split at hrun
    · exact basisStepB_of mb hrun
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
nothing of the flip (DESIGN §U.55 (c) 5). -/
theorem checkDeclsPure_soundB_of (hμ : μ.verifiedChecks = true) (hmod : ModeledStepB V μ)
    {F : Nat} {ds : List ConLeche.Declaration} {env' : Env}
    (h : ConLeche.checkDeclsPure μ (ConLeche.fueledOps μ F) pins ds = .ok env') :
    Nonempty (EnvModelB V μ env') :=
  (foldPMB hμ hmod ds ConLeche.Env.empty
    ⟨⟨EnvModelB.empty V μ⟩, ConLeche.EtaFamiliesClosed.empty⟩ h).1

end ConLeche.Model
