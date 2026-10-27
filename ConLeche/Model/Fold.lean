module

import ConLeche.Model.AxiomReduce
import ConLeche.Model.Inductives.StructEntryKit
public import ConLeche.Semantics.Bridge.Sound
import ConLeche.Model.Inductives.SumKit
import ConLeche.Model.BasisFalse
import ConLeche.Model.Cover
public import ConLeche.Model.Inductives.DeclBlockStep
import ConLeche.Kernel.Checker
import ConLeche.Kernel.CheckerBase
import ConLeche.Model.Reading.Levels
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Capstone
import ConLeche.Model.IndCons
import ConLeche.Model.BasisEq
import ConLeche.Model.Swap
import ConLeche.Semantics.DeclRun
import ConLeche.Semantics.EnvFacts
import ConLeche.Semantics.DeclEta
import ConLeche.Verify.Abstract
import ConLeche.Verify.Denote.EnvExt
import ConLeche.Verify.Denote
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.NestedRead
import ConLeche.Verify.Shift
import ConLeche.Verify.Subst
public section

/-!
# The P declaration fold, and the capstone (task #161, P4)

`foldPM` carries `EnvModelOk` — the P invariant plus the η-family
closure — through an accepted stream, and `no_proof_of_Empty_pure` is
the capstone, with input-level hypotheses only.

The η half of the fold invariant is `declEtaStepRun`
(`Semantics/DeclEta.lean`), model-free at every kind: no install
obligation is consulted for it.  Every tier step is discharged
(`axiomStepPB_of`, `basisStepPB_of`, `declBlock`); the only hypothesis
is `hμ`.
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

/-- The axiom kind's whole step, discharged by `axiomStepPB_of` below. -/
def AxiomStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  -- the relation premise is the run projection (`DeclAxiomRun`), which
  -- names no valuation; the carrier is the invariant the branches consume
  ∀ {F : Nat} {env : Env} (mp : EnvModelM V μ env)
    {cv : ConstantVal} {env₂ : Env},
    DeclAxiomRun μ F env cv env₂ →
    CoverStep mp env₂

/-- **`AxiomStepPB`, discharged.**  All four `DeclAxiomRun` branches:
the two standard axioms (`axiomStd`), `Lean.trustCompiler`
(`axiomTrustCompiler`), `ofReduceNat`/`ofReduceBool` (`axiomOfReduce`,
on the `ReduceOps` field), and the tolerated skip (`axiomSkip`, which
stores nothing). -/
theorem axiomStepPB_of (hμ : μ.isVerified = true) : AxiomStepPB V μ := by
  intro _F _env mp _cv _env₂ hR
  -- the `Quot.sound` arm (task #293) installs nothing
  rcases hR with ⟨-, rfl⟩ | hR
  · exact CoverTo.refl mp []
  obtain ⟨type', hcv, hbranch⟩ := hR
  rcases hbranch with ⟨hok, rfl⟩ | ⟨hname, hok, rfl⟩ |
    ⟨hor, hok, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · exact axiomStd hμ mp hcv hok
  · exact axiomTrustCompiler hμ mp hcv hname hok
  · exact axiomOfReduce hμ mp hcv hor hok
  · exact axiomSkip mp

/-- The basis kind's whole step, routed (basis tier). -/
def BasisStepPB (V : Type w) [SetTheory V] (μ : CheckMode) : Prop :=
  ∀ {env : Env} (mp : EnvModelM V μ env)
    {kind : ConLeche.BasisKind} {env₂ : Env},
      DeclBasisRun env kind env₂ →
      CoverStep mp env₂

/-- **`BasisStepPB`, discharged**: all pinned basis blocks install at
the P tier.  `quotK` is the one branch whose
`DeclBasisRun` guard is not vacuous: it needs `Eq` in the prefix, which
is what the block's `Eq` bridge consumes. -/
theorem basisStepPB_of : BasisStepPB V μ := by
  intro env mp kind env₂ h
  obtain ⟨hEq, hchain⟩ := h
  cases kind with
  | eqK => exact declBasisPB_eqK mp hchain
  | natK => exact declBasisPB_natK mp hchain
  | emptyK => exact declBasisPB_emptyK mp hchain
  | falseK => exact declBasisPB_falseK mp hchain
  | quotK => exact declBasisPB_quotK mp (hEq rfl) hchain

/-! ## Coverage through the fold

Every step concludes `CoverStep` (`Model/Cover.lean`): a carrier at its
result to which coverage (`LfpCover mp []`) carries.  The inductive
step is the uniform install (`declBlock`, every recognised block, nested
ones included); a block the recogniser does not read never
installs (`checkShapeless` declines), so there is no other inductive
step and coverage is unconditional. -/

/-- A step's carrier, covered, from a covered input. -/
theorem CoverTo.covered {env env' : Env} {mp : EnvModelM V μ env}
    (h : CoverStep mp env') (hcov : LfpCover mp []) :
    ∃ mp' : EnvModelM V μ env', LfpCover mp' [] :=
  h.elim fun mp' h' => ⟨mp', h'.2 hcov⟩

/-- A step's carrier, covered and agreeing with the input. -/
theorem CoverTo.coveredA {env env' : Env} {mp : EnvModelM V μ env}
    (h : CoverStep mp env') (hcov : LfpCover mp []) :
    ∃ mp' : EnvModelM V μ env', Agrees mp mp' ∧ LfpCover mp' [] :=
  h.elim fun mp' h' => ⟨mp', h'.1, h'.2 hcov⟩

/-- **The P fold invariant**: a covered P carrier plus the η-family
closure. -/
@[expose] def EnvModelOk (V : Type w) [SetTheory V] (μ : CheckMode) (env : Env) :
    Prop :=
  (∃ mp : EnvModelM V μ env, LfpCover mp []) ∧ EtaFamiliesClosed env

/-- The invariant's carrier. -/
theorem EnvModelOk.nonempty {env : Env} (h : EnvModelOk V μ env) :
    Nonempty (EnvModelM V μ env) :=
  h.1.elim fun mp _ => ⟨mp⟩

/-- The invariant at the empty environment. -/
theorem EnvModelOk.empty : EnvModelOk V μ Env.empty :=
  ⟨⟨EnvModelM.empty V μ, lfpCover_empty⟩, EtaFamiliesClosed.empty⟩

/-- **What a step says of its proof's leaf**: a theorem's leaf is the
canonical proof, and so is a definition's or opaque constant's whose type
the checker finds to be a proposition, at a name with no fast path. -/
@[expose] def DeclProofLeaf (μ : CheckMode) (env : Env) :
    Declaration → (Name → (Name → Nat) → Term) → Prop
  | .thmDecl cv _, acval => acval cv.name = fun _ => .prf
  | .defnDecl cv _ _, acval =>
    (ConLeche.natOpNames.contains cv.name || ConLeche.natDivModNames.contains cv.name) = false ∧
      PropTypeRun μ env cv.type → acval cv.name = fun _ => .prf
  | .opaqueDecl cv _, acval =>
    ConLeche.reduceOpNames.contains cv.name = false ∧ PropTypeRun μ env cv.type →
      acval cv.name = fun _ => .prf
  | _, _ => True

/-- **The per-declaration P step, by dispatch, keeping the input's
leaves.**  The premise is the RUN record (`DeclRun`, valuation-free; the
`ind` kind arrives through its `Ind` parameter), so this step consumes
exactly what it reads. -/
theorem declStep_agrees (hμ : μ.isVerified = true)
    {F : Nat} {env env₂ : Env} {d : Declaration}
    (mp : EnvModelM V μ env) (hcov : LfpCover mp [])
    (hE : EtaFamiliesClosed env)
    (hrun : DeclRun μ F (ConLeche.Semantics.DeclIndRunDispatchK μ F env)
      env d env₂) :
    ∃ mp' : EnvModelM V μ env₂, Agrees mp mp' ∧ LfpCover mp' [] ∧
      DeclProofLeaf μ env d mp'.base2.acval := by
  have triv : ∀ {e : Env}, (∃ mp' : EnvModelM V μ e, Agrees mp mp' ∧ LfpCover mp' []) →
      ∀ {d' : Declaration}, (∀ a, DeclProofLeaf μ env d' a) →
      ∃ mp' : EnvModelM V μ e, Agrees mp mp' ∧ LfpCover mp' [] ∧
        DeclProofLeaf μ env d' mp'.base2.acval :=
    fun h _ hp => h.elim fun mp' h' => ⟨mp', h'.1, h'.2, hp _⟩
  cases d with
  | defnDecl cv value hint =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hsh
    subst henv2
    obtain ⟨mp', hag, hleaf, hc⟩ := harvestDefn hμ mp hrun
    exact ⟨mp', hag, hc hcov, hleaf⟩
  | thmDecl cv value =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, -, henv2⟩ := hsh
    subst henv2
    obtain ⟨mp', hag, hleaf, hc⟩ := harvestThm hμ mp hrun
    exact ⟨mp', hag, hc hcov, hleaf trivial⟩
  | opaqueDecl cv value =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -⟩ := hsh
    subst henv2
    obtain ⟨mp', hag, hleaf, hc⟩ := harvestOpaque hμ mp hrun
    exact ⟨mp', hag, hc hcov, hleaf⟩
  | axiomDecl cv => exact triv ((axiomStepPB_of hμ mp hrun).coveredA hcov) fun _ => trivial
  | basisDecl kind => exact triv ((basisStepPB_of mp hrun).coveredA hcov) fun _ => trivial
  | quotDecl k cv =>
    -- task #293: the quotient package's `type` record installs the
    -- pinned block; its other records install nothing
    cases k with
    | type => exact triv ((basisStepPB_of mp hrun).coveredA hcov) fun _ => trivial
    | _ =>
      exact triv ((CoverTo.of_eq (show env₂ = env from hrun)).coveredA hcov) fun _ => trivial
  | indDecl block nP =>
    -- task #293: a block the fold recognises as one of the five pinned
    -- ones installs the PIN; everything else takes the `.indDecl`
    -- dispatch
    simp only [ConLeche.Semantics.DeclRun] at hrun
    split at hrun
    · exact triv ((basisStepPB_of mp hrun).coveredA hcov) fun _ => trivial
    · have hrun' : ConLeche.Semantics.DeclIndRunDispatchK μ F env block nP env₂ := hrun
      unfold ConLeche.Semantics.DeclIndRunDispatchK at hrun'
      cases hdf : ConLeche.blockParts? nP block with
      | some p =>
        rw [hdf] at hrun'
        -- the uniform install, at any number of members, nested blocks
        -- included (`declBlock`)
        exact triv (declBlock hμ mp hE hdf hrun' hcov) fun _ => trivial
      | none =>
        -- a block the recogniser does not read never installs
        rw [hdf] at hrun'
        exact hrun'.elim

/-- **The per-declaration P step**: `declStep_agrees`, with the η half
(`declEtaStepRun`, model-free at every kind; at `.indDecl` through the
dispatch's own case split, `declIndRunDispatchKEtaClosed`). -/
theorem declStep_preserves (hμ : μ.isVerified = true)
    {F : Nat} {env env₂ : Env} {d : Declaration}
    (mp : EnvModelM V μ env) (hcov : LfpCover mp [])
    (hE : EtaFamiliesClosed env)
    (hrun : DeclRun μ F (ConLeche.Semantics.DeclIndRunDispatchK μ F env)
      env d env₂) :
    EnvModelOk V μ env₂ :=
  ⟨(declStep_agrees hμ mp hcov hE hrun).elim fun mp' h => ⟨mp', h.2.1⟩,
    ConLeche.Semantics.declEtaStepRun
      (fun h' => ConLeche.Semantics.declIndRunDispatchKEtaClosed hE h') hE hrun⟩

/-- **The P fold**: the declaration fold's recursion at the P invariant. -/
theorem foldPM (hμ : μ.isVerified = true) {F : Nat} :
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
      obtain ⟨⟨mp, hcov⟩, hE⟩ := hm
      exact foldPM hμ ds env1
        (declStep_preserves hμ mp hcov hE
          -- **the RUN bridge, from the P carrier's own `EnvFacts`**
          -- (`checkDeclRun_ofEnvFactsK`; the `ind` kind through
          -- `DeclIndRunDispatchK`)
          (ConLeche.Semantics.checkDeclRun_ofEnvFactsK hd)) h

/-- **The acceptance theorem, P route.** -/
theorem checkDeclsPure_sound_of (hμ : μ.isVerified = true)
    {F : Nat} {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
    Nonempty (EnvModelM V μ env') :=
  (foldPM hμ ds Env.empty EnvModelOk.empty h).nonempty

/-- **The capstone, carrier form**: no proof of `Empty` is ever
accepted. -/
theorem no_proof_of_Empty_pure_of (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.isVerified = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨mp⟩ := checkDeclsPure_sound_of (V := V) hμ h
  exact no_constant_of_Empty mp c hc hty

/-- **THE CAPSTONE** (`Model/Capstone.lean`'s docstring): *the checker,
running in a validating mode, never accepts a declaration stream in
which some stored constant has type `Empty`.*

Hypotheses are **input-level only** — the accepted run, the stored
constant, its type, plus the validating mode, which is part of the
goal's letter (the checker the model covers *is* the verified mode;
`--trusted` omits the certification-only work by design).  No
residue: every tier step is discharged (`axiomStepPB_of`, `basisStepPB_of`, `declBlock`).

`SetTheory V` is the standing parametricity of the consistency
argument (project rule: consistency proofs stay parametric in the
`SetTheory` interface), not a hypothesis about the input. -/
theorem no_proof_of_Empty_pure (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.isVerified = true) {F : Nat}
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
    {μ : CheckMode} (hμ : μ.isVerified = true) {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure μ (fueledOps μ F) pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := checkDeclsPure_sound_of (V := V) hμ h
  exact fun c hc hty => no_constant_of_False mp c hc hty

end ConLeche.Model
