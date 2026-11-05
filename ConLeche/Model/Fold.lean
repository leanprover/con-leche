module

import ConLeche.Model.AxiomReduce
import ConLeche.Model.Inductives.StructEntryKit
public import ConLeche.Semantics.Bridge.Sound
import ConLeche.Model.Cover
public import ConLeche.Model.Inductives.BlockRunFacts
import ConLeche.Kernel.Checker
import ConLeche.Kernel.CheckerBase
import ConLeche.Model.Reading.Levels
import ConLeche.Verify.Denote.ErasedEq
import ConLeche.Model.Capstone
import ConLeche.Model.IndCons
import ConLeche.Model.BasisAtBlock
import ConLeche.Model.Swap
import ConLeche.Semantics.DeclRun
import ConLeche.Semantics.EnvFacts
import ConLeche.Semantics.DeclEta
import ConLeche.Semantics.Inductives.DeclBlockEta
import ConLeche.Verify.Abstract
import ConLeche.Verify.Denote.EnvExt
import ConLeche.Verify.Denote
import ConLeche.Verify.EnvWF
import ConLeche.Verify.Extend.Inversions
import ConLeche.Verify.Inductives.NestedRead
import ConLeche.Verify.Shift
public section

/-!
# The P declaration fold, and the capstone (task #161, P4)

`foldPM` carries `EnvModelOk` — the P invariant plus the η-family
closure — through an accepted stream, and `no_proof_of_Empty_pure` is
the capstone, with input-level hypotheses only.

The η half of the fold invariant is `declEtaStepRun`
(`Semantics/DeclEta.lean`), model-free at every kind: no install
obligation is consulted for it.  Every tier step is discharged
(`axiomStepPB_of`, `declBasisPB_at`, `declQuotPB_at`, `declBlock`); the fold carries no
hypothesis about the mode: the model tier is at `.verified`.
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
variable {pins : List ConLeche.NatOpPinSet}

/-- The axiom kind's whole step, discharged by `axiomStepPB_of` below. -/
def AxiomStepPB (V : Type w) [SetTheory V] : Prop :=
  -- the relation premise is the run projection (`DeclAxiomRun`), which
  -- names no valuation; the carrier is the invariant the branches consume
  ∀ {F : Nat} {env : Env} (mp : EnvModelM V env)
    {cv : ConstantVal} {env₂ : Env},
    DeclAxiomRun F env cv env₂ →
    CoverStep mp env₂

/-- **`AxiomStepPB`, discharged.**  All four `DeclAxiomRun` branches:
the two standard axioms (`axiomStd`), `Lean.trustCompiler`
(`axiomTrustCompiler`), `ofReduceNat`/`ofReduceBool` (`axiomOfReduce`,
on the `ReduceOps` field), and the tolerated skip (`axiomSkip`, which
stores nothing). -/
theorem axiomStepPB_of : AxiomStepPB V := by
  intro _F _env mp _cv _env₂ hR
  -- the `Quot.sound` arm is a quotient record
  rcases hR with ⟨-, hq⟩ | hR
  · exact declQuotPB_at mp hq
  obtain ⟨type', hopn, hcv, hbranch⟩ := hR
  rcases hbranch with ⟨hok, rfl⟩ | ⟨hname, hok, rfl⟩ |
    ⟨hor, hok, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
  · exact axiomStd mp hopn hcv hok
  · exact axiomTrustCompiler mp hopn hcv hname hok
  · exact axiomOfReduce mp hopn hcv hor hok
  · exact axiomSkip mp

/-! ## Coverage through the fold

Every step concludes `CoverStep` (`Model/Cover.lean`): a carrier at its
result to which coverage (`LfpCover mp []`) carries.  The inductive
step is the uniform install (`declBlock`, every recognised block, nested
ones included); a block the recogniser does not read never
installs (`checkShapeless` declines), so there is no other inductive
step and coverage is unconditional. -/

/-- A step's carrier, covered, from a covered input. -/
theorem CoverTo.covered {env env' : Env} {mp : EnvModelM V env}
    (h : CoverStep mp env') (hcov : LfpCover mp []) (hS : FamilyRan mp)
    (htb : ∀ T, (env.find? T).isSome = true → env'.findTable? T = env.findTable? T) :
    ∃ mp' : EnvModelM V env', LfpCover mp' [] ∧ FamilyRan mp' :=
  h.elim fun mp' h' => ⟨mp', h'.2 hcov, hS.step h'.1 htb⟩

/-- **The P fold invariant**: a covered P carrier plus the η-family
closure. -/
@[expose] def EnvModelOk (V : Type w) [SetTheory V] (env : Env) :
    Prop :=
  (∃ mp : EnvModelM V env, LfpCover mp [] ∧ FamilyRan mp) ∧ EtaFamiliesClosed env ∧ NatFacts env

/-- The invariant's carrier. -/
theorem EnvModelOk.nonempty {env : Env} (h : EnvModelOk V env) :
    Nonempty (EnvModelM V env) :=
  h.1.elim fun mp _ => ⟨mp⟩

/-- The invariant at the empty environment. -/
theorem EnvModelOk.empty : EnvModelOk V Env.empty :=
  ⟨⟨EnvModelM.empty V, lfpCover_empty, fun _ hD => nomatch hD⟩, EtaFamiliesClosed.empty,
    ⟨fun h => by rcases h with h | h | h <;> exact nomatch h⟩⟩

/-- A step that adds constants, none of `Nat`'s block's, and no table. -/
@[expose] def PlainStep (env env₂ : Env) : Prop :=
  ∃ new : List ConstantInfo, env₂.consts = new ++ env.consts ∧ env₂.tables = env.tables ∧
    ∀ c ∈ new, c.name ≠ ConLeche.natName ∧ c.name ≠ ConLeche.natZeroName ∧
      c.name ≠ ConLeche.natSuccName

/-- A plain step keeps the two fold-level facts. -/
theorem PlainStep.close {env env₂ : Env} {mp : EnvModelM V env} (h : PlainStep env env₂)
    (hstep : CoverStep mp env₂) (hcov : LfpCover mp []) (hS : FamilyRan mp) (hN : NatFacts env) :
    (∃ mp' : EnvModelM V env₂, LfpCover mp' [] ∧ FamilyRan mp') ∧ NatFacts env₂ := by
  obtain ⟨new, hnew, htab, hres⟩ := h
  exact ⟨hstep.covered hcov hS (findTable_of_added hnew htab), hN.append hnew hres⟩

/-- A declaration's constant, stored under an unreserved name. -/
theorem PlainStep.cons {env : Env} {c : ConstantInfo}
    (h : ConLeche.reservedBasisNames.contains c.name = false) :
    PlainStep env ⟨c :: env.consts, env.tables⟩ :=
  ⟨[c], rfl, rfl, fun _ hc => by
    rw [List.mem_singleton.mp hc]; exact nat_names_of_unreserved h⟩

/-- A quotient record is a plain step. -/
theorem plainStep_quot {env env₂ : Env} {k : ConLeche.QuotKind} {cv : ConstantVal}
    (h : DeclQuotRun env k cv env₂) : PlainStep env env₂ := by
  obtain ⟨-, -, -, rfl⟩ := h
  refine ⟨[_], rfl, rfl, fun _ hc => ?_⟩
  rw [List.mem_singleton.mp hc, show (quotAt k cv).name = (quotPin k).name from atLps_name _ _]
  cases k <;> decide

/-- An axiom record is a plain step. -/
theorem plainStep_axiom {F : Nat} {env env₂ : Env} {cv : ConstantVal}
    (h : DeclAxiomRun F env cv env₂) : PlainStep env env₂ := by
  rcases h with ⟨-, hq⟩ | ⟨type', -, hcv, hbranch⟩
  · exact plainStep_quot hq
  · have hres := hcv.2.1
    rcases hbranch with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
    · exact PlainStep.cons hres
    · exact PlainStep.cons hres
    · exact PlainStep.cons hres
    · exact ⟨[], rfl, rfl, fun _ hc => nomatch hc⟩

/-- What a pinned block stores, as a prefix of the constants. -/
theorem basisInstallRun_consts :
    ∀ {L : List ConstantInfo} {env env₂ : Env}, BasisInstallRun env L env₂ →
      env₂.consts = L.reverse ++ env.consts ∧ env₂.tables = env.tables
  | [], _, _, h => by
    obtain rfl := h
    exact ⟨rfl, rfl⟩
  | ci :: rest, _, _, h => by
    obtain ⟨hc, ht⟩ := basisInstallRun_consts h.2
    refine ⟨?_, ht⟩
    rw [hc]
    simp

/-- A pinned block's stored names are the pin's. -/
theorem atBlock_names :
    ∀ (pins block : List ConstantInfo), pins.map (·.name) = block.map (·.name) →
      (List.zipWith (fun pin c => pin.atLps c.toConstantVal.levelParams) pins block).map (·.name)
        = pins.map (·.name)
  | [], _, _ => rfl
  | _ :: _, [], h => nomatch h
  | p :: ps, b :: bs, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    simp only [List.zipWith_cons_cons, List.map_cons, atLps_name]
    rw [atBlock_names ps bs h.2]

/-- **A pinned block keeps `Nat`'s block whole.** -/
theorem natFacts_basis {env env₂ : Env} {kind : ConLeche.BasisKind} {block : List ConstantInfo}
    (hN : NatFacts env) (hk : ConLeche.basisNameHit block = some kind)
    (h : BasisInstallRun env (kind.atBlock block) env₂) : NatFacts env₂ := by
  obtain ⟨hc, -⟩ := basisInstallRun_consts h
  have hn : kind.decls.map (·.name) = block.map (·.name) := by
    have := List.find?_some hk
    simpa using this
  have hnames := atBlock_names kind.decls block hn
  have hnames' : (kind.atBlock block).map (·.name) = kind.decls.map (·.name) := hnames
  have hmem : ∀ c ∈ (kind.atBlock block).reverse, c.name ∈ kind.decls.map (·.name) := by
    intro c hc'
    rw [← hnames']
    exact List.mem_map.mpr ⟨c, List.mem_reverse.mp hc', rfl⟩
  have hfound : ∀ n, n ∈ kind.decls.map (·.name) → (env₂.find? n).isSome = true := by
    intro n hn'
    rw [← hnames'] at hn'
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hn'
    show (env₂.consts.find? (·.name == c.name)).isSome = true
    rw [List.find?_isSome]
    exact ⟨c, by rw [hc]; exact List.mem_append_left _ (List.mem_reverse.mpr hcm), by simp⟩
  have hnew : ∀ c ∈ (kind.atBlock block).reverse, kind ≠ .natK →
      c.name ≠ ConLeche.natName ∧ c.name ≠ ConLeche.natZeroName ∧ c.name ≠ ConLeche.natSuccName := by
    intro c hc' hne
    have hm := hmem c hc'
    cases kind with
    | natK => exact absurd rfl hne
    | eqK | emptyK | falseK | quotK =>
      revert hm
      generalize c.name = n
      intro hm
      refine ⟨?_, ?_, ?_⟩ <;> (rintro rfl; revert hm; decide)
  by_cases hnat : kind = .natK
  · subst hnat
    exact ⟨fun _ => ⟨hfound _ (by decide), hfound _ (by decide), hfound _ (by decide)⟩⟩
  · exact hN.append hc fun c hc' => hnew c hc' hnat


/-- **The per-declaration P step, by dispatch.**  The premise is the
RUN record (`DeclRun`, valuation-free; the `ind` kind arrives through
its `Ind` parameter), so this step consumes exactly what it reads. -/
theorem declStep_preserves
    {F : Nat} {env env₂ : Env} {d : Declaration}
    (mp : EnvModelM V env) (hcov : LfpCover mp []) (hS : FamilyRan mp)
    (hE : EtaFamiliesClosed env) (hN : NatFacts env)
    (hrun : DeclRun F (ConLeche.Semantics.DeclIndRunDispatchK F env)
      env d env₂) :
    EnvModelOk V env₂ := by
  -- the η half: `declEtaStepRun`, model-free at every kind; at `.indDecl`
  -- through the dispatch's own case split
  have hEta : EtaFamiliesClosed env₂ := ConLeche.Semantics.declEtaStepRun (fun h' => by
    unfold ConLeche.Semantics.DeclIndRunDispatchK at h'
    split at h'
    · exact ConLeche.Semantics.blockRun_etaClosed hE h'
    · exact h'.elim) hE hrun
  suffices h : (∃ mp' : EnvModelM V env₂, LfpCover mp' [] ∧ FamilyRan mp') ∧ NatFacts env₂ from
    ⟨h.1, hEta, h.2⟩
  cases d with
  | defnDecl cv value hint =>
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hsh
    subst henv2
    exact PlainStep.close (PlainStep.cons (by exact hcv.2.1)) (harvestDefn mp hrun) hcov hS hN
  | thmDecl cv value =>
    have hsh := hrun
    -- the run record has no is-a-proposition derivation row
    obtain ⟨-, type', value', hcv, -, -, henv2⟩ := hsh
    subst henv2
    exact PlainStep.close (PlainStep.cons (by exact hcv.2.1)) (harvestThm mp hrun) hcov hS hN
  | opaqueDecl cv value =>
    have hsh := hrun
    obtain ⟨-, type', value', hcv, -, henv2, -⟩ := hsh
    subst henv2
    exact PlainStep.close (PlainStep.cons (by exact hcv.2.1)) (harvestOpaque mp hrun) hcov hS hN
  | axiomDecl cv => exact (plainStep_axiom hrun).close (axiomStepPB_of mp hrun) hcov hS hN
  | quotDecl k cv => exact (plainStep_quot hrun).close (declQuotPB_at mp hrun) hcov hS hN
  | indDecl block nP =>
    -- a block with a pinned block's names installs the pin at the record's
    -- names; everything else takes the `.indDecl` dispatch
    simp only [ConLeche.Semantics.DeclRun] at hrun
    split at hrun
    · next kind hk =>
      have hnq : kind ≠ .quotK := by
        rintro rfl
        have hm := List.mem_of_find?_eq_some hk
        simp at hm
      obtain ⟨hc, htb⟩ := basisInstallRun_consts hrun.2
      exact ⟨(declBasisPB_at mp hnq hrun).covered hcov hS (findTable_of_added hc htb),
        natFacts_basis hN hk hrun.2⟩
    · have hrun' : ConLeche.Semantics.DeclIndRunDispatchK F env block nP env₂ := hrun
      unfold ConLeche.Semantics.DeclIndRunDispatchK at hrun'
      cases hdf : ConLeche.blockParts? nP block with
      | some p =>
        rw [hdf] at hrun'
        -- the uniform install, at any number of members, nested blocks included
        exact declBlock mp hE hdf hrun' hcov hS hN
      | none =>
        -- a block the recogniser does not read never installs
        rw [hdf] at hrun'
        exact hrun'.elim

/-- **The P fold**: the declaration fold's recursion at the P invariant. -/
theorem foldPM {F : Nat} :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvModelOk V env →
      ds.foldlM (checkDecl .verified (fueledOps .verified F) pins) env = .ok env' →
      EnvModelOk V env'
  | [], _, _, hm, h => by
    simp only [List.foldlM, pure, Except.pure, Except.ok.injEq] at h
    exact h ▸ hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl .verified (fueledOps .verified F) pins env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨mp, hcov, hS⟩, hE, hN⟩ := hm
      exact foldPM ds env1
        (declStep_preserves mp hcov hS hE hN
          -- **the RUN bridge, from the P carrier's own `EnvFacts`**
          -- (`checkDeclRun_ofEnvFactsK`; the `ind` kind through
          -- `DeclIndRunDispatchK`)
          (ConLeche.Semantics.checkDeclRun_ofEnvFactsK hd)) h

/-- **The acceptance theorem, P route.** -/
theorem checkDeclsPure_sound_of
    {F : Nat} {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure .verified (fueledOps .verified F) pins ds = .ok env') :
    Nonempty (EnvModelM V env') :=
  (foldPM ds Env.empty EnvModelOk.empty h).nonempty

/-- **The capstone, carrier form**: no proof of `Empty` is ever
accepted. -/
theorem no_proof_of_Empty_pure_of (V : Type w) [SetTheory V]
    {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure .verified (fueledOps .verified F) pins ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨mp⟩ := checkDeclsPure_sound_of (V := V) h
  exact no_constant_of_Empty mp c hc hty

/-- **THE CAPSTONE** (`Model/Capstone.lean`'s docstring): *the checker,
running in a validating mode, never accepts a declaration stream in
which some stored constant has type `Empty`.*

Hypotheses are **input-level only** — the accepted run, the stored
constant, its type, plus the validating mode, which is part of the
goal's letter (the checker the model covers *is* the verified mode;
`--trusted` omits the certification-only work by design).  No
residue: every tier step is discharged (`axiomStepPB_of`, `declBasisPB_at`, `declQuotPB_at`,
`declBlock`).

`SetTheory V` is the standing parametricity of the consistency
argument (project rule: consistency proofs stay parametric in the
`SetTheory` interface), not a hypothesis about the input. -/
theorem no_proof_of_Empty_pure (V : Type w) [SetTheory V]
    {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure .verified (fueledOps .verified F) pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False :=
  fun c hc hty => no_proof_of_Empty_pure_of V h c hc hty

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
    {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsPure .verified (fueledOps .verified F) pins ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := checkDeclsPure_sound_of (V := V) h
  exact fun c hc hty => no_constant_of_False mp c hc hty

end ConLeche.Model
