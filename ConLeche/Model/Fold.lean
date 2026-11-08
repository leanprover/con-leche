module

import ConLeche.Model.AxiomReduce
import ConLeche.Model.Inductives.StructEntryKit
public import ConLeche.Semantics.Bridge.Sound
import ConLeche.Verify.BasisBlock
import ConLeche.Verify.Inductives.BlockShapeInv
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
    DeclAxiomRun F env cv env₂ → ConLeche.basisNamesOk (.axiomDecl cv) = true →
    CoverStep mp env₂

/-- **`AxiomStepPB`, discharged.**  All four `DeclAxiomRun` branches:
the two standard axioms (`axiomStd`), `Lean.trustCompiler`
(`axiomTrustCompiler`), `ofReduceNat`/`ofReduceBool` (`axiomOfReduce`,
on the `ReduceOps` field), and the tolerated skip (`axiomSkip`, which
stores nothing). -/
theorem axiomStepPB_of : AxiomStepPB V := by
  intro _F _env mp _cv _env₂ hR hb
  -- the `Quot.sound` arm is a quotient record
  rcases hR with ⟨-, hq⟩ | ⟨hqs, hR⟩
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
ones included); a block `readBlock` cannot read never installs
(its error is the check's), so there is no other inductive
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
    (h : DeclAxiomRun F env cv env₂) (hb : ConLeche.basisNamesOk (.axiomDecl cv) = true) :
    PlainStep env env₂ := by
  rcases h with ⟨-, hq⟩ | ⟨hqs, type', -, hcv, hbranch⟩
  · exact plainStep_quot hq
  · -- off `Quot.sound`, the reserved names' check leaves an unreserved name
    have hres : ConLeche.reservedBasisNames.contains cv.name = false := by
      simpa [ConLeche.basisNamesOk, hqs] using hb
    rcases hbranch with ⟨-, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, rfl⟩ | ⟨-, -, -, -, -, -, -, rfl⟩
    · exact PlainStep.cons hres
    · exact PlainStep.cons hres
    · exact PlainStep.cons hres
    · exact ⟨[], rfl, rfl, fun _ hc => nomatch hc⟩

/-- **Constants pushed under distinct fresh names** are pushed one by one, each fresh. -/
theorem basisInstallRun_of_push :
    ∀ {L : List ConstantInfo} {env : Env}, (L.map (·.name)).Nodup →
      (∀ n ∈ L.map (·.name), env.find? n = none) →
      BasisInstallRun env L (env.pushDelta L [])
  | [], env, _, _ => by simp [BasisInstallRun, ConLeche.Env.pushDelta]
  | ci :: rest, env, hnd, hfr => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    refine ⟨Option.isNone_iff_eq_none.mpr (hfr _ List.mem_cons_self), ?_⟩
    have h := basisInstallRun_of_push (env := ⟨ci :: env.consts, env.tables⟩) hnd.2
      fun n hn => by
        rw [ConLeche.Env.find?_cons, ite_eq_right fun he => ?_]
        · exact hfr n (List.mem_cons_of_mem _ hn)
        · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hn
          exact hnd.1 c hc he.symm
    simpa [ConLeche.Env.pushDelta] using h

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
theorem storedAt_names :
    ∀ (pins block : List ConstantInfo), pins.length = block.length →
      (List.zipWith (fun pin c => pin.atLps c.toConstantVal.levelParams) pins block).map (·.name)
        = pins.map (·.name)
  | [], _, _ => rfl
  | _ :: _, [], h => nomatch h
  | p :: ps, b :: bs, h => by
    simp only [List.length_cons, Nat.add_right_cancel_iff] at h
    simp only [List.zipWith_cons_cons, List.map_cons, atLps_name]
    rw [storedAt_names ps bs h]

/-- **A pinned block keeps `Nat`'s block whole.** -/
private theorem natFacts_basis {env env₂ : Env} {kind : ConLeche.BasisKind} {block : List ConstantInfo}
    (hN : NatFacts env) (hk : ConLeche.basisNameHit block = some kind)
    (h : BasisInstallRun env (kind.storedAt block) env₂) : NatFacts env₂ := by
  obtain ⟨hc, -⟩ := basisInstallRun_consts h
  have hn : kind.decls.map (·.name) = block.map (·.name) := by
    have := List.find?_some hk
    simpa using this
  have hlen : kind.installed.length = block.length := by
    have := congrArg List.length hn
    simp only [List.length_map] at this
    rw [← this]
    cases kind <;> rfl
  have hnames' : (kind.storedAt block).map (·.name) = kind.installed.map (·.name) :=
    storedAt_names kind.installed block hlen
  have hmem : ∀ c ∈ (kind.storedAt block).reverse, c.name ∈ kind.installed.map (·.name) := by
    intro c hc'
    rw [← hnames']
    exact List.mem_map.mpr ⟨c, List.mem_reverse.mp hc', rfl⟩
  have hfound : ∀ n, n ∈ kind.installed.map (·.name) → (env₂.find? n).isSome = true := by
    intro n hn'
    rw [← hnames'] at hn'
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hn'
    show (env₂.consts.find? (·.name == c.name)).isSome = true
    rw [List.find?_isSome]
    exact ⟨c, by rw [hc]; exact List.mem_append_left _ (List.mem_reverse.mpr hcm), by simp⟩
  have hnew : ∀ c ∈ (kind.storedAt block).reverse, kind ≠ .natK →
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

/-- **A pinned block's install, as the model reads it**: the installed pins at the record's names,
each under a fresh name, and no table (`blockInstall_pinned`). -/
private theorem basisInstallRun_of_block {F : Nat} {env env₂ : Env} {block : List ConstantInfo}
    {nP : Nat} {kind : ConLeche.BasisKind} {p : ConLeche.BlockShape}
    (hk : ConLeche.basisNameHit block = some kind)
    (hok : ConLeche.pinListOk block kind.decls = true)
    (hdf : ConLeche.readBlock nP block = .ok p) (hrun : BlockRun F env block p env₂) :
    BasisInstallRun env (kind.storedAt block) env₂ := by
  have hd := ConLeche.readBlock_declared hdf
  obtain ⟨hC, hT⟩ := ConLeche.blockInstall_pinned hk hok hdf
  have henv := blockRun_env hd hrun
  have hfr := blockRun_fresh hd hrun
  rw [hC, hT] at henv
  rw [hC] at hfr
  subst henv
  have hn : kind.decls.map (·.name) = block.map (·.name) := by
    have := List.find?_some hk
    simpa using this
  have hlen : kind.installed.length = block.length := by
    have := congrArg List.length hn
    simp only [List.length_map] at this
    rw [← this]
    cases kind <;> rfl
  refine basisInstallRun_of_push ?_ hfr
  rw [show (kind.storedAt block).map (·.name) = kind.installed.map (·.name) from
    storedAt_names kind.installed block hlen]
  have hq : kind ≠ .quotK := by
    rintro rfl
    have hm := List.mem_of_find?_eq_some hk
    simp at hm
  cases kind <;> first | exact absurd rfl hq | decide

/-- **The reserved names' check at a block no pinned one's**: its records' names are unreserved. -/
theorem unreserved_of_basisNamesOk {block : List ConstantInfo} {nP : Nat}
    (hb : ConLeche.basisNamesOk (.indDecl block nP) = true)
    (hk : ConLeche.basisNameHit block = none) :
    ∀ c ∈ block, ConLeche.reservedBasisNames.contains c.name = false := by
  simp only [ConLeche.basisNamesOk, hk, List.all_eq_true, Bool.not_eq_eq_eq_not,
    Bool.not_true] at hb
  exact hb

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
  obtain ⟨hnames, hrun⟩ := hrun
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
    have hnres : ConLeche.reservedBasisNames.contains cv.name = false := by
      simpa [ConLeche.basisNamesOk] using hnames
    have hsh := hrun
    obtain ⟨type', value', hcv, -, henv2, -, -⟩ := hsh
    subst henv2
    exact PlainStep.close (PlainStep.cons hnres) (harvestDefn mp hrun hnres) hcov hS hN
  | thmDecl cv value =>
    have hnres : ConLeche.reservedBasisNames.contains cv.name = false := by
      simpa [ConLeche.basisNamesOk] using hnames
    have hsh := hrun
    -- the run record has no is-a-proposition derivation row
    obtain ⟨-, type', value', hcv, -, -, henv2⟩ := hsh
    subst henv2
    exact PlainStep.close (PlainStep.cons hnres) (harvestThm mp hrun hnres) hcov hS hN
  | opaqueDecl cv value =>
    have hnres : ConLeche.reservedBasisNames.contains cv.name = false := by
      simpa [ConLeche.basisNamesOk] using hnames
    have hsh := hrun
    obtain ⟨-, type', value', hcv, -, henv2, -⟩ := hsh
    subst henv2
    exact PlainStep.close (PlainStep.cons hnres) (harvestOpaque mp hrun hnres) hcov hS hN
  | axiomDecl cv =>
    exact (plainStep_axiom hrun hnames).close (axiomStepPB_of mp hrun hnames) hcov hS hN
  | quotDecl k cv => exact (plainStep_quot hrun).close (declQuotPB_at mp hrun) hcov hS hN
  | indDecl block nP =>
    have hrun' : ConLeche.Semantics.DeclIndRunDispatchK F env block nP env₂ := hrun
    unfold ConLeche.Semantics.DeclIndRunDispatchK at hrun'
    cases hdf : ConLeche.readBlock nP block with
    | error _ =>
      -- a block `readBlock` cannot read never installs
      rw [hdf] at hrun'
      exact hrun'.elim
    | ok p =>
      rw [hdf] at hrun'
      cases hk : ConLeche.basisNameHit block with
      | some kind =>
        -- a pinned block: its install is the installed pins at the record's names
        have hok : ConLeche.pinListOk block kind.decls = true := by
          simpa [ConLeche.basisNamesOk, hk] using hnames
        have hnq : kind ≠ .quotK := by
          rintro rfl
          have hm := List.mem_of_find?_eq_some hk
          simp at hm
        have hinst := basisInstallRun_of_block hk hok hdf hrun'
        obtain ⟨hc, htb⟩ := basisInstallRun_consts hinst
        exact ⟨(declBasisPB_at mp hnq hok hinst).covered hcov hS (findTable_of_added hc htb),
          natFacts_basis hN hk hinst⟩
      | none =>
        -- the uniform install, at any number of members, nested blocks included
        exact declBlock mp hE hdf (unreserved_of_basisNamesOk hnames hk) hrun' hcov hS hN

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
