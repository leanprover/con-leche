import Setlec.SetP.FoldP
import Setlec.Verify.BridgeWFDecl
import Setlec.Verify.BridgeSDecl
import Setlec.Verify.BridgePDecl
import Setlec.Verify.DeclStores

/-!
# The P route's consistency theorems for the SHIPPED drivers
(task #161, S8 — the SP_P batch, risk-rank 1 of the design review)

`FoldP.lean` closes the P capstone over `checkDecls μ (fueledOps μ F)`
— the *pure* checker.  That is not the function the executable runs.
The design census's **finding 2** named the gap: the P capstone family
had exactly two members, both over `checkDecls`, while the shipped
driver is `checkDeclsSP` (the #64 mode-4 snapshot bracket), covered
only by the collapsed lane's `no_proof_of_Empty_SP_R` and the 2U
lane's `no_proof_of_Empty_SP_R2`.  *"Without them the P mode has no
statement about the shipped driver, and the campaign's deliverable is
a theorem about a function the checker does not run."*

This file is `SetR/Main.lean`'s driver structure re-run at the P
invariant.  Three drivers, three carrier transposes each:

| driver | fold | acceptance | capstone |
|---|---|---|---|
| `checkDecls μ (cachedOps μ)` | `foldPMC` | `checkDeclsC_sound_P` | `no_proof_of_Empty_C_P` |
| `checkDeclsShared μ` | `foldPMS` | `checkDeclsS_sound_P` | `no_proof_of_Empty_S_P` |
| **`checkDeclsSP μ st pds`** | `foldSP_PM` | `checkDeclsSP_sound_P` | **`no_proof_of_Empty_SP_P`** |

**Nothing semantic is added.**  Each fold is `foldPM`'s recursion with
the driver's own step-to-`checkDecl` bridge spliced in — `checkDecl_bridge`
for the cached core, `checkDeclSharedF_bridge` for the shared-state
core, `checkDeclSPStep_run` for the parsed-index core — and each of
those bridges asks for exactly one fact about the environment,
`EnvWF`, which the P carrier supplies through its own projection
(`mp.toEnvR.wf`).  That is the whole content of "the P lane covers the
shipped driver": since S7 the graded carrier builds an `EnvR` without
a collapsed-model round trip, so the driver bridges the R lane already
had apply to it verbatim.

**The statements are frozen the moment they land** (the capstone
letter discipline).  Each is stated against the shipped driver's own
signature and is hypothesis-minimal in the #16 sense: the accepted
run, the stored constant, its type, plus `hμ : μ.verified = true`,
which is `no_proof_of_Empty_P`'s own mode hypothesis and part of the
goal's letter (the annotated checker *is* the verified mode). No tier
bundle, no install obligation, no residue — the milestone-shaped
`_of` forms that `FoldP.lean` keeps beside `no_proof_of_Empty_P` have
no analogue here because there is nothing left for them to carry.

**What is deliberately NOT here, and why** (scope, named rather than
silently dropped): the R lane's four `no_proof_of_Empty_input_*_R`
theorems have no P analogue, because the P lane has never had an
input-level capstone at *any* driver — `FoldP.lean` closes at
`no_proof_of_Empty_P` and stops.  The input forms are a different
argument (`foldlM_no_Empty_R`: the *annotated type of a declared*
`Empty`-typed `def`/`thm` survives the fold), not a carrier transpose,
and building them for P would be a new statement family rather than
this batch's ratified scope.  Recorded as a follow-up.
-/

namespace Setlec.SetR.Interp2

open Setlec.TT Setlec.TTVerify SetTheory EStore
open Setlec.SetR
open Setlec (CheckMode Env Expr Name Level ConstantInfo ConstantVal
  Declaration checkDecl checkDecls checkDeclsShared checkDeclsSP
  checkDeclSharedF checkDeclSPStep fueledOps cachedOps emptyName
  FEnv mkFEnv WFStore DeclP IState EStore)

universe w

variable {V : Type w} [SetTheory V]
variable {μ : CheckMode}

/-! ## The cached executable's core -/

/-- The cached-executable fold, at the P invariant.  `checkDecl_bridge`
supplies, per declaration, a fuel at which the pure checker reproduces
the cached run; everything after that is `foldPM`'s step.  The `EnvWF`
that bridge asks for is the P carrier's own — `mp.toEnvR.wf` — which is
why no collapsed-model carrier appears anywhere in this file. -/
theorem foldPMC (hμ : μ.verified = true) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvSPOk V μ env →
      ds.foldlM (checkDecl μ (cachedOps μ)) env = .ok env' →
      EnvSPOk V μ env'
  | [], env, env', hm, h => by
    have h' : (Except.ok env : CheckM Env) = Except.ok env' := h
    cases h'
    exact hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl μ (cachedOps μ) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨mp⟩, hE⟩ := hm
      obtain ⟨F, hF⟩ := checkDecl_bridge mp.toEnvR.wf hd
      exact foldPMC hμ ds env1
        (declStepPM hμ mp hE
          (Setlec.SetR.checkDeclR_ofEnvRE mp.toEnvR hE hF)) h

/-- **The acceptance theorem for the cached executable checker, P
route.** -/
theorem checkDeclsC_sound_P (hμ : μ.verified = true)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (cachedOps μ) ds = .ok env') :
    Nonempty (EnvS2PM V μ env') :=
  (foldPMC hμ ds Env.empty
    ⟨⟨EnvS2PM.empty V μ⟩, EtaFamiliesClosed.empty⟩ h).1

/-- **No proof of `Empty` is accepted by the cached executable**, on
the P route — `--core=cached`. -/
theorem no_proof_of_Empty_C_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verified = true)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (cachedOps μ) ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := checkDeclsC_sound_P (V := V) hμ h
  exact fun c hc hty => no_constant_of_Empty_P mp c hc hty

/-! ## The shared-state executable's core -/

/-- The shared-state executable's fold, at the P invariant. -/
theorem foldPMS (hμ : μ.verified = true) :
    ∀ (ds : List Declaration) (fe : FEnv) {fe' : FEnv},
      fe = mkFEnv fe.env →
      EnvSPOk V μ fe.env →
      ds.foldlM (checkDeclSharedF μ) fe = .ok fe' →
      EnvSPOk V μ fe'.env
  | [], fe, fe', _, hm, h => by
    have h' : (Except.ok fe : CheckM FEnv) = Except.ok fe' := h
    cases h'
    exact hm
  | d :: ds, fe, fe', hfe, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDeclSharedF μ fe d with
    | error e => rw [hd] at h; exact nomatch h
    | ok fe1 =>
      rw [hd] at h
      obtain ⟨⟨mp⟩, hE⟩ := hm
      rw [hfe] at hd
      obtain ⟨hfe1, F, hF⟩ := checkDeclSharedF_bridge mp.toEnvR.wf hd
      exact foldPMS hμ ds fe1 hfe1
        (declStepPM hμ mp hE
          (Setlec.SetR.checkDeclR_ofEnvRE mp.toEnvR hE hF)) h

/-- **The acceptance theorem for the shared-state executable, P
route.** -/
theorem checkDeclsS_sound_P (hμ : μ.verified = true)
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared μ ds = .ok env') :
    Nonempty (EnvS2PM V μ env') := by
  unfold checkDeclsShared at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : ds.foldlM (checkDeclSharedF μ) (mkFEnv Env.empty) with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    exact (foldPMS hμ ds (mkFEnv Env.empty) rfl
      ⟨⟨EnvS2PM.empty V μ⟩, EtaFamiliesClosed.empty⟩ hf).1

/-- **No proof of `Empty` is accepted by the shared-state
executable**, on the P route — `--core=shared`. -/
theorem no_proof_of_Empty_S_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verified = true)
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared μ ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := checkDeclsS_sound_P (V := V) hμ h
  exact fun c hc hty => no_constant_of_Empty_P mp c hc hty

/-! ## The shipped driver: the parsed-index executable -/

/-- The parsed-index executable's fold, at the P invariant.  The store
invariant's supplier is the bundle: `WFStore.wf` gives `st.raw.WF`
once, and the fold threads `ISOKF`/`Ext` from `checkDeclSPStep_run` —
the same "name the environment each premise is at" discipline, at the
store. -/
theorem foldSP_PM (hμ : μ.verified = true) {st0 : EStore} (hwfst : st0.WF) :
    ∀ (pds : List DeclP) (fe : FEnv) {fe' : FEnv} {s₀ s' : IState},
      fe = mkFEnv fe.env →
      EnvSPOk V μ fe.env →
      ISOKF s₀ → Ext st0 s₀.store →
      (pds.foldlM (checkDeclSPStep μ
        (st0.nodes.size + st0.nodes.size)) fe) s₀ = .ok (fe', s') →
      EnvSPOk V μ fe'.env
  | [], fe, fe', s₀, s', _, hm, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact hm
  | pd :: pds, fe, fe', s₀, s', hfe, hm, hres, hext0, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨⟨mp⟩, hE⟩ := hm
    obtain ⟨d, hd0⟩ := denoteDeclP_total hwfst
      (checkDeclSPStep_inRange hstep)
    have hd : denoteDeclP s₀.store pd = some d :=
      denoteDeclP_mono hwfst hext0 hd0
    rw [hfe] at hstep
    obtain ⟨hres₁, hext₁, hfe₁, F, hF⟩ :=
      checkDeclSPStep_run mp.toEnvR.wf hres hd hstep
    exact foldSP_PM hμ hwfst pds fe₁ hfe₁
      (declStepPM hμ mp hE
        (Setlec.SetR.checkDeclR_ofEnvRE mp.toEnvR hE hF)) hres₁
      (hext0.trans hext₁) h

/-- **The acceptance theorem for the parsed-index executable, P
route** — the shipped driver. -/
theorem checkDeclsSP_sound_P (hμ : μ.verified = true)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP μ st pds = .ok env') :
    Nonempty (EnvS2PM V μ env') := by
  unfold checkDeclsSP at h
  have hwf : st.raw.WF := st.wf
  simp only [Bind.bind, Except.bind] at h
  cases hf : (pds.foldlM (checkDeclSPStep μ
      (st.raw.nodes.size + st.raw.nodes.size))
      (mkFEnv Env.empty)).run' { store := st.raw } with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    simp only [StateT.run'] at hf
    cases hrun : (pds.foldlM (checkDeclSPStep μ
        (st.raw.nodes.size + st.raw.nodes.size))
        (mkFEnv Env.empty)) { store := st.raw } with
    | error e => rw [hrun] at hf; exact nomatch hf
    | ok pr =>
      obtain ⟨feO, sO⟩ := pr
      rw [hrun] at hf
      simp only [Functor.map, Except.map, Except.ok.injEq] at hf
      subst hf
      exact (foldSP_PM hμ hwf pds (mkFEnv Env.empty) rfl
        ⟨⟨EnvS2PM.empty V μ⟩, EtaFamiliesClosed.empty⟩
        (ISOKF.fresh hwf) (Ext.refl _) hrun).1

/-- **THE CAPSTONE FOR THE SHIPPED DRIVER** (task #161, S8): *the
checker, running in a validating mode over the parsed-index core it
actually ships with, never accepts a declaration stream in which some
stored constant has type `Empty`.*

This is `no_proof_of_Empty_P` at `checkDeclsSP` — the #64 mode-4
snapshot bracket, the function `Main.lean` runs — and it closes the
design census's finding 2: before it, the P lane's only statements
were about `checkDecls`, a function the executable does not call.

Hypotheses are **input-level only**: the store bundle `st : WFStore`
(whose well-formedness is a *field*, not a premise — that is what
makes it a bundle), the parsed declarations, the accepted run, and
`hμ : μ.verified = true`, which is `no_proof_of_Empty_P`'s own mode
hypothesis and part of the goal's letter (the annotated checker *is*
the verified mode; `--no-model` ignores annotations by design).  No
tier bundle and no install obligation appears — every one of them was
discharged before `FoldP.lean`'s close, and this file adds none.

`SetTheory V` is the standing parametricity of the consistency
argument (project rule: consistency proofs stay parametric in the
`SetTheory` interface), not a hypothesis about the input. -/
theorem no_proof_of_Empty_SP_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verified = true)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP μ st pds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := checkDeclsSP_sound_P (V := V) hμ h
  exact fun c hc hty => no_constant_of_Empty_P mp c hc hty

end Setlec.SetR.Interp2
