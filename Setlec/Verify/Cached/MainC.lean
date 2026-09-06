import Setlec.Verify.Cached.BridgeCP
import Setlec.SetP.FoldP

/-!
# The capstone letter of the SHIPPED driver

`checkDeclsSPCachedD` (`Setlec/Cached/ParsedC.lean`) is the only
declaration driver the binary has since task #172, and
`no_proof_of_Empty_SPCD_P` is its consistency letter, on the graded
(P) carrier.

The fold `foldSPC_PM` threads the environment-free residue `CSOKF`
across the steps — the flush lives inside the step — and takes the
per-step relation premise from `DeclCRel_total`: with one expression
type every parsed record relates to a `Declaration` unconditionally,
which is why nothing here carries a store, a well-formedness bundle, or
a conversion pass.

Retired at task #172 with the arena they were fed from: the
`checkDeclsSPCached` letters (`SPC_*` and `input_SPC_*`), which took a
`WFStore` and a `List DeclP` and converted once before folding.

Retired at the SetR removal (2026-09-05) **with their subjects**: the
collapsed-lane letters `no_proof_of_Empty_SPCD_{R,R2,R2M}`, their
acceptance corollaries and the folds `foldSPC_{R,R2,R2M}`.  Every one
of them was stated over an `EnvS`/`EnvS2U`/`EnvS2UM` carrier, and those
carriers were the `Setlec/SetR/*` tier — the B4 measurement having
shown a zero acceptance delta between the two verified configurations,
the P letter is the whole story.  This module used to be the only one
allowed to see both lanes; there is one lane.
-/

namespace Setlec.Cached

open Setlec Setlec.Semantics SetTheory Setlec.SetModel

universe w
variable {V : Type w} [SetTheory V]

/-! ## The direct-parse driver (task #171; restated at #172 B3b)

`Setlec/Frontend/ExportC.lean` parses the export straight into `DeclC`.

**The letter below used to be stated over `List WDeclC`** — the
subtype of records whose `ExprC` slots carried the field invariant
`WFc`, which supplied the fold's premise `∃ d, DeclCRel pc d`.  With
computed fields (#172 B3a) that invariant became provable of
everything, so B3b deleted the subtype and each letter is restated over
`List DeclC`: **a strengthening** — the old letter is the new one at
`ds.map (·.1)` — ratified by the coordinator, with the pre-restatement
statements recorded verbatim in DESIGN.md.  The premise is now met by
`DeclCRel_total`. -/

/-- Every parsed declaration relates to one: with one expression type
the witness is the record itself. -/
theorem DeclCRel_total : ∀ (pc : DeclC), ∃ d, DeclCRel pc d
  | .axiomDecl _ => ⟨_, .axiomDecl rfl⟩
  | .defnDecl _ _ _ => ⟨_, .defnDecl rfl rfl⟩
  | .thmDecl _ _ => ⟨_, .thmDecl rfl rfl⟩
  | .opaqueDecl _ _ => ⟨_, .opaqueDecl rfl rfl⟩
  | .basisDecl _ => ⟨_, .basisDecl⟩
  | .indDecl _ => ⟨_, .indDecl⟩

/-- The direct-parse driver, dissected (the `checkDeclsSPCached_run`
mirror; no conversion pass to peel). -/
theorem checkDeclsSPCachedD_run {μ : CheckMode}
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD μ ds = .ok env') :
    ∃ fe s', (ds.foldlM (checkDeclSPStepC μ)
        (mkFEnv Env.empty)) ({} : CState) = .ok (fe, s') ∧
      fe.env = env' := by
  -- The driver folds the POSITION-CARRYING step (2026-09-07, so that a
  -- rejection names its declaration); its accepts are the plain fold's
  -- accepts (`foldIdxC_ok`), which is why this statement — and every
  -- statement below it — is the one it was.
  unfold checkDeclsSPCachedD at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : (ds.foldlM (checkDeclStepIdxC μ)
      (0, mkFEnv Env.empty)).run' ({} : CState) with
  | error e => rw [hf] at h; exact nomatch h
  | ok p =>
    rw [hf] at h
    obtain rfl : p.2.env = env' := by
      have h' : (Except.ok p.2.env : Except (CheckError × Nat) Env)
        = .ok env' := h
      exact Except.ok.inj h'
    simp only [StateT.run'] at hf
    cases hrun : (ds.foldlM (checkDeclStepIdxC μ)
        (0, mkFEnv Env.empty)) ({} : CState) with
    | error e => rw [hrun] at hf; exact nomatch hf
    | ok pr =>
      obtain ⟨pO, sO⟩ := pr
      rw [hrun] at hf
      simp only [Functor.map, Except.map, Except.ok.injEq] at hf
      subst hf
      exact ⟨pO.2, sO, foldIdxC_ok μ ds 0 (mkFEnv Env.empty) hrun, rfl⟩

/-- The parsed records' carried invariant, in the fold's premise
shape. -/
theorem wdecl_rel {ds : List DeclC} :
    ∀ pc ∈ ds, ∃ d, DeclCRel pc d := fun pc _ => DeclCRel_total pc

/-! ## The P letter for the SHIPPED direct-parse driver (task #172 B4)

Task #163 flipped the shipped path to `checkDeclsSPCachedD`; the P
capstone family predates the flip, so the P mode had no statement
about the function `Main.lean` actually runs — the same species of
gap the S8 batch closed for `checkDeclsSP` (`SetP/MainP.lean`).  The
closure is the retired `SPCD_R` recipe at the P invariant: the cached
per-declaration bridge already lands at the pure `checkDecl` run,
`checkDeclRun_ofEnvFactsE` lifts it to the run record, and `declStepPM` —
the S11a P step, unchanged — walks the `EnvS2PM` carrier.  Nothing
semantic is added; the io-graded P core's soundness (B4's premise-form
slot claims) arrives through `declStepPM`'s dependency cone.

Since the SetR removal (2026-09-05) this is the tree's ONLY letter
about an executable, and `no_proof_of_Empty_P` (`SetP/FoldP.lean`, the
pure fueled checker the tower is stated about) its only sibling. -/

section PLetters

open Setlec.SetP (EnvSPOk EnvS2PM declStepPM
  no_constant_of_Empty_P no_constant_of_False_P)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The direct-parse cached fold preserves the P invariant
(the retired `foldSPC_R2M`'s recipe at `EnvSPOk`; the step is
`declStepPM`, verbatim). -/
theorem foldSPC_PM (hμ : μ.verifiedChecks = true) :
    ∀ (ds : List DeclC) (fe : FEnv) {fe' : FEnv} {s₀ s' : CState},
      fe = mkFEnv fe.env →
      EnvSPOk V μ fe.env →
      CSOKF s₀ →
      (∀ pc ∈ ds, ∃ d, DeclCRel pc d) →
      (ds.foldlM (checkDeclSPStepC μ) fe) s₀ = .ok (fe', s') →
      EnvSPOk V μ fe'.env
  | [], fe, fe', s₀, s', _, hm, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    exact hm
  | pc :: ds, fe, fe', s₀, s', hfe, hm, hres, hrel, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstepC, h⟩ := bindC_ok h
    obtain ⟨⟨mp⟩, hE⟩ := hm
    obtain ⟨d, hd⟩ := hrel pc List.mem_cons_self
    rw [hfe] at hstepC
    obtain ⟨hres₁, hfe₁, F, hF⟩ :=
      checkDeclSPStepC_run hμ mp.toEnvFacts.wf hres hd hstepC
    exact foldSPC_PM hμ ds fe₁ hfe₁
      (declStepPM hμ mp hE (Setlec.Semantics.checkDeclRun_ofEnvFactsE hF))
      hres₁ (fun p hp => hrel p (List.mem_cons_of_mem _ hp)) h

/-- **Acceptance, shipped direct-parse driver, P route.** -/
theorem checkDeclsSPCachedD_sound_P (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD μ ds = .ok env') :
    Nonempty (EnvS2PM V μ env') := by
  obtain ⟨fe, s', hrun, rfl⟩ := checkDeclsSPCachedD_run h
  exact (foldSPC_PM hμ ds (mkFEnv Env.empty) rfl
    ⟨⟨Setlec.SetP.EnvS2PM.empty V μ⟩, EtaFamiliesClosed.empty⟩
    CSOKF.empty wdecl_rel hrun).1

/-- **THE CAPSTONE FOR THE SHIPPED DRIVER, P mode** (task #172 B4):
the checker, running a validating mode over the direct-parse cached
core it ships with — io-graded skips live — never accepts a stream in
which some stored constant has type `Empty`.  Hypotheses are
input-level only. -/
theorem no_proof_of_Empty_SPCD_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD μ ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := checkDeclsSPCachedD_sound_P (V := V) hμ h
  exact fun c hc hty => no_constant_of_Empty_P mp c hc hty

/-- **THE CAPSTONE FOR THE SHIPPED DRIVER, about `False`** (task #181):
the same letter as `no_proof_of_Empty_SPCD_P` at the pinned `False`
block — no hypothesis about how the stream declared `False`. -/
theorem no_proof_of_False_SPCD_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD μ ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := checkDeclsSPCachedD_sound_P (V := V) hμ h
  exact fun c hc hty => no_constant_of_False_P mp c hc hty

/-! ### The loop the binary runs

`Main.lean` calls `checkDeclsSPCachedD` — this letter's subject —
directly on every run that is not printing progress.  The opt-in
`SETLEC_PROGRESS` lane runs an unverified `IO` twin of the same fold
(`Main.checkDeclsProgressIO`): the same `checkDeclStepIdxC` steps in
the same order, with a line printed before each declaration.  **User
ruling, 2026-09-07**: the two folds differ only in the print, and the
verified one is what the default run uses, so no monadic
generalisation, no `LawfulMonad IO` and no `IO`-shaped restatement of
the letters is carried for the sake of the printing lane.  (An earlier
round of this task did carry one — a `Callbacks`-taking loop, a bridge
at every lawful monad, and a hand-proved `IO` case, since core ships
no `LawfulMonad IO`; it is deleted.) -/

end PLetters

end Setlec.Cached
