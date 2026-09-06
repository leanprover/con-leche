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
    (h : checkDeclsSPCachedD (cfgOf μ) ds = .ok env') :
    ∃ fe s', (ds.foldlM (checkDeclSPStepC (cfgOf μ))
        (mkFEnv Env.empty)) ({} : CState) = .ok (fe, s') ∧
      fe.env = env' := by
  -- The driver folds the POSITION-CARRYING step (2026-09-07, so that a
  -- rejection names its declaration); its accepts are the plain fold's
  -- accepts (`foldIdxC_ok`), which is why this statement — and every
  -- statement below it — is the one it was.
  unfold checkDeclsSPCachedD at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : (ds.foldlM (checkDeclStepIdxC (cfgOf μ))
      (0, mkFEnv Env.empty)).run' ({} : CState) with
  | error e => rw [hf] at h; exact nomatch h
  | ok p =>
    rw [hf] at h
    obtain rfl : p.2.env = env' := by
      have h' : (Except.ok p.2.env : Except (CheckError × Nat) Env)
        = .ok env' := h
      exact Except.ok.inj h'
    simp only [StateT.run'] at hf
    cases hrun : (ds.foldlM (checkDeclStepIdxC (cfgOf μ))
        (0, mkFEnv Env.empty)) ({} : CState) with
    | error e => rw [hrun] at hf; exact nomatch hf
    | ok pr =>
      obtain ⟨pO, sO⟩ := pr
      rw [hrun] at hf
      simp only [Functor.map, Except.map, Except.ok.injEq] at hf
      subst hf
      exact ⟨pO.2, sO, foldIdxC_ok (cfgOf μ) ds 0 (mkFEnv Env.empty) hrun, rfl⟩

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
      (ds.foldlM (checkDeclSPStepC (cfgOf μ)) fe) s₀ = .ok (fe', s') →
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
      checkDeclSPStepC_run mp.toEnvFacts.wf hres hd hstepC
    exact foldSPC_PM hμ ds fe₁ hfe₁
      (declStepPM hμ mp hE (Setlec.Semantics.checkDeclRun_ofEnvFactsE hF))
      hres₁ (fun p hp => hrel p (List.mem_cons_of_mem _ hp)) h

/-- **Acceptance, shipped direct-parse driver, P route.** -/
theorem checkDeclsSPCachedD_sound_P (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD (cfgOf μ) ds = .ok env') :
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
    (h : checkDeclsSPCachedD (cfgOf μ) ds = .ok env') :
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
    (h : checkDeclsSPCachedD (cfgOf μ) ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := checkDeclsSPCachedD_sound_P (V := V) hμ h
  exact fun c hc hty => no_constant_of_False_P mp c hc hty

/-! ### … and for the `IO` loop the binary runs (2026-09-07)

`Main.lean` does not call `checkDeclsSPCachedD` directly: it runs
`checkDeclsSPCachedM` in `IO`, with a progress callback around each
declaration.  The generic bridge (`checkDeclsSPCachedM_eq`,
`Setlec/Cached/ParsedC.lean`) says that in **any lawful monad** the
loop runs the callback sequence and returns the pure driver's verdict.

`IO` cannot be quoted as an instance of it in this toolchain: `IO` is
`EIO IO.Error = EST IO.Error IO.RealWorld`, and core ships **no
`LawfulMonad` instance** for `EST` (nor for `EIO`/`IO`) — `#synth
LawfulMonad IO` fails.  So the run-level statement is proved here
directly, by the same induction over the same two definitions, using
`EST`'s `bind`/`pure` (two `rfl`-level lemmas below).  If core ever
gains the instance, this section collapses into an instantiation of
the generic bridge.

What the letter says: **for ANY callbacks**, if the `IO` run comes back
with an accepted environment, that environment has no constant of type
`Empty`.  A callback cannot change that — it sees the fold position and
the record, returns `Unit`, and can at worst throw, in which case the
run returns no result at all. -/

section IOLetter

/-- `IO`'s bind, reduced: a successful run of `x >>= f` ran `x`
successfully first. -/
theorem io_bind_ok {α β : Type} {x : IO α} {f : α → IO β}
    {s s' : Void IO.RealWorld} {b : β}
    (h : (x >>= f) s = .ok b s') :
    ∃ a s₁, x s = .ok a s₁ ∧ f a s₁ = .ok b s' := by
  have hb : (x >>= f) s = EST.bind x f s := rfl
  rw [hb] at h
  unfold EST.bind at h
  cases hx : x s with
  | ok a s₁ => rw [hx] at h; exact ⟨a, s₁, rfl, h⟩
  | error e s₁ => rw [hx] at h; exact nomatch h

/-- `IO`'s pure, reduced. -/
theorem io_pure_ok {α : Type} {v r : α} {s s' : Void IO.RealWorld}
    (h : (pure v : IO α) s = .ok r s') : r = v := by
  have hp : (pure v : IO α) s = .ok v s := rfl
  rw [hp] at h
  injection h with h₁ _
  exact h₁.symm

/-- **The monadic loop returns the pure loop's verdict**, whatever the
callbacks do (the `IO` instance of `checkDeclsGoM_eq`, proved directly
for want of a `LawfulMonad IO`). -/
theorem checkDeclsGoM_io_run (cb : Callbacks IO) (cfg : CoreCfg) :
    ∀ (ds : List DeclC) (p : Nat × FEnv) (s : CState)
      {ω ω' : Void IO.RealWorld} {r : Except (CheckError × Nat) Env},
      checkDeclsGoM cb cfg ds p s ω = .ok r ω' →
      r = checkDeclsGoP cfg ds p s := by
  intro ds
  induction ds with
  | nil => intro p s ω ω' r h; exact io_pure_ok h
  | cons pd ds ih =>
    intro p s ω ω' r h
    rw [checkDeclsGoM] at h
    obtain ⟨_, ω₁, _, h⟩ := io_bind_ok h
    simp only [checkDeclsGoP]
    cases hstep : checkDeclStepIdxC cfg p pd s with
    | error e =>
      rw [hstep] at h
      exact io_pure_ok h
    | ok pr =>
      obtain ⟨p', s'⟩ := pr
      rw [hstep] at h
      obtain ⟨_, ω₂, _, h⟩ := io_bind_ok h
      exact ih p' s' h

/-- The shipped shape: the `IO` driver's result **is**
`checkDeclsSPCachedD`'s. -/
theorem checkDeclsSPCachedM_run (cb : Callbacks IO) (cfg : CoreCfg)
    (ds : List DeclC) {ω ω' : Void IO.RealWorld}
    {r : Except (CheckError × Nat) Env}
    (h : checkDeclsSPCachedM cb cfg ds ω = .ok r ω') :
    r = checkDeclsSPCachedD cfg ds := by
  rw [checkDeclsSPCachedD_go]
  exact checkDeclsGoM_io_run cb cfg ds _ _ h

/-- **THE CAPSTONE FOR THE LOOP THE BINARY RUNS.**  Whatever the
callbacks do, an `IO` run of the callback-carrying driver that comes
back with an accepted environment has accepted no constant of type
`Empty`. -/
theorem no_proof_of_Empty_SPCD_IO (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    (cb : Callbacks IO) {ds : List DeclC} {env' : Env}
    {ω ω' : Void IO.RealWorld}
    (h : checkDeclsSPCachedM cb (cfgOf μ) ds ω = .ok (.ok env') ω') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False :=
  no_proof_of_Empty_SPCD_P V hμ (checkDeclsSPCachedM_run cb (cfgOf μ) ds h).symm

end IOLetter

end PLetters

end Setlec.Cached
