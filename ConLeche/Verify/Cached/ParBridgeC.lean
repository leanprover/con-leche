import ConLeche.Verify.Cached.MainC

/-!
# The deferred-body driver's bridge

The fan-out (`Main.lean`, `CON_LECHE_PAR`) runs the stream in two
passes: an install pass that checks everything except theorem BODIES,
recording each deferred body as a `BodyJob` carrying the very `FEnv`
the fold held, and a body pass that checks the jobs in any order, each
from a fresh memo state.  This module is the argument that such a run
means what the sequential fold means.

**The spec is the pivot.**  A cached run's success gives a SPEC run's
success (`thmPrepC_sim`, `thmBodyC_sim`); the spec checker has no memo
state, so the install pass's half and a worker's half — which share no
`CState` — compose there.  Going the other way, from one cached state to
another, would need the caches to be COMPLETE, which the simulation does
not give and this route does not ask for.

The composition needs the two halves to be *a computation followed by a
continuation*, which is what the CPS spelling buys and what the two
lemmas below say.
-/

namespace ConLeche.Cached

open ConLeche

variable {mode : CheckMode}

/-! ## One declaration

`thmInstallJobC_run` (`ConLeche/Verify/Cached/BridgeCP.lean`) is the
step this bridge turns on: the install pass's theorem step and a
worker's body check, run in different memo states, compose at the spec
into the branch.  Here that is lifted to a whole declaration — every
other kind runs the ORDINARY step in the install pass, so for those this
is the ordinary step lemma. -/

/-- Every kind but `thmDecl` runs the ORDINARY step in the install pass.
Stated at the step's already-reduced shape, so a call site whose kind is
a concrete constructor gets it definitionally. -/
private theorem stepEq_of_ordinary {env : Env} {pd : DeclC} {s₀ : CState}
    {i i' : Nat} {fe' : FEnv} {jobs jobs' : Array BodyJob} {s' : CState}
    (h : (match checkDeclSPStepC mode (mkFEnv env) pd s₀ with
          | Except.ok (fe₂, s₂) =>
            (Except.ok ((i + 1, fe₂, jobs), s₂) :
              Except (CheckError × Nat) ((Nat × FEnv × Array BodyJob) × CState))
          | Except.error e => Except.error (e, i))
      = Except.ok ((i', fe', jobs'), s')) :
    checkDeclSPStepC mode (mkFEnv env) pd s₀ = .ok (fe', s') := by
  cases hst : checkDeclSPStepC mode (mkFEnv env) pd s₀ with
  | error e => rw [hst] at h; exact nomatch h
  | ok r =>
    obtain ⟨fe₂, s₂⟩ := r
    rw [hst] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
    -- `cases hst : …` rewrote the goal too
    rfl

/-- One step of the install pass, with the bodies it deferred checked:
the spec's declaration check succeeds at that environment, which is
exactly what `checkDeclSPStepC_run` gives the sequential fold. -/
theorem installStepC_run (hμ : mode.verifiedChecks = true) {env : Env}
    (henv : EnvWF env) {pd : DeclC} {d : Declaration} {s₀ : CState}
    (hres : CSOKF s₀) (hrel : DeclCRel pd d)
    {i i' : Nat} {fe' : FEnv} {jobs jobs' : Array BodyJob} {s' : CState}
    (h : installStepC mode (i, mkFEnv env, jobs) pd s₀
      = .ok ((i', fe', jobs'), s'))
    (hbody : ∀ j ∈ jobs', bodyCheckC mode j = .ok ()) :
    CSOKF s' ∧ fe' = mkFEnv fe'.env ∧
      ∃ F, checkDecl mode (fueledOps mode F) env d = .ok fe'.env := by
  cases hrel with
  | @thmDecl cv tyE value ve hty hv =>
    -- the deferred branch: install half here, body half in a worker
    rw [installStepC] at h
    dsimp only at h
    cases hinner : (do
        flushC
        let (cvA, jty) ← checkConstantValC mode (mkFEnv env) cv
        thmInstallJobC mode (mkFEnv env) cvA jty value :
          CheckCM (FEnv × BodyJob)) s₀ with
    | error e => rw [hinner] at h; exact nomatch h
    | ok r =>
      obtain ⟨⟨fe₂, job₂⟩, s₂⟩ := r
      rw [hinner] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
      -- the flush, then the constant value, then the install half
      obtain ⟨u, s₁, hflush, hinner⟩ := bindC_ok hinner
      rw [flushC_run] at hflush
      injection hflush with hflush
      obtain rfl : s₀.flushed = s₁ := congrArg Prod.snd hflush
      have hcsok : CSOK mode env s₀.flushed := flushC_csok hres
      obtain ⟨pr, s₃, hcv, hinst⟩ := bindC_ok hinner
      obtain ⟨cvA, jty⟩ := pr
      obtain ⟨hs₃, cvM, hP, F₁, hF₁⟩ :=
        (checkConstantValC_sim hμ henv hcsok hty) _ _ hcv
      obtain ⟨rfl, hname, hwty, hjty⟩ := hP
      -- the worker's body fact, for the job this step pushed
      have hjob : bodyCheckC mode job₂ = .ok () := by
        have := hbody { job₂ with idx := i } (Array.mem_push_self ..)
        exact this
      obtain ⟨hs', hfe', F₂, hF₂⟩ :=
        thmInstallJobC_run hμ henv hs₃ hwty hjty hv hinst
          (by
            unfold bodyCheckC StateT.run' at hjob
            cases hb : thmBodyC mode job₂.fe job₂.name job₂.jty job₂.jv
                (pure ()) {} with
            | error e => rw [hb] at hjob; exact nomatch hjob
            | ok r => obtain ⟨⟨⟩, s''⟩ := r; exact ⟨s'', rfl⟩)
      refine ⟨hs'.residue, hfe', max F₁ F₂, ?_⟩
      rw [← checkDecl_datF]
      unfold checkDecl
      dsimp only
      rw [FueledM.atF_bind]
      rw [(checkConstantVal (fueledOpsM mode) env
        ⟨cv.name, cv.levelParams, tyE⟩).property (Nat.le_max_left F₁ F₂) hF₁]
      dsimp only [bind, Except.bind]
      exact (checkThmVal (fueledOpsM mode) env cvA ve).property
        (Nat.le_max_right F₁ F₂) hF₂
  | @axiomDecl cv tyE hty =>
    exact checkDeclSPStepC_run hμ henv hres (.axiomDecl hty) (stepEq_of_ordinary h)
  | @defnDecl cv tyE value ve hint hty hv =>
    exact checkDeclSPStepC_run hμ henv hres (.defnDecl hty hv) (stepEq_of_ordinary h)
  | @opaqueDecl cv tyE value ve hty hv =>
    exact checkDeclSPStepC_run hμ henv hres (.opaqueDecl hty hv) (stepEq_of_ordinary h)
  | @basisDecl kind =>
    exact checkDeclSPStepC_run hμ henv hres .basisDecl (stepEq_of_ordinary h)
  | @indDecl block =>
    exact checkDeclSPStepC_run hμ henv hres .indDecl (stepEq_of_ordinary h)

/-! ## The install pass's jobs only grow

The fold's body hypothesis is stated about the jobs it ENDS with; a
step needs it for the jobs it produced.  These two say the accumulator
is monotone, so the end's hypothesis reaches every step. -/

private theorem bindP_ok {α β : Type}
    {x : StateT CState (Except (CheckError × Nat)) α}
    {k : α → StateT CState (Except (CheckError × Nat)) β}
    {s₀ : CState} {v : β} {s' : CState}
    (h : (x >>= k) s₀ = .ok (v, s')) :
    ∃ a s₁, x s₀ = .ok (a, s₁) ∧ k a s₁ = .ok (v, s') := by
  simp only [Bind.bind, StateT.bind] at h
  cases hx : x s₀ with
  | error e => rw [hx] at h; exact nomatch h
  | ok r =>
    obtain ⟨a, s₁⟩ := r
    rw [hx] at h
    exact ⟨a, s₁, rfl, h⟩

private theorem pureP_ok {α : Type} {a : α} {s₀ : CState} {v : α} {s' : CState}
    (h : (pure a : StateT CState (Except (CheckError × Nat)) α) s₀
      = .ok (v, s')) : a = v ∧ s₀ = s' := by
  simp only [pure, StateT.pure, Except.pure, Except.ok.injEq,
    Prod.mk.injEq] at h
  exact h

/-- One step keeps the jobs it was given. -/
theorem installStepC_jobs_mono {pd : DeclC} {s₀ : CState}
    {i i' : Nat} {fe fe' : FEnv} {jobs jobs' : Array BodyJob} {s' : CState}
    (h : installStepC mode (i, fe, jobs) pd s₀ = .ok ((i', fe', jobs'), s'))
    {j : BodyJob} (hj : j ∈ jobs) : j ∈ jobs' := by
  -- `unfold`, not `rw`: rewriting with the definition picks the
  -- catch-all equation, whose "the earlier patterns do not match" side
  -- condition is not provable for a generic kind
  unfold installStepC at h
  -- case on the kind so the definition's match reduces, then on the
  -- step's own result
  cases pd <;>
    · try dsimp only at h
      first
        | (split at h <;>
             first
               | contradiction
               | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
                  obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
                  first | exact Array.mem_push_of_mem _ hj | exact hj))
        | (simp only [Except.ok.injEq, Prod.mk.injEq] at h
           obtain ⟨⟨rfl, rfl, rfl⟩, rfl⟩ := h
           first | exact Array.mem_push_of_mem _ hj | exact hj)
        | contradiction

/-- The fold keeps the jobs it started with. -/
theorem installFoldC_jobs_mono :
    ∀ (ds : List DeclC) (p : Nat × FEnv × Array BodyJob)
      {p' : Nat × FEnv × Array BodyJob} {s₀ s' : CState},
      (ds.foldlM (installStepC mode) p) s₀ = .ok (p', s') →
      ∀ {j : BodyJob}, j ∈ p.2.2 → j ∈ p'.2.2
  | [], p, p', s₀, s', h, j, hj => by
    obtain ⟨rfl, rfl⟩ := pureP_ok h
    exact hj
  | pd :: ds, p, p', s₀, s', h, j, hj => by
    rw [List.foldlM_cons] at h
    obtain ⟨p₁, s₁, hstep, h⟩ := bindP_ok h
    obtain ⟨i, fe, jobs⟩ := p
    obtain ⟨i₁, fe₁, jobs₁⟩ := p₁
    exact installFoldC_jobs_mono ds _ h (installStepC_jobs_mono hstep hj)

/-! ## The fold, and the parallel capstone

The sequential assembly is `foldSPC_PM` / `checkDeclsSPCachedD_sound_P`
(`ConLeche/Verify/Cached/MainC.lean`).  These are their twins for the
two-pass driver: the same invariant, threaded by the same `declStepPM`,
with the per-declaration fact coming from `installStepC_run` instead of
`checkDeclSPStepC_run` — which is the whole content of the fan-out being
sound. -/

section PLetters

universe w

open ConLeche.SetP (EnvSPOk EnvS2PM declStepPM)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The install pass preserves the P invariant, given that every body it
deferred was checked. -/
theorem foldParPM (hμ : μ.verifiedChecks = true) :
    ∀ (ds : List DeclC) (i : Nat) (fe : FEnv) (jobs : Array BodyJob)
      {p' : Nat × FEnv × Array BodyJob} {s₀ s' : CState},
      fe = mkFEnv fe.env →
      EnvSPOk V μ fe.env →
      CSOKF s₀ →
      (∀ pc ∈ ds, ∃ d, DeclCRel pc d) →
      (ds.foldlM (installStepC μ) (i, fe, jobs)) s₀ = .ok (p', s') →
      (∀ j ∈ p'.2.2, bodyCheckC μ j = .ok ()) →
      EnvSPOk V μ p'.2.1.env
  | [], i, fe, jobs, p', s₀, s', _, hm, _, _, h, _ => by
    obtain ⟨rfl, rfl⟩ := pureP_ok h
    exact hm
  | pc :: ds, i, fe, jobs, p', s₀, s', hfe, hm, hres, hrel, h, hbody => by
    rw [List.foldlM_cons] at h
    obtain ⟨p₁, s₁, hstep, h⟩ := bindP_ok h
    obtain ⟨i₁, fe₁, jobs₁⟩ := p₁
    obtain ⟨⟨mp⟩, hE⟩ := hm
    obtain ⟨d, hd⟩ := hrel pc List.mem_cons_self
    rw [hfe] at hstep
    obtain ⟨hres₁, hfe₁, F, hF⟩ :=
      installStepC_run hμ mp.toEnvFacts.wf hres hd hstep
        (fun j hj => hbody j (installFoldC_jobs_mono ds _ h hj))
    exact foldParPM hμ ds i₁ fe₁ jobs₁ hfe₁
      (declStepPM hμ mp hE (ConLeche.Semantics.checkDeclRun_ofEnvFactsE hF))
      hres₁ (fun p hp => hrel p (List.mem_cons_of_mem _ hp)) h hbody

/-- The install pass, dissected. -/
theorem installPassC_run {ds : List DeclC} {fe' : FEnv} {jobs : Array BodyJob}
    (h : installPassC μ ds = .ok (fe', jobs)) :
    ∃ p' s', (ds.foldlM (installStepC μ) (0, mkFEnv Env.empty, #[]))
        ({} : CState) = .ok (p', s') ∧ p'.2.1 = fe' ∧ p'.2.2 = jobs := by
  unfold installPassC at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : (ds.foldlM (installStepC μ)
      (0, mkFEnv Env.empty, #[])).run' ({} : CState) with
  | error e => rw [hf] at h; exact nomatch h
  | ok p =>
    rw [hf] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [StateT.run'] at hf
    cases hrun : (ds.foldlM (installStepC μ)
        (0, mkFEnv Env.empty, #[])) ({} : CState) with
    | error e => rw [hrun] at hf; exact nomatch hf
    | ok pr =>
      obtain ⟨pO, sO⟩ := pr
      rw [hrun] at hf
      simp only [Functor.map, Except.map, Except.ok.injEq] at hf
      subst hf
      -- `cases hrun : …` rewrote the goal too
      exact ⟨pO, sO, rfl, rfl, rfl⟩

/-- **THE PARALLEL CAPSTONE.**  A deferred-body run — an install pass
that accepted, and every body it deferred checked, in any order, each
from a fresh memo state — yields the same model invariant the sequential
driver's acceptance does.

What it does NOT need: that the two passes share a memo state, that the
caches be complete, or that anything be re-checked.  The install pass's
half and a worker's half meet at the SPEC, where there is no memo state
to disagree about, and `checkThmVal_split` puts them back together into
the branch the model tier is stated about. -/
theorem installPassC_sound_P (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} {fe' : FEnv} {jobs : Array BodyJob}
    (h : installPassC μ ds = .ok (fe', jobs))
    (hbody : ∀ j ∈ jobs, bodyCheckC μ j = .ok ()) :
    Nonempty (EnvS2PM V μ fe'.env) := by
  obtain ⟨p', s', hrun, rfl, rfl⟩ := installPassC_run h
  exact (foldParPM hμ ds 0 (mkFEnv Env.empty) #[] rfl
    ⟨⟨ConLeche.SetP.EnvS2PM.empty V μ⟩, EtaFamiliesClosed.empty⟩
    CSOKF.empty wdecl_rel hrun hbody).1

/-- **The parallel driver's letter, `Empty`**: a deferred-body run never
accepts a stream in which some stored constant has type `Empty`.  The
same sentence as `no_proof_of_Empty_SPCD_P`, about a run whose bodies
were checked in any order, in any number of workers, sharing no memo
state with the pass that installed them. -/
theorem no_proof_of_Empty_par_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} {fe' : FEnv} {jobs : Array BodyJob}
    (h : installPassC μ ds = .ok (fe', jobs))
    (hbody : ∀ j ∈ jobs, bodyCheckC μ j = .ok ()) :
    ∀ c ∈ fe'.env.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := installPassC_sound_P (V := V) hμ h hbody
  exact fun c hc hty => ConLeche.SetP.no_constant_of_Empty_P mp c hc hty

/-- **The parallel driver's letter, `False`** — the same at the pinned
`False` block, with no hypothesis about how the stream declared it. -/
theorem no_proof_of_False_par_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verifiedChecks = true)
    {ds : List DeclC} {fe' : FEnv} {jobs : Array BodyJob}
    (h : installPassC μ ds = .ok (fe', jobs))
    (hbody : ∀ j ∈ jobs, bodyCheckC μ j = .ok ()) :
    ∀ c ∈ fe'.env.consts,
      c.toConstantVal.type = .const falseName [] → False := by
  obtain ⟨mp⟩ := installPassC_sound_P (V := V) hμ h hbody
  exact fun c hc hty => ConLeche.SetP.no_constant_of_False_P mp c hc hty

end PLetters

end ConLeche.Cached
