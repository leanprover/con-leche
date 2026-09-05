import Setlec.Verify.Cached.BridgeCP
import Setlec.SetR.Main
import Setlec.SetR.Main2
import Setlec.SetP.FoldP

/-!
# The capstone letters of the SHIPPED driver

`checkDeclsSPCachedD` (`Setlec/Cached/ParsedC.lean`) is the only
declaration driver the binary has since task #172, and these are its
consistency letters: `no_proof_of_Empty_SPCD_{R,R2,R2M}` on the three
`SetR` carriers, and `no_proof_of_Empty_SPCD_P` on the graded one.

The folds (`foldSPC_R`, `foldSPC_R2`, `foldSPC_R2M`, `foldSPC_PM`)
thread the environment-free residue `CSOKF` across the steps — the
flush lives inside the step — and take the per-step relation premise
from `DeclCRel_total`: with one expression type every parsed record
relates to a `Declaration` unconditionally, which is why nothing here
carries a store, a well-formedness bundle, or a conversion pass.

Retired at task #172 with the arena they were fed from: the
`checkDeclsSPCached` letters (`SPC_*` and `input_SPC_*`), which took a
`WFStore` and a `List DeclP` and converted once before folding.
-/

namespace Setlec.Cached

open Setlec Setlec.SetR SetTheory
open Setlec.SetR.Interp2 (EnvS2U EnvS2UM)

universe w
variable {V : Type w} [SetTheory V]

/-! ## The v1 fold and its corollaries -/

/-- **The converted-declaration fold.**  The mirror of `foldSP_R`: one
`checkDeclSPStepC` per converted declaration, the environment-free
residue `CSOKF` threaded across the steps (the flush lives inside the
step), and the per-step relation premise supplied by the driver's
conversion pass. -/
theorem foldSPC_R :
    ∀ (ds : List DeclC) (fe : FEnv) {fe' : FEnv} {s₀ s' : CState},
      fe = mkFEnv fe.env →
      EnvSOk V fe.env →
      CSOKF s₀ →
      (∀ pc ∈ ds, ∃ d, DeclCRel pc d) →
      (ds.foldlM (checkDeclSPStepC modeR) fe) s₀ = .ok (fe', s') →
      EnvSOk V fe'.env
  | [], fe, fe', s₀, s', _, hm, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    exact hm
  | pc :: ds, fe, fe', s₀, s', hfe, hm, hres, hrel, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindC_ok h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨d, hd⟩ := hrel pc List.mem_cons_self
    rw [hfe] at hstep
    obtain ⟨hres₁, hfe₁, F, hF⟩ := checkDeclSPStepC_run m.wf hres hd hstep
    exact foldSPC_R ds fe₁ hfe₁
      (declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
        (declIndS memberKeyS) m hE (checkDeclR_sound m hE hF)) hres₁
      (fun p hp => hrel p (List.mem_cons_of_mem _ hp)) h

/-! ## The `Main2` siblings

`Setlec/SetR/Main2.lean` reruns the whole battery over the *annotated*
carriers `EnvS2U` / `EnvS2UM`, each conditional on one named
hypothesis — `DeclStep2All V μ` resp. `DeclStep2AllM V μ` — and
nothing else.  Both transpose to the cached fold verbatim: the
hypothesis is about the *declaration step* (`checkDecl` at the fueled
families), which the cached tier consumes unchanged, and the SP forms'
only other premises (`ISOKF`, `Ext`, the range check) are exactly the
legs the cached fold drops.  No premise of the SP siblings fails to
transpose. -/

/-- The converted-declaration fold, over `EnvS2U` (the `foldSP_R2`
mirror). -/
theorem foldSPC_R2 (hstep : DeclStep2All V modeR) :
    ∀ (ds : List DeclC) (fe : FEnv) {fe' : FEnv} {s₀ s' : CState},
      fe = mkFEnv fe.env →
      EnvS2UOk V fe.env →
      CSOKF s₀ →
      (∀ pc ∈ ds, ∃ d, DeclCRel pc d) →
      (ds.foldlM (checkDeclSPStepC modeR) fe) s₀ = .ok (fe', s') →
      EnvS2UOk V fe'.env
  | [], fe, fe', s₀, s', _, hm, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    exact hm
  | pc :: ds, fe, fe', s₀, s', hfe, hm, hres, hrel, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstepC, h⟩ := bindC_ok h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨d, hd⟩ := hrel pc List.mem_cons_self
    rw [hfe] at hstepC
    obtain ⟨hres₁, hfe₁, F, hF⟩ :=
      checkDeclSPStepC_run m.base.wf hres hd hstepC
    exact foldSPC_R2 hstep ds fe₁ hfe₁
      (checkDecl_sound_R2 hstep m hE hF) hres₁
      (fun p hp => hrel p (List.mem_cons_of_mem _ hp)) h

/-- The converted-declaration fold, over `EnvS2UM` (the `foldSP_R2M`
mirror). -/
theorem foldSPC_R2M (hstep : DeclStep2AllM V modeR) :
    ∀ (ds : List DeclC) (fe : FEnv) {fe' : FEnv} {s₀ s' : CState},
      fe = mkFEnv fe.env →
      EnvS2UOkM V modeR fe.env →
      CSOKF s₀ →
      (∀ pc ∈ ds, ∃ d, DeclCRel pc d) →
      (ds.foldlM (checkDeclSPStepC modeR) fe) s₀ = .ok (fe', s') →
      EnvS2UOkM V modeR fe'.env
  | [], fe, fe', s₀, s', _, hm, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureC_ok h
    subst hfe
    exact hm
  | pc :: ds, fe, fe', s₀, s', hfe, hm, hres, hrel, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstepC, h⟩ := bindC_ok h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨d, hd⟩ := hrel pc List.mem_cons_self
    rw [hfe] at hstepC
    obtain ⟨hres₁, hfe₁, F, hF⟩ :=
      checkDeclSPStepC_run m.base.wf hres hd hstepC
    exact foldSPC_R2M hstep ds fe₁ hfe₁
      (checkDecl_sound_R2M hstep m hE hF) hres₁
      (fun p hp => hrel p (List.mem_cons_of_mem _ hp)) h

/-! ## The direct-parse driver (task #171; restated at #172 B3b)

`Setlec/Frontend/ExportC.lean` parses the export straight into `DeclC`.

**The letters below used to be stated over `List WDeclC`** — the
subtype of records whose `ExprC` slots carried the field invariant
`WFc`, which supplied the fold's premise `∃ d, DeclCRel pc d`.  With
computed fields (#172 B3a) that invariant became provable of
everything, so B3b deletes the subtype and each letter is restated over
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
  unfold checkDeclsSPCachedD at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : (ds.foldlM (checkDeclSPStepC μ)
      (mkFEnv Env.empty)).run' ({} : CState) with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    simp only [StateT.run'] at hf
    cases hrun : (ds.foldlM (checkDeclSPStepC μ)
        (mkFEnv Env.empty)) ({} : CState) with
    | error e => rw [hrun] at hf; exact nomatch hf
    | ok pr =>
      obtain ⟨feO, sO⟩ := pr
      rw [hrun] at hf
      simp only [Functor.map, Except.map, Except.ok.injEq] at hf
      subst hf
      first
      | exact ⟨feO, sO, hrun, rfl⟩
      | exact ⟨feO, sO, rfl, rfl⟩

/-- The parsed records' carried invariant, in the fold's premise
shape. -/
theorem wdecl_rel {ds : List DeclC} :
    ∀ pc ∈ ds, ∃ d, DeclCRel pc d := fun pc _ => DeclCRel_total pc

/-- **Acceptance, direct-parse driver, `EnvS`** (the
`checkDeclsSPCached_sound_R` mirror). -/
theorem checkDeclsSPCachedD_sound_R (V : Type w) [SetTheory V]
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD modeR ds = .ok env') :
    Nonempty (EnvS V env') := by
  obtain ⟨fe, s', hrun, rfl⟩ := checkDeclsSPCachedD_run h
  exact (foldSPC_R ds (mkFEnv Env.empty) rfl
    ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ CSOKF.empty
    wdecl_rel hrun).1

/-- **No proof of `Empty`, direct-parse driver.** -/
theorem no_proof_of_Empty_SPCD_R (V : Type w) [SetTheory V]
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD modeR ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSPCachedD_sound_R V h
  exact no_constant_of_Empty_R m c hc hty

/-- **Acceptance, direct-parse driver, `EnvS2U`.** -/
theorem checkDeclsSPCachedD_sound_R2
    (hstep : DeclStep2All V modeR)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD modeR ds = .ok env') :
    Nonempty (EnvS2U V env') := by
  obtain ⟨fe, s', hrun, rfl⟩ := checkDeclsSPCachedD_run h
  exact (foldSPC_R2 hstep ds (mkFEnv Env.empty)
    rfl (EnvS2UOk.empty V) CSOKF.empty wdecl_rel hrun).1

/-- **No proof of `Empty`, direct-parse driver, annotated fold.** -/
theorem no_proof_of_Empty_SPCD_R2 (V : Type w) [SetTheory V]
    (hstep : DeclStep2All V modeR)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD modeR ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSPCachedD_sound_R2 (V := V) hstep h
  exact no_constant_of_Empty_R2 m c hc hty

/-- **Acceptance, direct-parse driver, `EnvS2UM`.** -/
theorem checkDeclsSPCachedD_sound_R2M
    (hstep : DeclStep2AllM V modeR)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD modeR ds = .ok env') :
    Nonempty (EnvS2UM V modeR env') := by
  obtain ⟨fe, s', hrun, rfl⟩ := checkDeclsSPCachedD_run h
  exact (foldSPC_R2M hstep ds (mkFEnv Env.empty)
    rfl (EnvS2UOkM.empty V modeR) CSOKF.empty wdecl_rel hrun).1

/-- **No proof of `Empty`, direct-parse driver, annotated fold at one
mode.** -/
theorem no_proof_of_Empty_SPCD_R2M (V : Type w) [SetTheory V]
    (hstep : DeclStep2AllM V modeR)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD modeR ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSPCachedD_sound_R2M (V := V) hstep h
  exact no_constant_of_Empty_R2M m c hc hty

/-! ## The P letter for the SHIPPED direct-parse driver (task #172 B4)

Task #163 flipped the shipped path to `checkDeclsSPCachedD`; the P
capstone family predates the flip, so the P mode had no statement
about the function `Main.lean` actually runs — the same species of
gap the S8 batch closed for `checkDeclsSP` (`SetP/MainP.lean`).  The
closure is the `SPCD_R` recipe at the P invariant: the cached
per-declaration bridge already lands at the pure `checkDecl` run,
`checkDeclRun_ofEnvRE` lifts it to the run record, and `declStepPM` —
the S11a P step, unchanged — walks the `EnvS2PM` carrier.  Nothing
semantic is added; the io-graded P core's soundness (B4's premise-form
slot claims) arrives through `declStepPM`'s dependency cone.

The interned cached driver `checkDeclsSPCached` gets **no** P letter:
the interned core is scheduled for removal, and its io slot is the
full-infer closure anyway (`Kernel/CoreI.lean`, the short bridge). -/

section PLetters

open Setlec.SetR.Interp2 (EnvSPOk EnvS2PM declStepPM
  no_constant_of_Empty_P)

variable {V : Type w} [SetTheory V] {μ : CheckMode}

/-- The direct-parse cached fold preserves the P invariant
(`foldSPC_R2M`'s recipe at `EnvSPOk`; the step is `declStepPM`,
verbatim). -/
theorem foldSPC_PM (hμ : μ.verified = true) :
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
      checkDeclSPStepC_run mp.toEnvR.wf hres hd hstepC
    exact foldSPC_PM hμ ds fe₁ hfe₁
      (declStepPM hμ mp hE (Setlec.SetR.checkDeclRun_ofEnvRE hF))
      hres₁ (fun p hp => hrel p (List.mem_cons_of_mem _ hp)) h

/-- **Acceptance, shipped direct-parse driver, P route.** -/
theorem checkDeclsSPCachedD_sound_P (hμ : μ.verified = true)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD μ ds = .ok env') :
    Nonempty (EnvS2PM V μ env') := by
  obtain ⟨fe, s', hrun, rfl⟩ := checkDeclsSPCachedD_run h
  exact (foldSPC_PM hμ ds (mkFEnv Env.empty) rfl
    ⟨⟨Setlec.SetR.Interp2.EnvS2PM.empty V μ⟩, EtaFamiliesClosed.empty⟩
    CSOKF.empty wdecl_rel hrun).1

/-- **THE CAPSTONE FOR THE SHIPPED DRIVER, P mode** (task #172 B4):
the checker, running a validating mode over the direct-parse cached
core it ships with — io-graded skips live — never accepts a stream in
which some stored constant has type `Empty`.  Hypotheses are
input-level only. -/
theorem no_proof_of_Empty_SPCD_P (V : Type w) [SetTheory V]
    {μ : CheckMode} (hμ : μ.verified = true)
    {ds : List DeclC} {env' : Env}
    (h : checkDeclsSPCachedD μ ds = .ok env') :
    ∀ c ∈ env'.consts,
      c.toConstantVal.type = .const emptyName [] → False := by
  obtain ⟨mp⟩ := checkDeclsSPCachedD_sound_P (V := V) hμ h
  exact fun c hc hty => no_constant_of_Empty_P mp c hc hty

end PLetters

end Setlec.Cached
