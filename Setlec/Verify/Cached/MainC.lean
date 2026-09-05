import Setlec.Verify.Cached.OfStoreC
import Setlec.SetR.Main
import Setlec.SetR.Main2
import Setlec.SetP.MainP

/-!
# The cached checker variant's consistency corollaries (task #163)

The capstone.  `--core=cached-parsed` is covered by the same
consistency theorems as the production checker's, and **as a corollary
of the simulation, not a re-proof**: every theorem here is
`Setlec/SetR/Main.lean`'s (or `Main2.lean`'s) fold with
`checkDeclSPStepC_run` (`Setlec/Verify/Cached/BridgeCP.lean`) in place
of `checkDeclSPStep_run`, consuming `declStepS` / `checkDeclR_sound` /
`no_constant_of_Empty_R` **unchanged**.

This is the campaign's first (and only) file to import `Setlec.SetR.*`;
the import is additive — nothing under `Setlec/SetR/` is touched.

## What the cached fold drops, and what replaces it

Against `foldSP_R` the fold below loses two legs and gains none:

* **no `Ext`, no store invariant.**  `ISOKF` carried an arena clause
  and the fold threaded `Ext st0 s₀.store` to move denotations from
  the parse store into the run's store.  The cached state has no
  arena, so `CSOKF` is the whole residue and `denoteDeclP_mono`
  disappears with it.
* **no per-step range check.**  `foldSP_R` obtains the step's premise
  `denoteDeclP s₀.store pd = some d` from `denoteDeclP_total` applied
  to `checkDeclSPStep_inRange`.  The cached driver converts the whole
  parse arena *before* the fold, so the premise is supplied up front,
  for the whole list at once, by `declsCOfP_relable`
  (`Setlec/Verify/Cached/OfStoreC.lean`) — whose own totality leg is
  conversion success rather than a range test.

Everything else is `foldSP_R` verbatim: the same `declStepS` dispatch,
the same `checkDeclR_sound`, the same `EnvSOk` carrier.

## Inventory

Nine theorems, in three groups of three (fold, acceptance, no-`Empty`)
across the three carriers, plus the three input-level forms:

| carrier | fold | acceptance | no `Empty` | input level |
| --- | --- | --- | --- | --- |
| `EnvS` | `foldSPC_R` | `checkDeclsSPCached_sound_R` | `no_proof_of_Empty_SPC_R` | `no_proof_of_Empty_input_SPC_R` |
| `EnvS2U` | `foldSPC_R2` | `checkDeclsSPCached_sound_R2` | `no_proof_of_Empty_SPC_R2` | `no_proof_of_Empty_input_SPC_R2` |
| `EnvS2UM` | `foldSPC_R2M` | `checkDeclsSPCached_sound_R2M` | `no_proof_of_Empty_SPC_R2M` | `no_proof_of_Empty_input_SPC_R2M` |
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

/-- **The driver, dissected.**  A successful `checkDeclsSPCached` run
is a successful conversion pass followed by a successful fold from the
empty state — the shape every acceptance corollary below consumes.
Factored out because the three carriers (`EnvS`, `EnvS2U`, `EnvS2UM`)
differ only in what they feed to the fold. -/
theorem checkDeclsSPCached_run {μ : CheckMode} {st : WFStore}
    {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached μ st pds = .ok env') :
    ∃ ds fe s', declsCOfP st.raw {} pds = .ok ds ∧
      (ds.foldlM (checkDeclSPStepC μ) (mkFEnv Env.empty))
          ({} : CState) = .ok (fe, s') ∧
      fe.env = env' := by
  unfold checkDeclsSPCached at h
  simp only [Bind.bind, Except.bind] at h
  cases hconv : declsCOfP st.raw {} pds with
  | error e => rw [hconv] at h; exact nomatch h
  | ok ds =>
    rw [hconv] at h
    dsimp only at h
    cases hf : (ds.foldlM (checkDeclSPStepC μ)
        (mkFEnv Env.empty)).run' ({} : CState) with
    | error e => rw [hf] at h; exact nomatch h
    | ok fe =>
      rw [hf] at h
      obtain rfl : fe.env = env' := by
        have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
        exact Except.ok.inj h'
      simp only [StateT.run'] at hf
      cases hrun : (ds.foldlM (checkDeclSPStepC μ) (mkFEnv Env.empty))
          ({} : CState) with
      | error e => rw [hrun] at hf; exact nomatch hf
      | ok pr =>
        obtain ⟨feO, sO⟩ := pr
        rw [hrun] at hf
        simp only [Functor.map, Except.map, Except.ok.injEq] at hf
        subst hf
        exact ⟨ds, feO, sO, rfl, hrun, rfl⟩

/-- The conversion pass's output, in the fold's premise shape. -/
theorem declsCOfP_rel_run {st : WFStore} {pds : List DeclP}
    {ds : List DeclC} (hconv : declsCOfP st.raw {} pds = .ok ds) :
    ∀ pc ∈ ds, ∃ d, DeclCRel pc d :=
  declsCOfP_relable st.wf OfStoreS.Inv.empty hconv

/-- **The acceptance theorem for the cached parsed-index executable.**
`--core=cached-parsed` accepts only environments carrying the set
model's invariant — the `checkDeclsSP_sound_R` mirror. -/
theorem checkDeclsSPCached_sound_R (V : Type w) [SetTheory V]
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env') :
    Nonempty (EnvS V env') := by
  obtain ⟨ds, fe, s', hconv, hrun, rfl⟩ := checkDeclsSPCached_run h
  exact (foldSPC_R ds (mkFEnv Env.empty) rfl
    ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ CSOKF.empty
    (declsCOfP_rel_run hconv) hrun).1

/-- **No proof of `Empty`** is accepted by the cached parsed-index
executable — the `no_proof_of_Empty_SP_R` mirror. -/
theorem no_proof_of_Empty_SPC_R (V : Type w) [SetTheory V]
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSPCached_sound_R V h
  exact no_constant_of_Empty_R m c hc hty

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

/-- **The cached parsed-index executable's acceptance theorem, over
`EnvS2U`.** -/
theorem checkDeclsSPCached_sound_R2
    (hstep : DeclStep2All V modeR)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env') :
    Nonempty (EnvS2U V env') := by
  obtain ⟨ds, fe, s', hconv, hrun, rfl⟩ := checkDeclsSPCached_run h
  exact (foldSPC_R2 hstep ds (mkFEnv Env.empty) rfl (EnvS2UOk.empty V)
    CSOKF.empty (declsCOfP_rel_run hconv) hrun).1

/-- **No proof of `Empty`** — cached parsed-index executable,
annotated fold. -/
theorem no_proof_of_Empty_SPC_R2 (V : Type w) [SetTheory V]
    (hstep : DeclStep2All V modeR)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSPCached_sound_R2 (V := V) hstep h
  exact no_constant_of_Empty_R2 m c hc hty

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

/-- **The cached parsed-index executable's acceptance theorem, over
`EnvS2UM`.** -/
theorem checkDeclsSPCached_sound_R2M
    (hstep : DeclStep2AllM V modeR)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env') :
    Nonempty (EnvS2UM V modeR env') := by
  obtain ⟨ds, fe, s', hconv, hrun, rfl⟩ := checkDeclsSPCached_run h
  exact (foldSPC_R2M hstep ds (mkFEnv Env.empty) rfl
    (EnvS2UOkM.empty V modeR) CSOKF.empty (declsCOfP_rel_run hconv) hrun).1

/-- **No proof of `Empty`** — cached parsed-index executable,
annotated fold at one mode. -/
theorem no_proof_of_Empty_SPC_R2M (V : Type w) [SetTheory V]
    (hstep : DeclStep2AllM V modeR)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSPCached_sound_R2M (V := V) hstep h
  exact no_constant_of_Empty_R2M m c hc hty

/-! ## The input-level form

`no_proof_of_Empty_input_SP_R` is stated at the *stream* level: no
accepted `List DeclP` contains a `def`/`theorem` whose type index
denotes `Empty`.  It transposes, but not as a corollary of the fold —
its induction has to walk the parsed list and the run in step, and the
cached driver's run is over the *converted* list.  What ties them is
`DeclsPCRel` (`Setlec/Verify/Cached/OfStoreC.lean`), the positional
lift of the conversion relation: the induction runs on the relation
rather than on either list, and each cons supplies both the parsed
declaration's denotation (for the `Empty`-type readout) and the
converted twin's `DeclCRel` (for the step).  Nothing else changes; the
`hfin` core is v1's, verbatim, at `checkDecl_stores`. -/

/-- **No accepted stream declares a proof of `Empty`** — the cached
parsed-index executable, at the stream level (the
`no_proof_of_Empty_input_SP_R` mirror). -/
theorem no_proof_of_Empty_input_SPC_R (V : Type w) [SetTheory V]
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env')
    {cvp : ConstantValP} {value : EIdx}
    (hd : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
      DeclP.thmDecl cvp value ∈ pds)
    (hty : st.denote cvp.type = some (.const emptyName [])) : False := by
  replace hty : st.raw.denote cvp.type
      = some (.const emptyName []) := hty
  obtain ⟨ds, feO, sO, hconv, hrun, -⟩ := checkDeclsSPCached_run h
  have hall : DeclsPCRel st.raw pds ds :=
    declsCOfP_rel st.wf pds {} OfStoreS.Inv.empty hconv
  clear h hconv
  suffices hgen : ∀ (pds : List DeclP) (ds : List DeclC),
      DeclsPCRel st.raw pds ds →
      ∀ (fe : FEnv) {fe' : FEnv} {s₀ s' : CState},
        fe = mkFEnv fe.env → EnvSOk V fe.env → CSOKF s₀ →
        (ds.foldlM (checkDeclSPStepC modeR) fe) s₀ = .ok (fe', s') →
        ((∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds) → False by
    exact hgen pds ds hall (mkFEnv Env.empty) rfl
      ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ CSOKF.empty hrun hd
  clear hrun hd hall
  intro pds ds hall
  induction hall with
  | nil =>
    intro fe fe' s₀ s' _ _ _ _ hdm
    rcases hdm with ⟨_, hdm⟩ | hdm <;> cases hdm
  | @cons pd pc pds ds hrel _ ih =>
    intro fe fe' s₀ s' hfe hm hres h hdm
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstepC, h⟩ := bindC_ok h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨d, hd0, hdrel⟩ := hrel
    rw [hfe] at hstepC
    obtain ⟨hres₁, hfe₁, F, hF⟩ :=
      checkDeclSPStepC_run m.wf hres hdrel hstepC
    by_cases hdis : (∃ hint, pd = DeclP.defnDecl cvp value hint) ∨
        pd = DeclP.thmDecl cvp value
    · have hdd : ∃ ve, (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve hint) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve := by
        rcases hdis with ⟨hint, rfl⟩ | rfl
        · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at hd0
          obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
          rw [hty] at hty'
          cases hty'
          exact ⟨ve, .inl ⟨hint, rfl⟩⟩
        · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at hd0
          obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
          rw [hty] at hty'
          cases hty'
          exact ⟨ve, .inr rfl⟩
      obtain ⟨ve, hdd⟩ := hdd
      have hfin : ((d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                (.regular 0) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve) ∨
            (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve hint)) →
          False := by
        intro hcase
        have hstores : ∃ type, annotateCore modeR fe.env F 0
              (.const emptyName []) = .ok type ∧
            ∃ c, c ∈ fe₁.env.consts ∧ c.toConstantVal =
              ⟨cvp.name, cvp.levelParams, type⟩ := by
          rcases hcase with hdis' | ⟨hint, hdis'⟩
          · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis'
            exact ⟨type, hann, c, hc, hcv⟩
          · obtain ⟨type, hann, c, hc, hcv⟩ :=
              checkDecl_stores hF (Or.inl hdis')
            exact ⟨type, hann, c, hc, hcv⟩
        obtain ⟨type, hann, c, hc, hcv⟩ := hstores
        obtain rfl : Expr.const emptyName [] = type :=
          annotate_empty_const_eq hann
        obtain ⟨m1⟩ := (checkDecl_sound_R (d := d) m hE hF).1
        exact no_constant_of_Empty_R m1 c hc (by rw [hcv])
      rcases hdd with ⟨hint, rfl⟩ | rfl
      · exact hfin (.inr ⟨hint, rfl⟩)
      · exact hfin (.inl (.inr rfl))
    · have hd' : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds := by
        rcases hdm with ⟨hint, hdm2⟩ | hdm2
        · rcases List.mem_cons.mp hdm2 with heq | hmem
          · exact absurd (.inl ⟨hint, heq.symm⟩) hdis
          · exact .inl ⟨hint, hmem⟩
        · rcases List.mem_cons.mp hdm2 with heq | hmem
          · exact absurd (.inr heq.symm) hdis
          · exact .inr hmem
      exact ih fe₁ hfe₁
        (declStepS divModPinS reducePinS stdAxiomKeyS declBasisS
          (declIndS memberKeyS) m hE (checkDeclR_sound m hE hF))
        hres₁ h hd'

/-- **No accepted stream declares a proof of `Empty`** — cached
parsed-index executable, annotated fold (the
`no_proof_of_Empty_input_SP_R2` mirror). -/
theorem no_proof_of_Empty_input_SPC_R2 (V : Type w) [SetTheory V]
    (hstep : DeclStep2All V modeR)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env')
    {cvp : ConstantValP} {value : EIdx}
    (hd : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
      DeclP.thmDecl cvp value ∈ pds)
    (hty : st.denote cvp.type = some (.const emptyName [])) : False := by
  replace hty : st.raw.denote cvp.type
      = some (.const emptyName []) := hty
  obtain ⟨ds, feO, sO, hconv, hrun, -⟩ := checkDeclsSPCached_run h
  have hall : DeclsPCRel st.raw pds ds :=
    declsCOfP_rel st.wf pds {} OfStoreS.Inv.empty hconv
  clear h hconv
  suffices hgen : ∀ (pds : List DeclP) (ds : List DeclC),
      DeclsPCRel st.raw pds ds →
      ∀ (fe : FEnv) {fe' : FEnv} {s₀ s' : CState},
        fe = mkFEnv fe.env → EnvS2UOk V fe.env → CSOKF s₀ →
        (ds.foldlM (checkDeclSPStepC modeR) fe) s₀ = .ok (fe', s') →
        ((∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds) → False by
    exact hgen pds ds hall (mkFEnv Env.empty) rfl
      (EnvS2UOk.empty V) CSOKF.empty hrun hd
  clear hrun hd hall
  intro pds ds hall
  induction hall with
  | nil =>
    intro fe fe' s₀ s' _ _ _ _ hdm
    rcases hdm with ⟨_, hdm⟩ | hdm <;> cases hdm
  | @cons pd pc pds ds hrel _ ih =>
    intro fe fe' s₀ s' hfe hm hres h hdm
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstepC, h⟩ := bindC_ok h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨d, hd0, hdrel⟩ := hrel
    rw [hfe] at hstepC
    obtain ⟨hres₁, hfe₁, F, hF⟩ :=
      checkDeclSPStepC_run m.base.wf hres hdrel hstepC
    by_cases hdis : (∃ hint, pd = DeclP.defnDecl cvp value hint) ∨
        pd = DeclP.thmDecl cvp value
    · have hdd : ∃ ve, (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve hint) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve := by
        rcases hdis with ⟨hint, rfl⟩ | rfl
        · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at hd0
          obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
          rw [hty] at hty'
          cases hty'
          exact ⟨ve, .inl ⟨hint, rfl⟩⟩
        · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at hd0
          obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
          rw [hty] at hty'
          cases hty'
          exact ⟨ve, .inr rfl⟩
      obtain ⟨ve, hdd⟩ := hdd
      have hfin : ((d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                (.regular 0) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve) ∨
            (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve hint)) →
          False := by
        intro hcase
        have hstores : ∃ type, annotateCore modeR fe.env F 0
              (.const emptyName []) = .ok type ∧
            ∃ c, c ∈ fe₁.env.consts ∧ c.toConstantVal =
              ⟨cvp.name, cvp.levelParams, type⟩ := by
          rcases hcase with hdis' | ⟨hint, hdis'⟩
          · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis'
            exact ⟨type, hann, c, hc, hcv⟩
          · obtain ⟨type, hann, c, hc, hcv⟩ :=
              checkDecl_stores hF (Or.inl hdis')
            exact ⟨type, hann, c, hc, hcv⟩
        obtain ⟨type, hann, c, hc, hcv⟩ := hstores
        obtain rfl : Expr.const emptyName [] = type :=
          annotate_empty_const_eq hann
        obtain ⟨m1⟩ := (checkDecl_sound_R2 (d := d) hstep m hE hF).1
        exact no_constant_of_Empty_R2 m1 c hc (by rw [hcv])
      rcases hdd with ⟨hint, rfl⟩ | rfl
      · exact hfin (.inr ⟨hint, rfl⟩)
      · exact hfin (.inl (.inr rfl))
    · have hd' : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds := by
        rcases hdm with ⟨hint, hdm2⟩ | hdm2
        · rcases List.mem_cons.mp hdm2 with heq | hmem
          · exact absurd (.inl ⟨hint, heq.symm⟩) hdis
          · exact .inl ⟨hint, hmem⟩
        · rcases List.mem_cons.mp hdm2 with heq | hmem
          · exact absurd (.inr heq.symm) hdis
          · exact .inr hmem
      exact ih fe₁ hfe₁ (checkDecl_sound_R2 (d := d) hstep m hE hF)
        hres₁ h hd'

/-- **No accepted stream declares a proof of `Empty`** — cached
parsed-index executable, annotated fold at one mode (the
`no_proof_of_Empty_input_SP_R2M` mirror). -/
theorem no_proof_of_Empty_input_SPC_R2M (V : Type w) [SetTheory V]
    (hstep : DeclStep2AllM V modeR)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSPCached modeR st pds = .ok env')
    {cvp : ConstantValP} {value : EIdx}
    (hd : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
      DeclP.thmDecl cvp value ∈ pds)
    (hty : st.denote cvp.type = some (.const emptyName [])) : False := by
  replace hty : st.raw.denote cvp.type
      = some (.const emptyName []) := hty
  obtain ⟨ds, feO, sO, hconv, hrun, -⟩ := checkDeclsSPCached_run h
  have hall : DeclsPCRel st.raw pds ds :=
    declsCOfP_rel st.wf pds {} OfStoreS.Inv.empty hconv
  clear h hconv
  suffices hgen : ∀ (pds : List DeclP) (ds : List DeclC),
      DeclsPCRel st.raw pds ds →
      ∀ (fe : FEnv) {fe' : FEnv} {s₀ s' : CState},
        fe = mkFEnv fe.env → EnvS2UOkM V modeR fe.env → CSOKF s₀ →
        (ds.foldlM (checkDeclSPStepC modeR) fe) s₀ = .ok (fe', s') →
        ((∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds) → False by
    exact hgen pds ds hall (mkFEnv Env.empty) rfl
      (EnvS2UOkM.empty V modeR) CSOKF.empty hrun hd
  clear hrun hd hall
  intro pds ds hall
  induction hall with
  | nil =>
    intro fe fe' s₀ s' _ _ _ _ hdm
    rcases hdm with ⟨_, hdm⟩ | hdm <;> cases hdm
  | @cons pd pc pds ds hrel _ ih =>
    intro fe fe' s₀ s' hfe hm hres h hdm
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstepC, h⟩ := bindC_ok h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨d, hd0, hdrel⟩ := hrel
    rw [hfe] at hstepC
    obtain ⟨hres₁, hfe₁, F, hF⟩ :=
      checkDeclSPStepC_run m.base.wf hres hdrel hstepC
    by_cases hdis : (∃ hint, pd = DeclP.defnDecl cvp value hint) ∨
        pd = DeclP.thmDecl cvp value
    · have hdd : ∃ ve, (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve hint) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve := by
        rcases hdis with ⟨hint, rfl⟩ | rfl
        · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at hd0
          obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
          rw [hty] at hty'
          cases hty'
          exact ⟨ve, .inl ⟨hint, rfl⟩⟩
        · simp only [denoteDeclP, denoteCVP, Option.bind_eq_some_iff,
            Option.map_eq_some_iff] at hd0
          obtain ⟨cv0, ⟨ty, hty', rfl⟩, ve, hve, rfl⟩ := hd0
          rw [hty] at hty'
          cases hty'
          exact ⟨ve, .inr rfl⟩
      obtain ⟨ve, hdd⟩ := hdd
      have hfin : ((d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                (.regular 0) ∨
            d = Declaration.thmDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve) ∨
            (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve hint)) →
          False := by
        intro hcase
        have hstores : ∃ type, annotateCore modeR fe.env F 0
              (.const emptyName []) = .ok type ∧
            ∃ c, c ∈ fe₁.env.consts ∧ c.toConstantVal =
              ⟨cvp.name, cvp.levelParams, type⟩ := by
          rcases hcase with hdis' | ⟨hint, hdis'⟩
          · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis'
            exact ⟨type, hann, c, hc, hcv⟩
          · obtain ⟨type, hann, c, hc, hcv⟩ :=
              checkDecl_stores hF (Or.inl hdis')
            exact ⟨type, hann, c, hc, hcv⟩
        obtain ⟨type, hann, c, hc, hcv⟩ := hstores
        obtain rfl : Expr.const emptyName [] = type :=
          annotate_empty_const_eq hann
        obtain ⟨m1⟩ := (checkDecl_sound_R2M (d := d) hstep m hE hF).1
        exact no_constant_of_Empty_R2M m1 c hc (by rw [hcv])
      rcases hdd with ⟨hint, rfl⟩ | rfl
      · exact hfin (.inr ⟨hint, rfl⟩)
      · exact hfin (.inl (.inr rfl))
    · have hd' : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds := by
        rcases hdm with ⟨hint, hdm2⟩ | hdm2
        · rcases List.mem_cons.mp hdm2 with heq | hmem
          · exact absurd (.inl ⟨hint, heq.symm⟩) hdis
          · exact .inl ⟨hint, hmem⟩
        · rcases List.mem_cons.mp hdm2 with heq | hmem
          · exact absurd (.inr heq.symm) hdis
          · exact .inr hmem
      exact ih fe₁ hfe₁ (checkDecl_sound_R2M (d := d) hstep m hE hF)
        hres₁ h hd'

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
