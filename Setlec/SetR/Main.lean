import Setlec.SetR.Bridge.Sound
import Setlec.Verify.BridgeWFDecl
import Setlec.Verify.BridgeSDecl
import Setlec.Verify.BridgePDecl
import Setlec.Verify.DeclStores

/-!
# The `SetR` route's consistency theorems (task #148, T6)

The replacements for `Setlec/Model/Consistency*.lean`'s top-level
claims, on the algorithmic-relation route.  Three of the fourteen land
here — the ones over `checkDecls` at `fueledOps`.  The other eleven are
the `_S`/`_C`/`_SP` driver variants, each of which needs its *own*
fold soundness (`foldlM_soundS`, `foldlM_soundC`, `foldSP` in the
Model lane); they are a distinct shape and are tracked separately.

Every theorem here carries its obligations as **named hypotheses**,
all stated attached to an `EnvS`.  That is deliberate: the campaign's
recorded vacuity signature is a valuation with no invariant attached,
and these are the last place new hypotheses enter.
-/

namespace Setlec.SetR
open Setlec.TT Setlec.TTVerify SetTheory EStore Expr
universe u w
variable {V : Type w} [SetTheory V]

theorem no_constant_of_Empty_R {env : Env} (m : EnvS V env)
    (c : ConstantInfo) (hc : c ∈ env.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨t, hTi, hrest⟩ := m.mem_type c hc (fun _ => 0)
  rw [hty, denoteClosed, denote_const] at hTi
  revert hTi
  cases hf : env.find? emptyName with
  | none => intro hTi; exact nomatch hTi
  | some ci =>
    dsimp only
    split
    · next hlen =>
      intro hTi
      obtain rfl := (Option.some.inj hTi).symm
      obtain ⟨u0, hu0⟩ := m.empty_pinned
        (Level.substFn (fun _ => 0) ci.toConstantVal.levelParams [])
      obtain ⟨hmem, -⟩ := hrest (fun _ => (SetTheory.empty : V))
      rw [hu0, interp_emptyT] at hmem
      exact not_mem_empty _ hmem
    · intro hTi; exact nomatch hTi

/-- **The acceptance theorem, on the `SetR` route.** -/
theorem checkDecls_sound_R
    {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env') :
    Nonempty (EnvS V env') :=
  (foldlM_R (hg := rfl)
    ds Env.empty ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ h).1

/-- **No proof of `Empty` is ever accepted**, on the `SetR` route. -/
theorem no_proof_of_Empty_R (V : Type w) [SetTheory V]
    {F : Nat}
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound_R (V := V) h
  exact no_constant_of_Empty_R m c hc hty

/-- The cached-executable fold.  `checkDecl_bridge` supplies, per
declaration, a fuel at which the pure checker reproduces the cached
run; everything after that is `foldlM_R (hg := rfl)`'s step. -/
theorem foldlM_RC :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvSOk V env →
      ds.foldlM (checkDecl modeR (cachedOps modeR)) env = .ok env' →
      EnvSOk V env'
  | [], env, env', hm, h => by
    have h' : (Except.ok env : CheckM Env) = Except.ok env' := h
    cases h'
    exact hm
  | d :: ds, env, _, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDecl modeR (cachedOps modeR) env d with
    | error e => rw [hd] at h; exact nomatch h
    | ok env1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      obtain ⟨F, hF⟩ := checkDecl_bridge m.wf hd
      exact foldlM_RC ds env1
        (declStepS (hg := rfl) divModPinS reducePinS stdAxiomKeyS declBasisS
          (declIndS memberKeyS) m hE (checkDeclR_sound (hg := rfl) m hE hF)) h
/-- **The acceptance theorem for the cached executable checker.** -/
theorem checkDeclsC_sound_R
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (cachedOps modeR) ds = .ok env') :
    Nonempty (EnvS V env') :=
  (foldlM_RC ds Env.empty
    ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ h).1

/-- **No proof of `Empty`** is accepted by the cached executable. -/
theorem no_proof_of_Empty_C_R (V : Type w) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (cachedOps modeR) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsC_sound_R (V := V) h
  exact no_constant_of_Empty_R m c hc hty

/-- The shared-state executable's fold. -/
theorem foldlM_RS :
    ∀ (ds : List Declaration) (fe : FEnv) {fe' : FEnv},
      fe = mkFEnv fe.env →
      EnvSOk V fe.env →
      ds.foldlM (checkDeclSharedF modeR) fe = .ok fe' →
      EnvSOk V fe'.env
  | [], fe, fe', _, hm, h => by
    have h' : (Except.ok fe : CheckM FEnv) = Except.ok fe' := h
    cases h'
    exact hm
  | d :: ds, fe, fe', hfe, hm, h => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hd : checkDeclSharedF modeR fe d with
    | error e => rw [hd] at h; exact nomatch h
    | ok fe1 =>
      rw [hd] at h
      obtain ⟨⟨m⟩, hE⟩ := hm
      rw [hfe] at hd
      obtain ⟨hfe1, F, hF⟩ := checkDeclSharedF_bridge m.wf hd
      exact foldlM_RS ds fe1 hfe1
        (declStepS (hg := rfl) divModPinS reducePinS stdAxiomKeyS declBasisS
          (declIndS memberKeyS) m hE (checkDeclR_sound (hg := rfl) m hE hF)) h
/-- **The acceptance theorem for the shared-state executable.** -/
theorem checkDeclsS_sound_R
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared modeR ds = .ok env') :
    Nonempty (EnvS V env') := by
  unfold checkDeclsShared at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : ds.foldlM (checkDeclSharedF modeR) (mkFEnv Env.empty) with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    exact (foldlM_RS ds (mkFEnv Env.empty) rfl
      ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ hf).1

/-- **No proof of `Empty`** is accepted by the shared-state
executable. -/
theorem no_proof_of_Empty_S_R (V : Type w) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared modeR ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsS_sound_R (V := V) h
  exact no_constant_of_Empty_R m c hc hty

/-- The parsed-index executable's fold.  The store invariant's
supplier is the bundle: `WFStore.wf` gives `st.raw.WF` once, and the
fold threads `ISOKF`/`Ext` from `checkDeclSPStep_run` — the same
"name the environment each premise is at" discipline, at the store. -/
theorem foldSP_R
    {st0 : EStore} (hwfst : st0.WF) :
    ∀ (pds : List DeclP) (fe : FEnv) {fe' : FEnv} {s₀ s' : IState},
      fe = mkFEnv fe.env →
      EnvSOk V fe.env →
      ISOKF s₀ → Ext st0 s₀.store →
      (pds.foldlM (checkDeclSPStep modeR
        (st0.nodes.size + st0.nodes.size)) fe) s₀ = .ok (fe', s') →
      EnvSOk V fe'.env
  | [], fe, fe', s₀, s', _, hm, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact hm
  | pd :: pds, fe, fe', s₀, s', hfe, hm, hres, hext0, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨d, hd0⟩ := denoteDeclP_total hwfst
      (checkDeclSPStep_inRange hstep)
    have hd : denoteDeclP s₀.store pd = some d :=
      denoteDeclP_mono hwfst hext0 hd0
    rw [hfe] at hstep
    obtain ⟨hres₁, hext₁, hfe₁, F, hF⟩ :=
      checkDeclSPStep_run m.wf hres hd hstep
    exact foldSP_R hwfst pds fe₁ hfe₁
      (declStepS (hg := rfl) divModPinS reducePinS stdAxiomKeyS declBasisS
        (declIndS memberKeyS) m hE (checkDeclR_sound (hg := rfl) m hE hF)) hres₁
      (hext0.trans hext₁) h

/-- **The acceptance theorem for the parsed-index executable.** -/
theorem checkDeclsSP_sound_R
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP modeR st pds = .ok env') :
    Nonempty (EnvS V env') := by
  unfold checkDeclsSP at h
  have hwf : st.raw.WF := st.wf
  simp only [Bind.bind, Except.bind] at h
  cases hf : (pds.foldlM (checkDeclSPStep modeR
      (st.raw.nodes.size + st.raw.nodes.size))
      (mkFEnv Env.empty)).run' { store := st.raw } with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    simp only [StateT.run'] at hf
    cases hrun : (pds.foldlM (checkDeclSPStep modeR
        (st.raw.nodes.size + st.raw.nodes.size))
        (mkFEnv Env.empty)) { store := st.raw } with
    | error e => rw [hrun] at hf; exact nomatch hf
    | ok pr =>
      obtain ⟨feO, sO⟩ := pr
      rw [hrun] at hf
      simp only [Functor.map, Except.map, Except.ok.injEq] at hf
      subst hf
      exact (foldSP_R hwf pds
        (mkFEnv Env.empty) rfl ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩
        (ISOKF.fresh hwf) (Ext.refl _) hrun).1

/-- **No proof of `Empty`** is accepted by the parsed-index
executable. -/
theorem no_proof_of_Empty_SP_R (V : Type w) [SetTheory V]
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP modeR st pds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSP_sound_R (V := V) h
  exact no_constant_of_Empty_R m c hc hty

/-- **One checked declaration extends the invariant.** -/
theorem checkDecl_sound_R
    {F : Nat}
    {env env₂ : Env} {d : Declaration} (m : EnvS V env)
    (hE : EtaFamiliesClosed env)
    (h : checkDecl modeR (fueledOps modeR F) env d = .ok env₂) :
    EnvSOk V env₂ :=
  declStepS (hg := rfl) divModPinS reducePinS stdAxiomKeyS declBasisS
    (declIndS memberKeyS) m hE
    (checkDeclR_sound (hg := rfl) m hE h)

/-- A declared `Empty`-typed `def`/`theorem` cannot survive the fold:
the stored constant would carry the annotated type, which annotation
leaves as `Empty`. -/
theorem foldlM_no_Empty_R
    {F : Nat}
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvSOk V env →
      ds.foldlM (checkDecl modeR (fueledOps modeR F)) env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl modeR (fueledOps modeR F) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hdd hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type := by
        have h1 : annotateCore modeR env F 0 (.const emptyName []) =
            .ok type := hann
        cases F with
        | zero =>
          rw [annotateCore_zero] at h1
          simp [throw, throwThe, MonadExceptOf.throw] at h1
        | succ F' =>
          rw [annotateCore_succ] at h1
          simpa [annotateBody, pure, Except.pure] using h1
      obtain ⟨m1⟩ := (checkDecl_sound_R (d := d)
        m hE hdd).1
      exact no_constant_of_Empty_R m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_R (value := value) (hint := hint)
        hty ds env1
        (checkDecl_sound_R (d := d) m hE hdd)
        h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`.** -/
theorem no_proof_of_Empty_input_R (V : Type w) [SetTheory V]
    {F : Nat}
     {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (fueledOps modeR F) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_R hty ds Env.empty
    ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ h hd

/-- The cached executable's input-level fold. -/
theorem foldlM_no_Empty_RC
    {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      EnvSOk V env →
      ds.foldlM (checkDecl modeR (cachedOps modeR)) env = .ok env' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, env, env', hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDecl modeR (cachedOps modeR) env d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok env1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    obtain ⟨F, hF⟩ := checkDecl_bridge m.wf hdd
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type := by
        have h1 : annotateCore modeR env F 0 (.const emptyName []) =
            .ok type := hann
        cases F with
        | zero =>
          rw [annotateCore_zero] at h1
          simp [throw, throwThe, MonadExceptOf.throw] at h1
        | succ F' =>
          rw [annotateCore_succ] at h1
          simpa [annotateBody, pure, Except.pure] using h1
      obtain ⟨m1⟩ := (checkDecl_sound_R (d := d)
        m hE hF).1
      exact no_constant_of_Empty_R m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_RC (value := value) (hint := hint)
        hty ds env1
        (checkDecl_sound_R (d := d) m hE hF) h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`** — cached
executable. -/
theorem no_proof_of_Empty_input_C_R (V : Type w) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDecls modeR (cachedOps modeR) ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False :=
  foldlM_no_Empty_RC hty ds Env.empty
    ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩ h hd

/-- The shared-state executable's input-level fold. -/
theorem foldlM_no_Empty_RS
    {cv : ConstantVal} {value : Expr}
    {hint : ReducibilityHint}
    (hty : cv.type = .const emptyName []) :
    ∀ (ds : List Declaration) (fe : FEnv) {fe' : FEnv},
      fe = mkFEnv fe.env →
      EnvSOk V fe.env →
      ds.foldlM (checkDeclSharedF modeR) fe = .ok fe' →
      (Declaration.defnDecl cv value hint ∈ ds ∨
        Declaration.thmDecl cv value ∈ ds) → False
  | [], _, _, _, _, _, hd => by rcases hd with hd | hd <;> cases hd
  | d :: ds, fe, fe', hfe, hm, h, hd => by
    simp only [List.foldlM, Bind.bind, Except.bind] at h
    cases hdd : checkDeclSharedF modeR fe d with
    | error e => rw [hdd] at h; exact nomatch h
    | ok fe1 =>
    rw [hdd] at h
    obtain ⟨⟨m⟩, hE⟩ := hm
    rw [hfe] at hdd
    obtain ⟨hfe1, F, hF⟩ := checkDeclSharedF_bridge m.wf hdd
    by_cases hdis : d = Declaration.defnDecl cv value hint ∨
        d = Declaration.thmDecl cv value
    · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF hdis
      rw [hty] at hann
      obtain rfl : Expr.const emptyName [] = type := by
        have h1 : annotateCore modeR fe.env F 0 (.const emptyName []) =
            .ok type := hann
        cases F with
        | zero =>
          rw [annotateCore_zero] at h1
          simp [throw, throwThe, MonadExceptOf.throw] at h1
        | succ F' =>
          rw [annotateCore_succ] at h1
          simpa [annotateBody, pure, Except.pure] using h1
      obtain ⟨m1⟩ := (checkDecl_sound_R (d := d)
        m hE hF).1
      exact no_constant_of_Empty_R m1 c hc (by rw [hcv])
    · refine foldlM_no_Empty_RS (value := value) (hint := hint)
        hty ds fe1 hfe1
        (checkDecl_sound_R (d := d) m hE hF) h ?_
      rcases hd with hd | hd
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inl rfl) hdis
        · exact Or.inl hmem
      · rcases List.mem_cons.mp hd with rfl | hmem
        · exact absurd (Or.inr rfl) hdis
        · exact Or.inr hmem

/-- **No accepted stream declares a proof of `Empty`** — shared-state
executable. -/
theorem no_proof_of_Empty_input_S_R (V : Type w) [SetTheory V]
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared modeR ds = .ok env')
    {cv : ConstantVal} {value : Expr} {hint : ReducibilityHint}
    (hd : Declaration.defnDecl cv value hint ∈ ds ∨
      Declaration.thmDecl cv value ∈ ds)
    (hty : cv.type = .const emptyName []) : False := by
  unfold checkDeclsShared at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : ds.foldlM (checkDeclSharedF modeR) (mkFEnv Env.empty) with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    exact foldlM_no_Empty_RS hty ds
      (mkFEnv Env.empty) rfl ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩
      hf hd

/-- **No accepted input stream declares a proof of `Empty`** — the
parsed-index executable, at the *stream* level: the parsed record's
type index denotes `Empty` in the parse store. -/
theorem no_proof_of_Empty_input_SP_R (V : Type w) [SetTheory V]
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP modeR st pds = .ok env')
    {cvp : ConstantValP} {value : EIdx}
    (hd : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
      DeclP.thmDecl cvp value ∈ pds)
    (hty : st.denote cvp.type = some (.const emptyName [])) :
    False := by
  replace hty : st.raw.denote cvp.type
      = some (.const emptyName []) := hty
  unfold checkDeclsSP at h
  have hwf : st.raw.WF := st.wf
  simp only [Bind.bind, Except.bind, StateT.run'] at h
  cases hrun : (pds.foldlM (checkDeclSPStep modeR
      (st.raw.nodes.size + st.raw.nodes.size))
      (mkFEnv Env.empty)) { store := st.raw } with
  | error e => rw [hrun] at h; exact nomatch h
  | ok pr =>
    clear h
    obtain ⟨feO, sO⟩ := pr
    suffices hgen : ∀ (pds : List DeclP) (fe : FEnv) {fe' : FEnv}
        {s₀ s' : IState},
        fe = mkFEnv fe.env →
        EnvSOk V fe.env →
        ISOKF s₀ → Ext st.raw s₀.store →
        (pds.foldlM (checkDeclSPStep modeR
          (st.raw.nodes.size + st.raw.nodes.size)) fe) s₀
          = .ok (fe', s') →
        ((∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
          DeclP.thmDecl cvp value ∈ pds) → False by
      exact hgen pds (mkFEnv Env.empty) rfl
        ⟨⟨EnvS.empty V⟩, EtaFamiliesClosed.empty⟩
        (ISOKF.fresh hwf) (Ext.refl _) hrun hd
    clear hrun hd
    intro pds
    induction pds with
    | nil =>
      intro fe fe' s₀ s' _ _ _ _ _ hd
      rcases hd with ⟨_, hd⟩ | hd <;> cases hd
    | cons pd pds ih =>
      intro fe fe' s₀ s' hfe hm hres hext0 h hd
      rw [List.foldlM_cons] at h
      obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
      obtain ⟨⟨m⟩, hE⟩ := hm
      obtain ⟨d, hd0⟩ := denoteDeclP_total hwf
        (checkDeclSPStep_inRange hstep)
      have hden : denoteDeclP s₀.store pd = some d :=
        denoteDeclP_mono hwf hext0 hd0
      rw [hfe] at hstep
      obtain ⟨hres₁, hext₁, hfe₁, F, hF⟩ :=
        checkDeclSPStep_run m.wf hres hden hstep
      by_cases hdis : (∃ hint, pd = DeclP.defnDecl cvp value hint) ∨
          pd = DeclP.thmDecl cvp value
      · have hdd : ∃ ve, (∃ hint, d = Declaration.defnDecl
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                hint) ∨
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
              ⟨cvp.name, cvp.levelParams, .const emptyName []⟩ ve
                hint)) →
            False := by
          intro hcase
          have hstores : ∃ type, annotateCore modeR fe.env F 0
                (.const emptyName []) = .ok type ∧
              ∃ c, c ∈ fe₁.env.consts ∧ c.toConstantVal =
                ⟨cvp.name, cvp.levelParams, type⟩ := by
            rcases hcase with hdis' | ⟨hint, hdis'⟩
            · obtain ⟨type, hann, c, hc, hcv⟩ :=
                checkDecl_stores hF hdis'
              exact ⟨type, hann, c, hc, hcv⟩
            · obtain ⟨type, hann, c, hc, hcv⟩ := checkDecl_stores hF
                (Or.inl hdis')
              exact ⟨type, hann, c, hc, hcv⟩
          obtain ⟨type, hann, c, hc, hcv⟩ := hstores
          obtain rfl : Expr.const emptyName [] = type := by
            have h1 : annotateCore modeR fe.env F 0 (.const emptyName []) =
                .ok type := hann
            cases F with
            | zero =>
              rw [annotateCore_zero] at h1
              simp [throw, throwThe, MonadExceptOf.throw] at h1
            | succ F' =>
              rw [annotateCore_succ] at h1
              simpa [annotateBody, pure, Except.pure] using h1
          obtain ⟨m1⟩ := (checkDecl_sound_R (d := d)
            m hE hF).1
          exact no_constant_of_Empty_R m1 c hc (by rw [hcv])
        rcases hdd with ⟨hint, rfl⟩ | rfl
        · exact hfin (.inr ⟨hint, rfl⟩)
        · exact hfin (.inl (.inr rfl))
      · have hd' : (∃ hint, DeclP.defnDecl cvp value hint ∈ pds) ∨
            DeclP.thmDecl cvp value ∈ pds := by
          rcases hd with ⟨hint, hdm2⟩ | hdm2
          · rcases List.mem_cons.mp hdm2 with heq | hmem
            · exact absurd (.inl ⟨hint, heq.symm⟩) hdis
            · exact .inl ⟨hint, hmem⟩
          · rcases List.mem_cons.mp hdm2 with heq | hmem
            · exact absurd (.inr heq.symm) hdis
            · exact .inr hmem
        exact ih fe₁ hfe₁
          (checkDecl_sound_R (d := d) m hE hF)
          hres₁ (hext0.trans hext₁) h hd'

end Setlec.SetR
