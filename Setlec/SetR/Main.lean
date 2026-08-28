import Setlec.SetR.Bridge.Sound
import Setlec.Verify.BridgeWFDecl
import Setlec.Verify.BridgeSDecl
import Setlec.Verify.BridgePDecl

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
theorem checkDecls_sound_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    (hdm : DivModPinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env') :
    Nonempty (EnvS V env') :=
  foldlM_R hkey heta hdm hstd hofr
    ds Env.empty ⟨EnvS.empty V⟩ h

/-- **No proof of `Empty` is ever accepted**, on the `SetR` route. -/
theorem no_proof_of_Empty_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} {F : Nat}
    (hdm : DivModPinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (fueledOps μ F) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDecls_sound_R hkey heta hdm
    hstd hofr h
  exact no_constant_of_Empty_R m c hc hty

/-- The cached-executable fold.  `checkDecl_bridge` supplies, per
declaration, a fuel at which the pure checker reproduces the cached
run; everything after that is `foldlM_R`'s step. -/
theorem foldlM_RC (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} (hdm : DivModPinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) :
    ∀ (ds : List Declaration) (env : Env) {env' : Env},
      Nonempty (EnvS V env) →
      ds.foldlM (checkDecl μ (cachedOps μ)) env = .ok env' →
      Nonempty (EnvS V env')
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
      obtain ⟨m⟩ := hm
      obtain ⟨F, hF⟩ := checkDecl_bridge m.wf hd
      exact foldlM_RC hkey heta hdm hstd hofr ds env1
        (declStepS hdm reducePinS hstd hofr declBasisS
          (declIndS hkey heta) m
          (checkDeclR_sound hkey heta m hF)) h

/-- **The acceptance theorem for the cached executable checker.** -/
theorem checkDeclsC_sound_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} (hdm : DivModPinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (cachedOps μ) ds = .ok env') :
    Nonempty (EnvS V env') :=
  foldlM_RC hkey heta hdm hstd hofr ds Env.empty ⟨EnvS.empty V⟩ h

/-- **No proof of `Empty`** is accepted by the cached executable. -/
theorem no_proof_of_Empty_C_R (hkey : MemberKeyS V)
    (heta : MemberEtaS V) {μ : CheckMode} (hdm : DivModPinS V)
    (hstd : StdAxiomKeyS V) (hofr : OfReduceKeyS V)
    {ds : List Declaration} {env' : Env}
    (h : checkDecls μ (cachedOps μ) ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsC_sound_R hkey heta hdm hstd hofr h
  exact no_constant_of_Empty_R m c hc hty

/-- The shared-state executable's fold. -/
theorem foldlM_RS (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} (hdm : DivModPinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) :
    ∀ (ds : List Declaration) (fe : FEnv) {fe' : FEnv},
      fe = mkFEnv fe.env →
      Nonempty (EnvS V fe.env) →
      ds.foldlM (checkDeclSharedF μ) fe = .ok fe' →
      Nonempty (EnvS V fe'.env)
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
      obtain ⟨m⟩ := hm
      rw [hfe] at hd
      obtain ⟨hfe1, F, hF⟩ := checkDeclSharedF_bridge m.wf hd
      exact foldlM_RS hkey heta hdm hstd hofr ds fe1 hfe1
        (declStepS hdm reducePinS hstd hofr declBasisS
          (declIndS hkey heta) m
          (checkDeclR_sound hkey heta m hF)) h

/-- **The acceptance theorem for the shared-state executable.** -/
theorem checkDeclsS_sound_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} (hdm : DivModPinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared μ ds = .ok env') :
    Nonempty (EnvS V env') := by
  unfold checkDeclsShared at h
  simp only [Bind.bind, Except.bind] at h
  cases hf : ds.foldlM (checkDeclSharedF μ) (mkFEnv Env.empty) with
  | error e => rw [hf] at h; exact nomatch h
  | ok fe =>
    rw [hf] at h
    obtain rfl : fe.env = env' := by
      have h' : (Except.ok fe.env : CheckM Env) = .ok env' := h
      exact Except.ok.inj h'
    exact foldlM_RS hkey heta hdm hstd hofr ds (mkFEnv Env.empty) rfl
      ⟨EnvS.empty V⟩ hf

/-- **No proof of `Empty`** is accepted by the shared-state
executable. -/
theorem no_proof_of_Empty_S_R (hkey : MemberKeyS V)
    (heta : MemberEtaS V) {μ : CheckMode} (hdm : DivModPinS V)
    (hstd : StdAxiomKeyS V) (hofr : OfReduceKeyS V)
    {ds : List Declaration} {env' : Env}
    (h : checkDeclsShared μ ds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsS_sound_R hkey heta hdm hstd hofr h
  exact no_constant_of_Empty_R m c hc hty

/-- The parsed-index executable's fold.  The store invariant's
supplier is the bundle: `WFStore.wf` gives `st.raw.WF` once, and the
fold threads `ISOKF`/`Ext` from `checkDeclSPStep_run` — the same
"name the environment each premise is at" discipline, at the store. -/
theorem foldSP_R (hkey : MemberKeyS V) (heta : MemberEtaS V)
    {μ : CheckMode} (hdm : DivModPinS V) (hstd : StdAxiomKeyS V)
    (hofr : OfReduceKeyS V) {st0 : EStore} (hwfst : st0.WF) :
    ∀ (pds : List DeclP) (fe : FEnv) {fe' : FEnv} {s₀ s' : IState},
      fe = mkFEnv fe.env →
      Nonempty (EnvS V fe.env) →
      ISOKF s₀ → Ext st0 s₀.store →
      (pds.foldlM (checkDeclSPStep μ
        (st0.nodes.size + st0.nodes.size)) fe) s₀ = .ok (fe', s') →
      Nonempty (EnvS V fe'.env)
  | [], fe, fe', s₀, s', _, hm, _, _, h => by
    obtain ⟨hfe, rfl⟩ := pureI_ok h
    subst hfe
    exact hm
  | pd :: pds, fe, fe', s₀, s', hfe, hm, hres, hext0, h => by
    rw [List.foldlM_cons] at h
    obtain ⟨fe₁, s₁, hstep, h⟩ := bindI_ok h
    obtain ⟨m⟩ := hm
    obtain ⟨d, hd0⟩ := denoteDeclP_total hwfst
      (checkDeclSPStep_inRange hstep)
    have hd : denoteDeclP s₀.store pd = some d :=
      denoteDeclP_mono hwfst hext0 hd0
    rw [hfe] at hstep
    obtain ⟨hres₁, hext₁, hfe₁, F, hF⟩ :=
      checkDeclSPStep_run m.wf hres hd hstep
    exact foldSP_R hkey heta hdm hstd hofr hwfst pds fe₁ hfe₁
      (declStepS hdm reducePinS hstd hofr declBasisS
        (declIndS hkey heta) m
        (checkDeclR_sound hkey heta m hF)) hres₁
      (hext0.trans hext₁) h

/-- **The acceptance theorem for the parsed-index executable.** -/
theorem checkDeclsSP_sound_R (hkey : MemberKeyS V)
    (heta : MemberEtaS V) {μ : CheckMode} (hdm : DivModPinS V)
    (hstd : StdAxiomKeyS V) (hofr : OfReduceKeyS V)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP μ st pds = .ok env') :
    Nonempty (EnvS V env') := by
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
      exact foldSP_R hkey heta hdm hstd hofr hwf pds
        (mkFEnv Env.empty) rfl ⟨EnvS.empty V⟩ (ISOKF.fresh hwf)
        (Ext.refl _) hrun

/-- **No proof of `Empty`** is accepted by the parsed-index
executable. -/
theorem no_proof_of_Empty_SP_R (hkey : MemberKeyS V)
    (heta : MemberEtaS V) {μ : CheckMode} (hdm : DivModPinS V)
    (hstd : StdAxiomKeyS V) (hofr : OfReduceKeyS V)
    {st : WFStore} {pds : List DeclP} {env' : Env}
    (h : checkDeclsSP μ st pds = .ok env')
    (c : ConstantInfo) (hc : c ∈ env'.consts)
    (hty : c.toConstantVal.type = .const emptyName []) : False := by
  obtain ⟨m⟩ := checkDeclsSP_sound_R hkey heta hdm hstd hofr h
  exact no_constant_of_Empty_R m c hc hty

end Setlec.SetR
