import Setlec.SetR.Bridge.Sound
import Setlec.Verify.BridgeWFDecl

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
open Setlec.TT Setlec.TTVerify SetTheory
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

end Setlec.SetR
